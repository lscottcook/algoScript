using System;
using System.Collections.Generic;
using System.Diagnostics.Metrics;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using TradingPlatform.BusinessLayer;

namespace strategyTesting
{
    /// <summary>
    /// Keltner re-entry strategy (3-minute bars).
    ///
    /// LONG:  a 3-minute bar CLOSES below the lower band (setup armed), then a later
    ///        3-minute bar CLOSES back above the lower band -> buy at market.
    ///        Exit when any trade prints at or above the middle band.
    /// SHORT: mirror image — close above the upper band arms; a later close back
    ///        below the upper band sells; exit when a trade prints at or below the middle band.
    ///
    /// No stop loss or take-profit order is attached (by request). Positions are still
    /// closed at the 4:00 PM ET session-close exit when ExcludeClosedPeriod is on.
    ///
    /// Shadow logging is the default. Paper orders require two explicit inputs:
    /// EnablePaperOrders=true and PaperConfirmation="PAPER ONLY".
    /// </summary>
    public class strategyTesting : Strategy, ICurrentAccount, ICurrentSymbol
    {
        [InputParameter("Symbol", 0)]
        public Symbol CurrentSymbol { get; set; }

        [InputParameter("Account", 1)]
        public Account CurrentAccount { get; set; }

        [InputParameter("Bar period (minutes)", 2, 1, 60, 1, 0)]
        public int BarMinutes = 3;

        [InputParameter("Keltner EMA period (middle band)", 3, 2, 200, 1, 0)]
        public int KeltnerPeriod = 20;

        [InputParameter("Keltner ATR multiplier", 4, 0.1, 10, 0.1, 1)]
        public double KeltnerOffset = 1.0;

        [InputParameter("Keltner ATR period", 7, 1, 200, 1, 0)]
        public int AtrPeriod = 10;

        [InputParameter("Enable longs", 5)]
        public bool EnableLongs = true;

        [InputParameter("Enable shorts", 6)]
        public bool EnableShorts = true;

        [InputParameter("Exclude 4:00-6:00 PM ET", 10)]
        public bool ExcludeClosedPeriod = true;

        [InputParameter("Enable PAPER orders", 12)]
        public bool EnablePaperOrders = true;

        [InputParameter("Paper confirmation text", 13)]
        public string PaperConfirmation = "PAPER ONLY";

        [InputParameter("Paper quantity", 14, 1, 10, 1, 0)]
        public int PaperQuantity = 1;

        [InputParameter("Starting Balance", 14)]
        public double StartingBalance { get; set; }

        private readonly object _sync = new object();
        private readonly object _csvSync = new object();
        private readonly object _flushIoLock = new object();
        private readonly List<string> _tradeBuffer = new List<string>();

        private string _runId;
        private long _signalSequence;
        private double _tickSize;
        private bool _stopping;
        private bool _closedState;
        private bool _rebindInProgress;
        private bool _lastKnownConnected = true;
        private readonly Dictionary<Connection, EventHandler<ConnectionStateChangedEventArgs>>
            _connectionHandlers = new Dictionary<Connection, EventHandler<ConnectionStateChangedEventArgs>>();
        private System.Timers.Timer _connectionWatchdog;
        private System.Timers.Timer _housekeepingTimer;
        private System.Timers.Timer _flushTimer;

        // 3-minute bars + Keltner built from EMA (middle) and ATR (width):
        // upper = EMA + mult*ATR, lower = EMA - mult*ATR.
        private HistoricalData _history;
        private Indicator _ema;
        private Indicator _atr;
        private const int _upperLine = 0, _middleLine = 1, _lowerLine = 2;

        // Setup state
        private bool _longArmed;
        private bool _shortArmed;
        private DateTime _armedBarUtc = DateTime.MinValue;

        // Position state
        private string _tradeCsv;
        private Position _paperPosition;
        private bool _paperEntryPending;
        private bool _exitRequested;
        private bool _paperTradingBlockedAfterReconnect;
        private Side _paperPendingSide;
        private string _paperSignalId = "";
        private DateTime _nextReconcileUtc = DateTime.MinValue;
        private TradeRecord _openRecord;

        private sealed class TradeRecord
        {
            public string SignalId;
            public Side Side;
            public DateTime SetupBarUtc;
            public DateTime SignalBarUtc;
            public double SignalClose;
            public double Upper, Middle, Lower;
            public DateTime SubmitUtc;
            public DateTime FillUtc;
            public double FillPrice = double.NaN;
        }

        public strategyTesting()
        {
            Name = "strategyTesting";
            Description = "Keltner re-entry: close outside a band, re-enter on close back inside, exit at the middle band.";
        }

        protected override void OnRun()
        {
            _stopping = false;
            _paperTradingBlockedAfterReconnect = false;
            if (CurrentSymbol == null)
            {
                Log("Symbol must be selected.", StrategyLoggingLevel.Error);
                return;
            }

            CurrentSymbol = Core.GetSymbol(CurrentSymbol.CreateInfo());
            _tickSize = CurrentSymbol.TickSize;
            if (_tickSize <= 0)
            {
                Log("The selected symbol has an invalid tick size.", StrategyLoggingLevel.Error);
                return;
            }

            BarMinutes = Math.Max(1, BarMinutes);
            KeltnerPeriod = Math.Max(2, KeltnerPeriod);
            PaperQuantity = Math.Max(1, PaperQuantity);

            _runId = Guid.NewGuid().ToString("N");
            string downloads = Path.Combine(
                Environment.GetFolderPath(Environment.SpecialFolder.UserProfile), "Downloads");
            _tradeCsv = Path.Combine(downloads, "strategyTesting_keltner_trades.csv");
            EnsureHeader(_tradeCsv,
                "runId,signalId,side,setupBarUtc,signalBarUtc,signalClose,upper,middle,lower," +
                "submitUtc,fillUtc,fillPrice,exitUtc,exitReason,exitTriggerPrice,middleAtExit,signedPoints");

            if (!LoadHistory()) return;

            CurrentSymbol.NewLast -= OnNewLast;
            CurrentSymbol.NewLast += OnNewLast;
            Core.Instance.PositionAdded += OnPositionAdded;
            Core.Instance.PositionRemoved += OnPositionRemoved;

            Core.Instance.Connections.ConnectionAdded += OnConnectionAdded;
            Core.Instance.Connections.ConnectionRemoved += OnConnectionRemoved;
            foreach (Connection connection in Core.Instance.Connections.All)
                SubscribeToConnection(connection);
            _lastKnownConnected = Core.Instance.Connections.All.Any(
                c => c.State == ConnectionState.Connected);
            _connectionWatchdog = new System.Timers.Timer(15000) { AutoReset = true };
            _connectionWatchdog.Elapsed += (s, e) => CheckConnectionHealth();
            _connectionWatchdog.Start();

            _housekeepingTimer = new System.Timers.Timer(500) { AutoReset = true };
            _housekeepingTimer.Elapsed += (s, e) => OnHousekeepingTimer();
            _housekeepingTimer.Start();

            _flushTimer = new System.Timers.Timer(5000) { AutoReset = true };
            _flushTimer.Elapsed += (s, e) => Flush();
            _flushTimer.Start();

            Log($"Keltner re-entry started for {CurrentSymbol.Name}: {BarMinutes}-min bars, KC(EMA {KeltnerPeriod}, ATR {AtrPeriod} x {KeltnerOffset}). " +
                $"Longs={EnableLongs}, Shorts={EnableShorts}. Mode={(EnablePaperOrders ? "PAPER REQUESTED" : "SHADOW")}. No stop loss.",
                StrategyLoggingLevel.Info);
            Log($"Trades: {_tradeCsv}", StrategyLoggingLevel.Info);
        }

        protected override void OnStop()
        {
            _stopping = true;
            if (CurrentSymbol != null) CurrentSymbol.NewLast -= OnNewLast;
            Core.Instance.PositionAdded -= OnPositionAdded;
            Core.Instance.PositionRemoved -= OnPositionRemoved;

            foreach (var item in _connectionHandlers.ToList())
                item.Key.StateChanged -= item.Value;
            _connectionHandlers.Clear();
            Core.Instance.Connections.ConnectionAdded -= OnConnectionAdded;
            Core.Instance.Connections.ConnectionRemoved -= OnConnectionRemoved;
            _connectionWatchdog?.Stop();
            _connectionWatchdog?.Dispose();
            _connectionWatchdog = null;
            _housekeepingTimer?.Stop();
            _housekeepingTimer?.Dispose();
            _flushTimer?.Stop();
            _flushTimer?.Dispose();

            lock (_sync) UnloadHistory();
            Flush();
            Log("Keltner re-entry stopped. Existing paper positions are not automatically closed by stopping the strategy.",
                StrategyLoggingLevel.Info);
        }

        protected override void OnRemove()
        {
            CurrentSymbol = null;
            CurrentAccount = null;
        }

        protected override void OnInitializeMetrics(Meter meter)
        {
            base.OnInitializeMetrics(meter);
            meter.CreateObservableCounter("balance",
                () => CurrentAccount.Balance - StartingBalance,
                description: "Balance");
        }

        // ------------------------------------------------------------------
        // Bars + Keltner
        // ------------------------------------------------------------------

        private bool LoadHistory()
        {
            try
            {
                UnloadHistory();
                // Enough history to warm up the indicator even across a weekend.
                _history = CurrentSymbol.GetHistory(new Period(BasePeriod.Minute, BarMinutes),
                    HistoryType.Last, DateTime.UtcNow.AddDays(-4));
                _ema = Core.Indicators.BuiltIn.EMA(KeltnerPeriod, PriceType.Close);
                // SMMA = Wilder's smoothing (TradingView's RMA), the standard ATR smoothing.
                _atr = Core.Indicators.BuiltIn.ATR(AtrPeriod, MaMode.SMMA);
                _history.AddIndicator(_ema);
                _history.AddIndicator(_atr);
                _history.NewHistoryItem += OnNewHistoryItem;

                if (double.IsNaN(Band(1, _middleLine)) || double.IsNaN(Band(1, _upperLine)))
                {
                    Log("EMA/ATR have no value yet on the last closed bar.", StrategyLoggingLevel.Error);
                    return false;
                }
                Log($"Loaded {_history.Count} bars. Last closed bar: upper={Band(1, _upperLine):F2}, " +
                    $"middle={Band(1, _middleLine):F2}, lower={Band(1, _lowerLine):F2}. " +
                    "Compare these with the chart before trusting signals.", StrategyLoggingLevel.Info);
                return true;
            }
            catch (Exception ex)
            {
                Log("History/indicator load failed: " + ex.Message, StrategyLoggingLevel.Error);
                return false;
            }
        }

        private void UnloadHistory()
        {
            if (_history == null) return;
            _history.NewHistoryItem -= OnNewHistoryItem;
            if (_ema != null) _history.RemoveIndicator(_ema);
            if (_atr != null) _history.RemoveIndicator(_atr);
            _history.Dispose();
            _history = null;
            _ema = null;
            _atr = null;
        }

        // offset 0 = forming bar, 1 = last closed bar.
        private double Band(int offset, int line)
        {
            if (_ema == null || _atr == null) return double.NaN;
            double mid = _ema.GetValue(offset);
            if (line == _middleLine) return mid;
            double width = KeltnerOffset * _atr.GetValue(offset);
            return line == _upperLine ? mid + width : mid - width;
        }

        // Fires when a new bar opens, so offset 1 is the bar that just closed.
        private void OnNewHistoryItem(object sender, HistoryEventArgs e)
        {
            if (_stopping) return;
            lock (_sync)
            {
                if (_history == null || _history.Count < KeltnerPeriod + 2) return;
                DateTime nowUtc = DateTime.UtcNow;
                HandleClosedPeriod(nowUtc);
                if (IsClosedEt(nowUtc)) return;

                IHistoryItem closedBar = _history[1, SeekOriginHistory.End];
                double close = closedBar[PriceType.Close];
                DateTime barUtc = closedBar.TimeLeft;
                double upper = Band(1, _upperLine);
                double middle = Band(1, _middleLine);
                double lower = Band(1, _lowerLine);
                if (double.IsNaN(close) || double.IsNaN(upper) || double.IsNaN(middle) || double.IsNaN(lower)) return;

                // Only look for setups while flat.
                if (_paperPosition != null || _paperEntryPending)
                {
                    _longArmed = _shortArmed = false;
                    return;
                }

                if (close < lower)
                {
                    if (EnableLongs && !_longArmed)
                        Log($"LONG setup armed: bar {barUtc:HH:mm} closed {close:F2} below lower band {lower:F2}.",
                            StrategyLoggingLevel.Info);
                    if (EnableLongs && !_longArmed) _armedBarUtc = barUtc;
                    _longArmed = EnableLongs;
                    _shortArmed = false;
                    return;
                }
                if (close > upper)
                {
                    if (EnableShorts && !_shortArmed)
                        Log($"SHORT setup armed: bar {barUtc:HH:mm} closed {close:F2} above upper band {upper:F2}.",
                            StrategyLoggingLevel.Info);
                    if (EnableShorts && !_shortArmed) _armedBarUtc = barUtc;
                    _shortArmed = EnableShorts;
                    _longArmed = false;
                    return;
                }

                // Close is back inside the bands.
                if (_longArmed)
                {
                    _longArmed = false;
                    if (close >= middle)
                        Log($"LONG skipped: re-entry bar closed {close:F2} at/above middle {middle:F2} (no room to target).",
                            StrategyLoggingLevel.Info);
                    else
                        Signal(Side.Buy, barUtc, close, upper, middle, lower);
                }
                else if (_shortArmed)
                {
                    _shortArmed = false;
                    if (close <= middle)
                        Log($"SHORT skipped: re-entry bar closed {close:F2} at/below middle {middle:F2} (no room to target).",
                            StrategyLoggingLevel.Info);
                    else
                        Signal(Side.Sell, barUtc, close, upper, middle, lower);
                }
            }
        }

        private void Signal(Side side, DateTime barUtc, double close, double upper, double middle, double lower)
        {
            var record = new TradeRecord
            {
                SignalId = _runId + "-S" + (++_signalSequence).ToString("D6"),
                Side = side,
                SetupBarUtc = _armedBarUtc,
                SignalBarUtc = barUtc,
                SignalClose = close,
                Upper = upper,
                Middle = middle,
                Lower = lower,
                SubmitUtc = DateTime.UtcNow
            };
            Log($"{side} signal {record.SignalId}: bar {barUtc:HH:mm} closed {close:F2} back inside " +
                $"(U {upper:F2} / M {middle:F2} / L {lower:F2}).", StrategyLoggingLevel.Trading);

            if (!TryPlacePaperOrder(record))
            {
                // Shadow mode (or entry refused): log the signal with no fill.
                WriteTradeRow(record, DateTime.MinValue, "NO_ORDER", double.NaN, double.NaN);
            }
        }

        // ------------------------------------------------------------------
        // Exit: first trade at/through the middle band of the forming bar
        // ------------------------------------------------------------------

        private void OnNewLast(Symbol symbol, Last last)
        {
            if (_stopping || last == null || last.Price <= 0) return;
            lock (_sync)
            {
                if (_paperPosition == null || _exitRequested || _ema == null) return;
                double middle = Band(0, _middleLine);
                if (double.IsNaN(middle)) return;

                bool hit = _paperPosition.Side == Side.Buy ? last.Price >= middle : last.Price <= middle;
                if (!hit) return;

                _exitRequested = true;
                TradingOperationResult result = Core.Instance.ClosePosition(_paperPosition);
                if (result.Status == TradingOperationResultStatus.Success)
                {
                    Log($"PAPER exit requested at middle band: trade {last.Price:F2}, middle {middle:F2}; signal={_paperSignalId}",
                        StrategyLoggingLevel.Trading);
                    if (_openRecord != null)
                        WriteTradeRow(_openRecord, DateTime.UtcNow, "MIDDLE_BAND", last.Price, middle);
                }
                else
                {
                    _exitRequested = false;
                    Log("PAPER middle-band exit failed: " + result.Message, StrategyLoggingLevel.Error);
                }
            }
        }

        private void OnHousekeepingTimer()
        {
            if (_stopping) return;
            DateTime nowUtc = DateTime.UtcNow;
            lock (_sync)
            {
                if (_stopping) return;
                HandleClosedPeriod(nowUtc);
                ReconcileOrphanedPositions(nowUtc);
            }
        }

        // ------------------------------------------------------------------
        // Orders and positions
        // ------------------------------------------------------------------

        private bool TryPlacePaperOrder(TradeRecord record)
        {
            if (!EnablePaperOrders) return false;
            if (_paperTradingBlockedAfterReconnect)
            {
                Log("Signal not traded: paper execution is blocked after reconnect until strategy restart.",
                    StrategyLoggingLevel.Error);
                return false;
            }
            if (!string.Equals(PaperConfirmation?.Trim(), "PAPER ONLY", StringComparison.Ordinal))
            {
                Log("Signal not traded: Paper confirmation must equal PAPER ONLY.", StrategyLoggingLevel.Error);
                return false;
            }
            if (CurrentAccount == null)
            {
                Log("Signal not traded: no account selected.", StrategyLoggingLevel.Error);
                return false;
            }
            if (_paperEntryPending || _paperPosition != null) return false;
            if (Core.Instance.Positions.Any(p => IsOurAccount(p.Account) && IsOurSymbol(p.Symbol))) return false;
            if (Core.Instance.Orders.Any(o => IsOurAccount(o.Account) && IsOurSymbol(o.Symbol)
                && (o.Status == OrderStatus.Opened || o.Status == OrderStatus.PartiallyFilled))) return false;

            _paperEntryPending = true;
            _paperPendingSide = record.Side;
            _paperSignalId = record.SignalId;
            _openRecord = record;

            var result = Core.Instance.PlaceOrder(new PlaceOrderRequestParameters
            {
                Symbol = CurrentSymbol,
                Account = CurrentAccount,
                Side = record.Side,
                OrderTypeId = OrderType.Market,
                Quantity = PaperQuantity,
                TimeInForce = TimeInForce.GTC,
                Comment = "KC_REENTRY"
            });
            if (result.Status != TradingOperationResultStatus.Success)
            {
                _paperEntryPending = false;
                _paperSignalId = "";
                _openRecord = null;
                Log("Paper entry failed: " + result.Message, StrategyLoggingLevel.Error);
                return false;
            }
            Log($"PAPER entry submitted: {record.Side} {PaperQuantity}, signal={record.SignalId} (no stop loss)",
                StrategyLoggingLevel.Trading);
            return true;
        }

        private void OnPositionAdded(Position position)
        {
            lock (_sync)
            {
                if (!IsOurAccount(position.Account) || !IsOurSymbol(position.Symbol)) return;

                if (_paperEntryPending && position.Side == _paperPendingSide)
                {
                    _paperPosition = position;
                    _paperEntryPending = false;
                    _exitRequested = false;
                    if (_openRecord != null)
                    {
                        _openRecord.FillUtc = DateTime.UtcNow;
                        _openRecord.FillPrice = position.OpenPrice;
                    }
                    Log($"PAPER position filled: {position.Side} {position.Quantity} @ {position.OpenPrice:F2}; signal={_paperSignalId}",
                        StrategyLoggingLevel.Trading);
                    return;
                }

                string reason = _paperEntryPending
                    ? $"a pending {_paperPendingSide} entry did not match the arriving {position.Side} position"
                    : "no entry was pending when this position appeared";
                CloseUnexpectedPosition(position, reason);
            }
        }

        private void OnPositionRemoved(Position position)
        {
            lock (_sync)
            {
                if (_paperPosition == null || position.Id != _paperPosition.Id) return;
                Log($"PAPER position closed: {position.Id}; signal={_paperSignalId}", StrategyLoggingLevel.Trading);
                // Closed by something other than the middle-band exit (manual close, session close, platform).
                if (!_exitRequested && _openRecord != null)
                    WriteTradeRow(_openRecord, DateTime.UtcNow, "CLOSED_ELSEWHERE", double.NaN, Band(0, _middleLine));
                _paperPosition = null;
                _paperSignalId = "";
                _openRecord = null;
                _exitRequested = false;
            }
        }

        // A position here did not come from this strategy's own entry flow, so it
        // is not ours to manage. Close it rather than adopt it.
        private void CloseUnexpectedPosition(Position position, string reason)
        {
            if (_paperPosition != null)
            {
                if (_paperPosition.Id == position.Id) return;
                Log($"PAPER position anomaly: already tracking id={_paperPosition.Id} but an unrelated " +
                    $"position id={position.Id}, side={position.Side}, qty={position.Quantity} appeared for " +
                    $"our account/symbol ({reason}). Not touching it; check the platform.", StrategyLoggingLevel.Error);
                return;
            }
            Log($"PAPER position found outside the normal entry flow: id={position.Id}, side={position.Side}, " +
                $"qty={position.Quantity} @ {position.OpenPrice:F2} ({reason}). Closing it rather than adopting it.",
                StrategyLoggingLevel.Error);
            TradingOperationResult result = Core.Instance.ClosePosition(position);
            if (result.Status == TradingOperationResultStatus.Success)
            {
                Log($"Unexpected PAPER position close requested: id={position.Id}.", StrategyLoggingLevel.Trading);
                if (!_paperEntryPending) CancelWorkingOrders("unexpected position closed");
            }
            else
                Log($"Unexpected PAPER position close FAILED: id={position.Id}: {result.Message}. " +
                    "Manual intervention required.", StrategyLoggingLevel.Error);
        }

        private void CancelWorkingOrders(string reason)
        {
            List<Order> working = Core.Instance.Orders.Where(o => IsOurAccount(o.Account) && IsOurSymbol(o.Symbol)
                && (o.Status == OrderStatus.Opened || o.Status == OrderStatus.PartiallyFilled)).ToList();
            foreach (Order order in working)
            {
                TradingOperationResult result = Core.Instance.CancelOrder((IOrder)order);
                if (result.Status == TradingOperationResultStatus.Success)
                    Log($"Working order cancelled ({reason}): id={order.Id}.", StrategyLoggingLevel.Trading);
                else
                    Log($"Failed to cancel working order ({reason}): id={order.Id}: {result.Message}.",
                        StrategyLoggingLevel.Error);
            }
        }

        private void ReconcileOrphanedPositions(DateTime nowUtc)
        {
            if (nowUtc < _nextReconcileUtc) return;
            _nextReconcileUtc = nowUtc.AddSeconds(2);
            if (_paperPosition != null || _paperEntryPending || CurrentAccount == null || CurrentSymbol == null) return;

            Position orphan = Core.Instance.Positions.FirstOrDefault(
                p => IsOurAccount(p.Account) && IsOurSymbol(p.Symbol));
            if (orphan == null) return;
            CloseUnexpectedPosition(orphan, "found during periodic reconciliation with no local tracking");
        }

        private bool IsOurAccount(Account account)
        {
            return account != null && CurrentAccount != null
                && (ReferenceEquals(account, CurrentAccount) || account.Id == CurrentAccount.Id);
        }

        private bool IsOurSymbol(Symbol symbol)
        {
            if (symbol == null || CurrentSymbol == null) return false;
            if (ReferenceEquals(symbol, CurrentSymbol) || symbol.Id == CurrentSymbol.Id) return true;
            return !string.IsNullOrEmpty(symbol.Root) && !string.IsNullOrEmpty(CurrentSymbol.Root)
                && string.Equals(symbol.Root, CurrentSymbol.Root, StringComparison.OrdinalIgnoreCase);
        }

        // ------------------------------------------------------------------
        // Session handling
        // ------------------------------------------------------------------

        private void HandleClosedPeriod(DateTime nowUtc)
        {
            bool closed = IsClosedEt(nowUtc);
            if (closed && !_closedState)
            {
                _longArmed = _shortArmed = false;
                _closedState = true;
                if (_paperPosition != null && !_exitRequested)
                {
                    _exitRequested = true;
                    TradingOperationResult closeResult = Core.Instance.ClosePosition(_paperPosition);
                    if (closeResult.Status == TradingOperationResultStatus.Success)
                    {
                        Log("PAPER session-close exit requested for signal " + _paperSignalId,
                            StrategyLoggingLevel.Trading);
                        if (_openRecord != null)
                            WriteTradeRow(_openRecord, nowUtc, "SESSION_CLOSE", double.NaN, Band(0, _middleLine));
                        CancelWorkingOrders("session close");
                    }
                    else
                    {
                        _exitRequested = false;
                        Log("PAPER session-close exit failed: " + closeResult.Message, StrategyLoggingLevel.Error);
                    }
                }
            }
            else if (!closed && _closedState)
            {
                _closedState = false;
            }
        }

        private bool IsClosedEt(DateTime utc)
        {
            if (!ExcludeClosedPeriod) return false;
            DateTime et = ToEastern(utc);
            return et.Hour >= 16 && et.Hour < 18;
        }

        // ------------------------------------------------------------------
        // Connection handling
        // ------------------------------------------------------------------

        private void SubscribeToConnection(Connection connection)
        {
            if (connection == null || _connectionHandlers.ContainsKey(connection)) return;
            EventHandler<ConnectionStateChangedEventArgs> handler =
                (sender, args) => OnConnectionStateChanged(connection, args);
            connection.StateChanged += handler;
            _connectionHandlers[connection] = handler;
        }

        private void OnConnectionAdded(Connection connection)
        {
            if (_stopping) return;
            SubscribeToConnection(connection);
            Log("Connection added: " + connection.Name, StrategyLoggingLevel.Info);
        }

        private void OnConnectionRemoved(Connection connection)
        {
            if (connection != null && _connectionHandlers.TryGetValue(connection, out var handler))
            {
                connection.StateChanged -= handler;
                _connectionHandlers.Remove(connection);
            }
        }

        private void OnConnectionStateChanged(Connection connection, ConnectionStateChangedEventArgs args)
        {
            if (_stopping) return;
            if (args.NewState == ConnectionState.Disconnected)
            {
                Log("Disconnected: " + connection.Name, StrategyLoggingLevel.Error);
                ResetAfterDataGap();
            }
            else if (args.NewState == ConnectionState.Connected)
            {
                Log("Reconnected: " + connection.Name, StrategyLoggingLevel.Info);
                RebindAfterReconnect();
                Task.Run(async () =>
                {
                    await Task.Delay(5000);
                    if (!_stopping) RebindAfterReconnect();
                });
            }
        }

        private void CheckConnectionHealth()
        {
            if (_stopping) return;
            bool connected = Core.Instance.Connections.All.Any(c => c.State == ConnectionState.Connected);
            if (!connected && _lastKnownConnected)
            {
                _lastKnownConnected = false;
                Log("Connection watchdog: no connected data connection.", StrategyLoggingLevel.Error);
                ResetAfterDataGap();
            }
            else if (connected && !_lastKnownConnected)
            {
                _lastKnownConnected = true;
                Log("Connection watchdog: connection restored.", StrategyLoggingLevel.Info);
                RebindAfterReconnect();
            }
        }

        private void RebindAfterReconnect()
        {
            lock (_sync)
            {
                if (_stopping || _rebindInProgress || CurrentSymbol == null) return;
                _rebindInProgress = true;
                try
                {
                    string accountId = CurrentAccount?.Id;
                    var symbolInfo = CurrentSymbol.CreateInfo();
                    CurrentSymbol.NewLast -= OnNewLast;
                    CurrentSymbol = Core.GetSymbol(symbolInfo);
                    if (CurrentSymbol == null)
                        throw new InvalidOperationException("Could not reacquire the selected symbol.");
                    _tickSize = CurrentSymbol.TickSize;
                    CurrentSymbol.NewLast += OnNewLast;

                    if (!string.IsNullOrEmpty(accountId))
                    {
                        Account account = Core.Instance.Accounts.FirstOrDefault(a => a.Id == accountId);
                        if (account != null) CurrentAccount = account;
                        else Log("Reconnect warning: selected account was not reacquired.", StrategyLoggingLevel.Error);
                    }

                    Core.Instance.PositionAdded -= OnPositionAdded;
                    Core.Instance.PositionRemoved -= OnPositionRemoved;
                    Core.Instance.PositionAdded += OnPositionAdded;
                    Core.Instance.PositionRemoved += OnPositionRemoved;

                    _longArmed = _shortArmed = false;
                    if (!LoadHistory())
                        Log("Reconnect: bars/indicator reload failed; no new signals until restart.",
                            StrategyLoggingLevel.Error);
                    else
                        Log($"Reattached {CurrentSymbol.Name} and reloaded bars.", StrategyLoggingLevel.Info);
                }
                catch (Exception ex)
                {
                    Log("Reconnect rebind failed: " + ex.Message, StrategyLoggingLevel.Error);
                }
                finally
                {
                    _rebindInProgress = false;
                }
            }
        }

        private void ResetAfterDataGap()
        {
            lock (_sync)
            {
                if (EnablePaperOrders && (_paperEntryPending || _paperPosition != null))
                {
                    _paperTradingBlockedAfterReconnect = true;
                    Log("Paper entries blocked after connection loss. Restart the strategy after reconciling the account and orders.",
                        StrategyLoggingLevel.Error);
                }
                _longArmed = _shortArmed = false;
            }
        }

        // ------------------------------------------------------------------
        // CSV
        // ------------------------------------------------------------------

        private void WriteTradeRow(TradeRecord r, DateTime exitUtc, string exitReason,
            double exitTriggerPrice, double middleAtExit)
        {
            double signed = double.IsNaN(r.FillPrice) || double.IsNaN(exitTriggerPrice)
                ? double.NaN
                : (exitTriggerPrice - r.FillPrice) * (r.Side == Side.Buy ? 1.0 : -1.0);
            var values = new List<string>
            {
                _runId, r.SignalId, r.Side.ToString(), CsvTime(r.SetupBarUtc), CsvTime(r.SignalBarUtc),
                Csv(r.SignalClose), Csv(r.Upper), Csv(r.Middle), Csv(r.Lower),
                CsvTime(r.SubmitUtc), CsvTime(r.FillUtc), Csv(r.FillPrice),
                CsvTime(exitUtc), exitReason, Csv(exitTriggerPrice), Csv(middleAtExit), Csv(signed, "F2")
            };
            lock (_csvSync) _tradeBuffer.Add(string.Join(",", values));
        }

        private static void EnsureHeader(string path, string header)
        {
            Directory.CreateDirectory(Path.GetDirectoryName(path));
            if (!File.Exists(path) || new FileInfo(path).Length == 0)
            {
                File.AppendAllText(path, header + Environment.NewLine);
                return;
            }
            string existing = File.ReadLines(path).FirstOrDefault();
            if (string.Equals(existing, header, StringComparison.Ordinal)) return;
            string archive = Path.Combine(Path.GetDirectoryName(path),
                Path.GetFileNameWithoutExtension(path) + "-" +
                DateTime.Now.ToString("yyyyMMdd-HHmmssfff") + ".csv");
            File.Move(path, archive);
            File.AppendAllText(path, header + Environment.NewLine);
        }

        private void Flush()
        {
            lock (_flushIoLock)
            {
                List<string> rows;
                lock (_csvSync) rows = new List<string>(_tradeBuffer);
                if (rows.Count == 0) return;
                try
                {
                    File.AppendAllLines(_tradeCsv, rows);
                }
                catch (Exception ex)
                {
                    Log("CSV flush failed; rows retained: " + ex.Message, StrategyLoggingLevel.Error);
                    return;
                }
                lock (_csvSync) _tradeBuffer.RemoveRange(0, Math.Min(rows.Count, _tradeBuffer.Count));
            }
        }

        private static string Csv(double value, string format = "F2")
        {
            return double.IsNaN(value) || double.IsInfinity(value)
                ? "" : value.ToString(format, CultureInfo.InvariantCulture);
        }

        private static string CsvTime(DateTime value)
        {
            return value == DateTime.MinValue
                ? "" : value.ToString("yyyy-MM-dd HH:mm:ss.fff", CultureInfo.InvariantCulture);
        }

        private static readonly TimeZoneInfo Eastern =
            TimeZoneInfo.FindSystemTimeZoneById("Eastern Standard Time");

        private static DateTime ToEastern(DateTime utc)
        {
            DateTime normalized = utc.Kind == DateTimeKind.Utc ? utc : utc.ToUniversalTime();
            return TimeZoneInfo.ConvertTimeFromUtc(normalized, Eastern);
        }
    }
}
