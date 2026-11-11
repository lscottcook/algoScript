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
    /// ADX + candle-direction strategy.
    ///
    /// BUY:  the last two closed 30-second candles AND the last closed 1-minute candle were
    ///       bullish (close > open), and ADX is above 25 on both the 30-second and 1-minute
    ///       charts -> buy LIMIT PullbackTicks below the bid (cancelled if unfilled after
    ///       EntryTimeoutSeconds; the strategy then keeps watching for the next signal).
    /// SELL: same, with all three candles bearish (close < open); sell LIMIT PullbackTicks above the ask.
    ///
    /// Checked each time a 30-second bar closes, while flat. Both ADX values are read from
    /// the last CLOSED bar on their chart. +DI / -DI are not used.
    ///
    /// Every entry carries a server-side hard stop and take-profit (ticks from fill), and the
    /// strategy also closes the position itself when a trade reaches either level.
    /// </summary>
    public class strategyTesting : Strategy, ICurrentAccount, ICurrentSymbol
    {
        [InputParameter("Symbol", 0)]
        public Symbol CurrentSymbol { get; set; }

        [InputParameter("Account", 1)]
        public Account CurrentAccount { get; set; }

        [InputParameter("Hard stop (ticks)", 8, 1, 1000, 1, 0)]
        public int StopTicks = 7;

        [InputParameter("Take profit (ticks)", 9, 1, 1000, 1, 0)]
        public int TargetTicks = 5;

        [InputParameter("Pullback (ticks)", 9, 0, 100, 1, 0)]
        public int PullbackTicks = 1;

        [InputParameter("Entry limit timeout (seconds)", 9, 1, 60, 1, 0)]
        public int EntryTimeoutSeconds = 3;

        [InputParameter("Paper quantity", 14, 1, 10, 1, 0)]
        public int PaperQuantity = 1;

        [InputParameter("Account TakeProfit", 16)]
        public double inputedAccountTakeProfit = 200.0;

        [InputParameter("Account Stoploss", 17)]
        public double inputedAccountStopLoss = -100.0;

        [InputParameter("Starting Balance", 18)]
        public double StartingBalance { get; set; }







        private int FilterMinutes = 1;
        private int SignalSeconds = 30;
        private int AdxPeriod = 14;
        private double AdxThreshold = 25;



        private double accountTakeProfit;
        private double accountStopLoss;
        private double _baselineBalance;
        private bool _accountLimitLogged;
        private bool _accountStopLogged;
        private DateTime _nextFlattenUtc = DateTime.MinValue;
        private bool _outsideHoursLogged;

        private readonly object _sync = new object();

        private string _runId;
        private long _signalSequence;
        private double _tickSize;
        private bool _stopping;
        private bool _rebindInProgress;
        private bool _lastKnownConnected = true;
        private readonly Dictionary<Connection, EventHandler<ConnectionStateChangedEventArgs>>
            _connectionHandlers = new Dictionary<Connection, EventHandler<ConnectionStateChangedEventArgs>>();
        private System.Timers.Timer _connectionWatchdog;
        private System.Timers.Timer _housekeepingTimer;

        // 1-min and 30-sec bars, each with its own ADX.
        private HistoricalData _filterHistory;
        private HistoricalData _signalHistory;
        private Indicator _filterAdx;
        private Indicator _signalAdx;
        // Line indices inside the built-in ADX indicator; resolved by name at load.
        private int _adxLine = 0, _plusDiLine = 1, _minusDiLine = 2;

        // Trade log
        private string _tradeCsv;
        private TradeRecord _openRecord;
        private readonly List<Execution> _executions = new List<Execution>();
        private const int ExitFillTimeoutSeconds = 10;

        // ADX / +DI / -DI on both charts at one moment (last closed bar of each).
        private sealed class DmiSnapshot
        {
            public double Adx30 = double.NaN, Plus30 = double.NaN, Minus30 = double.NaN;
            public double Adx1m = double.NaN, Plus1m = double.NaN, Minus1m = double.NaN;
        }

        private sealed class TradeRecord
        {
            public string SignalId;
            public Side Side;
            public string EntryOrderId;
            public DateTime SubmitTime;
            public DateTime EntryTime;
            public DateTime ExitTime;
            public double PositionOpenPrice = double.NaN; // fallback if no entry execution arrives
            public double EntryQty, EntryNotional, ExitQty, ExitNotional;
            public double Fees = double.NaN;
            public double MfeTicks, MaeTicks;             // MFE >= 0, MAE <= 0, measured from the fill
            public string ExitReason = "";
            public DmiSnapshot AtEntry, AtExit;
            public bool Closed;
            public int Written;
            public System.Timers.Timer Fallback;
            public double EntryFill => EntryQty > 0 ? EntryNotional / EntryQty : PositionOpenPrice;
            public double ExitFill => ExitQty > 0 ? ExitNotional / ExitQty : double.NaN;
            public bool ExitComplete => ExitQty > 0 && ExitQty >= (EntryQty > 0 ? EntryQty : 1) - 1e-9;
        }

        // One execution on our account/symbol, consumed by at most one trade.
        private sealed class Execution
        {
            public string OrderId;
            public Side Side;
            public double Price, Quantity, Fee;
            public DateTime Seen;
            public bool Claimed;
        }

        // Position state
        private Position _paperPosition;
        private bool _paperEntryPending;
        private bool _exitRequested;
        private string _exitReason = "";
        private bool _paperTradingBlockedAfterReconnect;
        private Side _paperPendingSide;
        private string _paperSignalId = "";

        // Pullback limit entry
        private double _bid = double.NaN, _ask = double.NaN;
        private string _entryOrderId;
        private DateTime _entryDeadlineUtc = DateTime.MaxValue;
        private bool _entryCancelRequested;
        private DateTime _entryCancelUtc;
        private DateTime _nextReconcileUtc = DateTime.MinValue;

        public strategyTesting()
        {
            Name = "strategyTesting";
            Description = "ADX + candles: two 30-sec candles and the last 1-min candle in one direction, ADX above threshold on both charts, hard stop + take profit.";
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

            FilterMinutes = Math.Max(1, FilterMinutes);
            SignalSeconds = Math.Max(5, SignalSeconds);
            AdxPeriod = Math.Max(2, AdxPeriod);
            PaperQuantity = Math.Max(1, PaperQuantity);
            StopTicks = Math.Max(1, StopTicks);
            TargetTicks = Math.Max(1, TargetTicks);
            PullbackTicks = Math.Max(0, PullbackTicks);
            EntryTimeoutSeconds = Math.Max(1, EntryTimeoutSeconds);

            _runId = Guid.NewGuid().ToString("N");

            accountTakeProfit = inputedAccountTakeProfit * PaperQuantity;
            accountStopLoss = inputedAccountStopLoss * PaperQuantity;
            _accountLimitLogged = _accountStopLogged = _outsideHoursLogged = false;
            _nextFlattenUtc = DateTime.MinValue;
            // If no Starting Balance is entered, account P&L is measured from the balance at start.
            _baselineBalance = CurrentAccount != null ? CurrentAccount.Balance : 0;

            _tradeCsv = Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.UserProfile),
                "Downloads", "AdexEntry_trades.csv");
            try { EnsureHeader(_tradeCsv, CsvHeader); }
            catch (Exception ex) { Log("Trade CSV setup failed: " + ex.Message, StrategyLoggingLevel.Error); }

            if (!LoadHistory()) return;

            CurrentSymbol.NewLast -= OnNewLast;
            CurrentSymbol.NewLast += OnNewLast;
            CurrentSymbol.NewQuote -= OnNewQuote;
            CurrentSymbol.NewQuote += OnNewQuote;
            Core.Instance.TradeAdded -= OnTradeAdded;
            Core.Instance.TradeAdded += OnTradeAdded;
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

            Log($"ADX + candles started for {CurrentSymbol.Name}: ADX({AdxPeriod}) > {AdxThreshold} on {SignalSeconds}-sec and {FilterMinutes}-min, " +
                $"two {SignalSeconds}-sec + one {FilterMinutes}-min same-direction candles, ADX on both. " +
                $"Pullback limit {PullbackTicks}t, cancel after {EntryTimeoutSeconds}s. Bracket SL={StopTicks}t TP={TargetTicks}t.",
                StrategyLoggingLevel.Info);
            Log($"Trades CSV: {_tradeCsv}", StrategyLoggingLevel.Info);
            Log($"Account TP {accountTakeProfit:F2} (stops new entries), account SL {-Math.Abs(accountStopLoss):F2} " +
                $"(closes everything), measured from balance {(StartingBalance > 0 ? StartingBalance : _baselineBalance):F2}. " +
                $"New entries only inside the ET trading window(s) in IsTradingTimeValid.",
                StrategyLoggingLevel.Info);
        }

        protected override void OnStop()
        {
            _stopping = true;
            if (CurrentSymbol != null) CurrentSymbol.NewLast -= OnNewLast;
            if (CurrentSymbol != null) CurrentSymbol.NewQuote -= OnNewQuote;
            Core.Instance.TradeAdded -= OnTradeAdded;
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

            lock (_sync) UnloadHistory();
            Log("ADX + candles stopped. Existing paper positions and their stop/target orders are left in place.",
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
        // Bars + ADX
        // ------------------------------------------------------------------

        private bool LoadHistory()
        {
            try
            {
                UnloadHistory();
                // Enough history to warm up the indicator even across a weekend.
                _filterHistory = CurrentSymbol.GetHistory(new Period(BasePeriod.Minute, FilterMinutes),
                    HistoryType.Last, DateTime.UtcNow.AddDays(-4));
                _signalHistory = CurrentSymbol.GetHistory(new Period(BasePeriod.Second, SignalSeconds),
                    HistoryType.Last, DateTime.UtcNow.AddDays(-1));

                // SMMA = Wilder's smoothing, the standard ADX smoothing.
                _filterAdx = Core.Indicators.BuiltIn.ADX(AdxPeriod, MaMode.SMMA);
                _signalAdx = Core.Indicators.BuiltIn.ADX(AdxPeriod, MaMode.SMMA);
                _filterHistory.AddIndicator(_filterAdx);
                _signalHistory.AddIndicator(_signalAdx);
                ResolveAdxLine(_filterAdx);
                _signalHistory.NewHistoryItem += OnNewSignalBar;

                if (double.IsNaN(Value(_filterAdx, 1, _adxLine)) || double.IsNaN(Value(_signalAdx, 1, _adxLine)))
                {
                    Log("ADX has no value yet on the last closed bars.", StrategyLoggingLevel.Error);
                    return false;
                }
                Log($"Loaded {_filterHistory.Count} x {FilterMinutes}-min bars: ADX={Value(_filterAdx, 1, _adxLine):F2}. " +
                    $"Loaded {_signalHistory.Count} x {SignalSeconds}-sec bars: ADX={Value(_signalAdx, 1, _adxLine):F2}. " +
                    "Compare ADX with the chart before trusting signals.",
                    StrategyLoggingLevel.Info);
                return true;
            }
            catch (Exception ex)
            {
                Log("History/indicator load failed: " + ex.Message, StrategyLoggingLevel.Error);
                return false;
            }
        }

        // Find the ADX, +DI and -DI lines by name so the code does not depend on line order.
        private void ResolveAdxLine(Indicator indicator)
        {
            var lines = indicator.LinesSeries;
            string names = string.Join(", ", lines.Select((l, i) => $"{i}='{l.Name}'"));
            int adx = -1, plus = -1, minus = -1;
            for (int i = 0; i < lines.Length; i++)
            {
                string n = (lines[i].Name ?? "").Replace(" ", "").ToUpperInvariant();
                if (n.Contains("+DI") || n.Contains("PLUS") || n == "DI+") plus = i;
                else if (n.Contains("-DI") || n.Contains("MINUS") || n == "DI-") minus = i;
                else if (n.Contains("ADX") && adx < 0) adx = i;
            }
            _adxLine = adx >= 0 ? adx : 0;
            _plusDiLine = plus >= 0 ? plus : 1;
            _minusDiLine = minus >= 0 ? minus : 2;
            bool matched = adx >= 0 && plus >= 0 && minus >= 0;
            Log($"ADX lines: {names} -> ADX={_adxLine}, +DI={_plusDiLine}, -DI={_minusDiLine}" +
                (matched ? "." : " (not all matched by name; using default order ADX=0, +DI=1, -DI=2 where missing). Verify against the chart."),
                matched ? StrategyLoggingLevel.Info : StrategyLoggingLevel.Error);
        }

        // Offset of the last CLOSED bar as of asOfUtc. If the forming bar has already ended
        // (the roll-over event hasn't arrived yet), the forming bar is the closed one.
        private static int ClosedOffset(HistoricalData history, TimeSpan period, DateTime asOfUtc)
        {
            return history[0, SeekOriginHistory.End].TimeLeft.Add(period) <= asOfUtc ? 0 : 1;
        }

        private DmiSnapshot TakeSnapshot(DateTime asOfUtc)
        {
            var s = new DmiSnapshot();
            if (_signalHistory != null && _signalAdx != null && _signalHistory.Count > 2)
            {
                int o = ClosedOffset(_signalHistory, TimeSpan.FromSeconds(SignalSeconds), asOfUtc);
                s.Adx30 = Value(_signalAdx, o, _adxLine);
                s.Plus30 = Value(_signalAdx, o, _plusDiLine);
                s.Minus30 = Value(_signalAdx, o, _minusDiLine);
            }
            if (_filterHistory != null && _filterAdx != null && _filterHistory.Count > 2)
            {
                int o = ClosedOffset(_filterHistory, TimeSpan.FromMinutes(FilterMinutes), asOfUtc);
                s.Adx1m = Value(_filterAdx, o, _adxLine);
                s.Plus1m = Value(_filterAdx, o, _plusDiLine);
                s.Minus1m = Value(_filterAdx, o, _minusDiLine);
            }
            return s;
        }

        private void UnloadHistory()
        {
            if (_signalHistory != null)
            {
                _signalHistory.NewHistoryItem -= OnNewSignalBar;
                if (_signalAdx != null) _signalHistory.RemoveIndicator(_signalAdx);
                _signalHistory.Dispose();
                _signalHistory = null;
            }
            if (_filterHistory != null)
            {
                if (_filterAdx != null) _filterHistory.RemoveIndicator(_filterAdx);
                _filterHistory.Dispose();
                _filterHistory = null;
            }
            _filterAdx = null;
            _signalAdx = null;
        }

        // offset 0 = forming bar, 1 = last closed bar, 2 = the bar before that.
        private static double Value(Indicator indicator, int offset, int line)
        {
            return indicator == null ? double.NaN : indicator.GetValue(offset, line);
        }

        // Fires when a new signal bar opens, so offset 1 is the bar that just closed
        // and offset 2 is the one before it.
        private void OnNewSignalBar(object sender, HistoryEventArgs e)
        {
            if (_stopping) return;
            lock (_sync)
            {
                if (_signalHistory == null || _signalHistory.Count < AdxPeriod * 2 + 3) return;
                if (_filterHistory == null || _filterHistory.Count < AdxPeriod * 2 + 2) return;
                DateTime nowUtc = DateTime.UtcNow;

                // Only look for entries while flat.
                if (_paperPosition != null || _paperEntryPending) return;

                // Entry window (ET). Exits and stops are never gated by this.
                if (!IsTradingTimeValid(ToEastern(nowUtc).TimeOfDay))
                {
                    if (!_outsideHoursLogged)
                        Log("Outside trading hours; no new entries until the next window.", StrategyLoggingLevel.Info);
                    _outsideHoursLogged = true;
                    return;
                }
                _outsideHoursLogged = false;

                if (AccountLimitReason().Length > 0) return;

                IHistoryItem bar1 = _signalHistory[1, SeekOriginHistory.End];
                IHistoryItem bar2 = _signalHistory[2, SeekOriginHistory.End];
                int dir1 = CandleDirection(bar1);
                int dir2 = CandleDirection(bar2);
                if (dir1 == 0 || dir1 != dir2) return;

                // Last CLOSED 1-minute bar as of this 30-second close. On a minute boundary the
                // 30-sec event can arrive before the 1-min bar rolls over, so if the forming 1-min
                // bar has already ended by this close time, treat it as the closed one.
                DateTime signalCloseUtc = bar1.TimeLeft.AddSeconds(SignalSeconds);
                int filterOffset = ClosedOffset(_filterHistory, TimeSpan.FromMinutes(FilterMinutes), signalCloseUtc);
                IHistoryItem filterBar = _filterHistory[filterOffset, SeekOriginHistory.End];
                int filterDir = CandleDirection(filterBar);

                Side side = dir1 > 0 ? Side.Buy : Side.Sell;
                string label = side == Side.Buy ? "LONG" : "SHORT";
                string word = side == Side.Buy ? "bullish" : "bearish";

                string candles = $"{SignalSeconds}-sec {bar2.TimeLeft:HH:mm:ss} O{bar2[PriceType.Open]:F2}/C{bar2[PriceType.Close]:F2}, " +
                    $"{bar1.TimeLeft:HH:mm:ss} O{bar1[PriceType.Open]:F2}/C{bar1[PriceType.Close]:F2}; " +
                    $"{FilterMinutes}-min {filterBar.TimeLeft:HH:mm} O{filterBar[PriceType.Open]:F2}/C{filterBar[PriceType.Close]:F2}";

                if (filterDir != dir1)
                {
                    Log($"{label} skipped: two {word} {SignalSeconds}-sec candles but the last {FilterMinutes}-min candle was not {word} ({candles}).",
                        StrategyLoggingLevel.Info);
                    return;
                }

                double signalAdx = Value(_signalAdx, 1, _adxLine);
                double filterAdx = Value(_filterAdx, filterOffset, _adxLine);
                string adxText = $"{SignalSeconds}-sec ADX={signalAdx:F2}, {FilterMinutes}-min ADX={filterAdx:F2}";
                bool adxOk = !double.IsNaN(signalAdx) && !double.IsNaN(filterAdx)
                    && signalAdx > AdxThreshold && filterAdx > AdxThreshold;
                if (!adxOk)
                {
                    Log($"{label} skipped: candles all {word} but ADX not above {AdxThreshold} on both ({adxText}; {candles}).",
                        StrategyLoggingLevel.Info);
                    return;
                }

                Signal(side, $"all {word}: {candles}; {adxText}", signalCloseUtc);
            }
        }

        // +1 bullish (close > open), -1 bearish (close < open), 0 doji or no data.
        private static int CandleDirection(IHistoryItem bar)
        {
            double open = bar[PriceType.Open], close = bar[PriceType.Close];
            if (double.IsNaN(open) || double.IsNaN(close)) return 0;
            return close > open ? 1 : close < open ? -1 : 0;
        }

        private void Signal(Side side, string detail, DateTime signalCloseUtc)
        {
            string signalId = _runId + "-S" + (++_signalSequence).ToString("D6");
            Log($"{side} signal {signalId}: {detail}.", StrategyLoggingLevel.Trading);

            if (!TryPlacePaperOrder(side, signalId, TakeSnapshot(signalCloseUtc)))
                Log($"Signal {signalId} not traded (entry refused).", StrategyLoggingLevel.Info);
        }

        // ------------------------------------------------------------------
        // Stop / target exit: close the position when a trade prints at or
        // through fill -/+ StopTicks or fill +/- TargetTicks. Runs alongside
        // the server-side bracket; whichever acts first closes the position.
        // ------------------------------------------------------------------

        private void OnNewLast(Symbol symbol, Last last)
        {
            if (_stopping || last == null || last.Price <= 0) return;
            lock (_sync)
            {
                if (_paperPosition != null) CheckAccountStop(DateTime.UtcNow);
                if (_paperPosition == null) return;
                double entry = _paperPosition.OpenPrice;
                if (double.IsNaN(entry) || entry <= 0 || _tickSize <= 0) return;

                bool isLong = _paperPosition.Side == Side.Buy;

                // MFE / MAE in ticks from the fill, tracked until the position is gone.
                if (_openRecord != null && !_openRecord.Closed)
                {
                    double moveTicks = (last.Price - entry) * (isLong ? 1.0 : -1.0) / _tickSize;
                    if (moveTicks > _openRecord.MfeTicks) _openRecord.MfeTicks = moveTicks;
                    if (moveTicks < _openRecord.MaeTicks) _openRecord.MaeTicks = moveTicks;
                }

                if (_exitRequested) return;
                double stopPrice = isLong ? entry - StopTicks * _tickSize : entry + StopTicks * _tickSize;
                double targetPrice = isLong ? entry + TargetTicks * _tickSize : entry - TargetTicks * _tickSize;
                // Half-tick tolerance so floating-point noise doesn't miss an exact touch.
                double eps = _tickSize * 0.5;
                bool stopHit = isLong ? last.Price <= stopPrice + eps : last.Price >= stopPrice - eps;
                bool targetHit = isLong ? last.Price >= targetPrice - eps : last.Price <= targetPrice + eps;
                if (!stopHit && !targetHit) return;

                string reason = stopHit ? "stop" : "target";
                _exitRequested = true;
                _exitReason = reason;
                TradingOperationResult result = Core.Instance.ClosePosition(_paperPosition);
                if (result.Status == TradingOperationResultStatus.Success)
                {
                    Log($"PAPER {reason} exit requested: trade {last.Price:F2}, fill {entry:F2}, " +
                        $"stop {stopPrice:F2} ({StopTicks}t), target {targetPrice:F2} ({TargetTicks}t); signal={_paperSignalId}",
                        StrategyLoggingLevel.Trading);
                    CancelWorkingOrders(reason + " exit");
                }
                else
                {
                    _exitRequested = false;
                    _exitReason = "";
                    Log($"PAPER {reason} exit failed: {result.Message}", StrategyLoggingLevel.Error);
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
                CheckAccountStop(nowUtc);
                CheckEntryTimeout(nowUtc);
                ReconcileOrphanedPositions(nowUtc);
            }
        }

        private void OnNewQuote(Symbol symbol, Quote quote)
        {
            if (quote == null || double.IsNaN(quote.Bid) || double.IsNaN(quote.Ask)
                || quote.Bid <= 0 || quote.Ask <= 0) return;
            _bid = quote.Bid;
            _ask = quote.Ask;
        }

        // Pullback limit not filled in time -> cancel it, then go back to looking for signals
        // once the platform confirms the order is no longer working. Caller holds _sync.
        private void CheckEntryTimeout(DateTime nowUtc)
        {
            if (!_paperEntryPending || string.IsNullOrEmpty(_entryOrderId)) return;
            Order order = Core.Instance.Orders.FirstOrDefault(o => o.Id == _entryOrderId);
            bool working = order != null
                && (order.Status == OrderStatus.Opened || order.Status == OrderStatus.PartiallyFilled);

            if (!_entryCancelRequested)
            {
                if (nowUtc < _entryDeadlineUtc) return;
                _entryCancelRequested = true;
                _entryCancelUtc = nowUtc;
                if (working)
                {
                    TradingOperationResult result = Core.Instance.CancelOrder((IOrder)order);
                    Log(result.Status == TradingOperationResultStatus.Success
                            ? $"Pullback LIMIT not filled in {EntryTimeoutSeconds}s; cancel requested (signal={_paperSignalId})."
                            : $"Pullback LIMIT cancel FAILED (signal={_paperSignalId}): {result.Message}",
                        result.Status == TradingOperationResultStatus.Success
                            ? StrategyLoggingLevel.Trading : StrategyLoggingLevel.Error);
                }
                return;
            }

            // Cancel requested: wait until the order is gone. A fill that raced the cancel
            // arrives through OnPositionAdded and clears _paperEntryPending there.
            if (working)
            {
                if ((nowUtc - _entryCancelUtc).TotalSeconds > 10)
                {
                    _entryCancelUtc = nowUtc;
                    Log($"Pullback LIMIT {_entryOrderId} still working 10s after cancel; retrying cancel.",
                        StrategyLoggingLevel.Error);
                    Core.Instance.CancelOrder((IOrder)order);
                }
                return;
            }
            if (Core.Instance.Positions.Any(p => IsOurAccount(p.Account) && IsOurSymbol(p.Symbol))) return;

            Log($"Pullback entry cancelled, no fill; signal={_paperSignalId}. Watching for the next signal.",
                StrategyLoggingLevel.Trading);
            ClearEntryOrder();
            _paperEntryPending = false;
            _paperSignalId = "";
            _openRecord = null;
        }

        private void ClearEntryOrder()
        {
            _entryOrderId = null;
            _entryDeadlineUtc = DateTime.MaxValue;
            _entryCancelRequested = false;
        }

        // ------------------------------------------------------------------
        // Orders and positions
        // ------------------------------------------------------------------

        private bool TryPlacePaperOrder(Side side, string signalId, DmiSnapshot atEntry)
        {
            if (_paperTradingBlockedAfterReconnect)
            {
                Log("Signal not traded: paper execution is blocked after reconnect until strategy restart.",
                    StrategyLoggingLevel.Error);
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

            // Pullback limit, as in DirectEntry: buy below the bid, sell above the ask.
            if (double.IsNaN(_bid) || double.IsNaN(_ask) || _bid <= 0 || _ask <= 0)
            {
                Log("Signal not traded: no bid/ask quote yet to price the pullback limit.", StrategyLoggingLevel.Error);
                return false;
            }
            double limitPrice = CurrentSymbol.RoundPriceToTickSize(side == Side.Buy
                ? _bid - PullbackTicks * _tickSize
                : _ask + PullbackTicks * _tickSize);

            _paperEntryPending = true;
            _paperPendingSide = side;
            _paperSignalId = signalId;
            _openRecord = new TradeRecord
            {
                SignalId = signalId,
                Side = side,
                SubmitTime = DateTime.Now,
                AtEntry = atEntry
            };

            var result = Core.Instance.PlaceOrder(new PlaceOrderRequestParameters
            {
                Symbol = CurrentSymbol,
                Account = CurrentAccount,
                Side = side,
                OrderTypeId = OrderType.Limit,
                Price = limitPrice,
                Quantity = PaperQuantity,
                TimeInForce = TimeInForce.GTC,
                Comment = "ADX_PULLBACK",
                //TakeProfit = SlTpHolder.CreateTP(TargetTicks, PriceMeasurement.Offset),
                //StopLoss = SlTpHolder.CreateSL(StopTicks, PriceMeasurement.Offset)
            });
            if (result.Status != TradingOperationResultStatus.Success)
            {
                _paperEntryPending = false;
                _paperSignalId = "";
                _openRecord = null;
                Log("Paper entry failed: " + result.Message, StrategyLoggingLevel.Error);
                return false;
            }
            _openRecord.EntryOrderId = result.OrderId;
            _entryOrderId = result.OrderId;
            _entryCancelRequested = false;
            _entryDeadlineUtc = DateTime.UtcNow.AddSeconds(EntryTimeoutSeconds);
            // One-shot timer so the cancel lands at the timeout, not up to 0.5s later on housekeeping.
            var cancelTimer = new System.Timers.Timer(EntryTimeoutSeconds * 1000) { AutoReset = false };
            cancelTimer.Elapsed += (s, e) =>
            {
                cancelTimer.Dispose();
                if (_stopping) return;
                lock (_sync) CheckEntryTimeout(DateTime.UtcNow);
            };
            cancelTimer.Start();
            Log($"PAPER pullback LIMIT submitted: {side} {PaperQuantity} @ {limitPrice:F2} " +
                $"({PullbackTicks}t from bid {_bid:F2} / ask {_ask:F2}), cancel in {EntryTimeoutSeconds}s, " +
                $"bracket SL={StopTicks}t TP={TargetTicks}t, signal={signalId}",
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
                    ClearEntryOrder();
                    _exitRequested = false;
                    _exitReason = "";
                    if (_openRecord != null)
                    {
                        _openRecord.EntryTime = DateTime.Now;
                        _openRecord.PositionOpenPrice = position.OpenPrice;
                    }
                    Log($"PAPER position filled: {position.Side} {position.Quantity} @ {position.OpenPrice:F2}; " +
                        $"SL id={position.StopLoss?.Id ?? "none"}, TP id={position.TakeProfit?.Id ?? "none"}; signal={_paperSignalId}",
                        StrategyLoggingLevel.Trading);
                    if (position.StopLoss == null || position.TakeProfit == null)
                        Log("WARNING: the position does not report both a stop and a target order. Check the platform.",
                            StrategyLoggingLevel.Error);
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
                Log($"PAPER position closed: {position.Id}; signal={_paperSignalId}" +
                    (_exitRequested ? $" ({_exitReason} exit)" : " (server bracket or closed elsewhere)"),
                    StrategyLoggingLevel.Trading);
                if (_openRecord != null)
                {
                    TradeRecord record = _openRecord;
                    _openRecord = null;
                    record.Closed = true;
                    record.ExitTime = DateTime.Now;
                    record.AtExit = TakeSnapshot(DateTime.UtcNow);
                    record.ExitReason = _exitRequested ? _exitReason : "";
                    RegisterClosedTrade(record);
                }
                _paperPosition = null;
                _paperSignalId = "";
                _exitRequested = false;
                _exitReason = "";
                // Remove any leftover bracket leg so it cannot open a new position.
                CancelWorkingOrders("position closed");
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
        // Trade log: prices come from the executions, not Position P&L fields
        // (those were unreliable on this connection; see algoTrading). The strategy
        // holds one position at a time, so the entry is the execution of our entry
        // order and the exit is any later unclaimed opposite-side execution.
        // ------------------------------------------------------------------

        private void OnTradeAdded(Trade trade)
        {
            if (_stopping || trade == null) return;
            if (!IsOurAccount(trade.Account) || !IsOurSymbol(trade.Symbol)) return;
            if (trade.Price <= 0 || trade.Quantity <= 0) return;

            TradeRecord completed = null;
            lock (_sync)
            {
                _executions.Add(new Execution
                {
                    OrderId = trade.OrderId,
                    Side = trade.Side,
                    Price = trade.Price,
                    Quantity = trade.Quantity,
                    Fee = PnlNumber(trade, "Fee"),
                    Seen = DateTime.Now
                });
                _executions.RemoveAll(x => x.Claimed && (DateTime.Now - x.Seen).TotalMinutes > 5);
                if (_executions.Count > 200) _executions.RemoveRange(0, _executions.Count - 200);

                if (_openRecord != null) ApplyExecutions(_openRecord);
                foreach (TradeRecord pending in _pendingTrades.ToList())
                {
                    ApplyExecutions(pending);
                    if (pending.ExitComplete)
                    {
                        _pendingTrades.Remove(pending);
                        completed = pending;
                        break;
                    }
                }
            }
            if (completed != null) CompleteTrade(completed);
        }

        private readonly List<TradeRecord> _pendingTrades = new List<TradeRecord>();

        // Caller holds _sync.
        private void ApplyExecutions(TradeRecord record)
        {
            foreach (Execution x in _executions)
            {
                if (x.Claimed || x.Seen < record.SubmitTime) continue;

                bool isEntry = !string.IsNullOrEmpty(record.EntryOrderId)
                    ? x.OrderId == record.EntryOrderId
                    : x.Side == record.Side && record.ExitQty == 0 && !record.Closed && record.EntryQty < PaperQuantity;
                if (isEntry)
                {
                    record.EntryQty += x.Quantity;
                    record.EntryNotional += x.Price * x.Quantity;
                    AddFee(record, x.Fee);
                    x.Claimed = true;
                    continue;
                }

                if (record.EntryQty <= 0 && double.IsNaN(record.PositionOpenPrice)) continue; // not filled yet
                if (record.ExitComplete || x.Side == record.Side) continue;

                record.ExitQty += x.Quantity;
                record.ExitNotional += x.Price * x.Quantity;
                AddFee(record, x.Fee);
                x.Claimed = true;
            }
        }

        private static void AddFee(TradeRecord record, double fee)
        {
            if (double.IsNaN(fee)) return;
            record.Fees = (double.IsNaN(record.Fees) ? 0 : record.Fees) + Math.Abs(fee);
        }

        // Caller holds _sync.
        private void RegisterClosedTrade(TradeRecord record)
        {
            ApplyExecutions(record);
            if (record.ExitComplete)
            {
                // Write outside the strategy lock.
                Task.Run(() => CompleteTrade(record));
                return;
            }
            _pendingTrades.Add(record);
            var timer = new System.Timers.Timer(ExitFillTimeoutSeconds * 1000) { AutoReset = false };
            timer.Elapsed += (s, e) =>
            {
                lock (_sync)
                {
                    if (!_pendingTrades.Remove(record)) return;
                }
                Log($"No closing execution seen for signal {record.SignalId} after {ExitFillTimeoutSeconds}s; " +
                    "recording the trade with exit price and P&L blank.", StrategyLoggingLevel.Error);
                CompleteTrade(record);
            };
            record.Fallback = timer;
            timer.Start();
        }

        private void CompleteTrade(TradeRecord r)
        {
            if (System.Threading.Interlocked.Exchange(ref r.Written, 1) != 0) return;
            r.Fallback?.Stop();
            r.Fallback?.Dispose();
            r.Fallback = null;

            double entry = r.EntryFill, exit = r.ExitFill;
            double qty = r.ExitQty > 0 ? r.ExitQty : (r.EntryQty > 0 ? r.EntryQty : PaperQuantity);
            double dir = r.Side == Side.Buy ? 1.0 : -1.0;
            double pnlTicks = double.NaN, gross = double.NaN, net = double.NaN;
            double tickValue = TickValue(entry);
            if (!double.IsNaN(entry) && !double.IsNaN(exit) && _tickSize > 0)
            {
                pnlTicks = (exit - entry) * dir / _tickSize;
                if (!double.IsNaN(tickValue)) gross = pnlTicks * tickValue * qty;
            }
            if (!double.IsNaN(gross)) net = gross - (double.IsNaN(r.Fees) ? 0 : r.Fees);

            string reason = r.ExitReason;
            if (string.IsNullOrEmpty(reason))
            {
                reason = double.IsNaN(pnlTicks) ? "closed (unknown)"
                    : pnlTicks >= TargetTicks - 0.5 ? "server target"
                    : pnlTicks <= -(StopTicks - 0.5) ? "server stop"
                    : "closed elsewhere";
            }

            string symbolName = CurrentSymbol?.Name ?? "";
            var values = new List<string>
            {
                _runId, r.SignalId, symbolName, r.Side.ToString(), Csv(qty, "F0"),
                CsvTime(r.EntryTime), CsvTime(r.ExitTime), Csv(entry, "F2"), Csv(exit, "F2"), reason,
                TargetTicks.ToString(CultureInfo.InvariantCulture), StopTicks.ToString(CultureInfo.InvariantCulture),
                Csv(r.MaeTicks, "F1"), Csv(r.MfeTicks, "F1"),
                Csv(net, "F2"),
                Csv(r.AtEntry?.Adx30), Csv(r.AtEntry?.Plus30), Csv(r.AtEntry?.Minus30),
                Csv(r.AtEntry?.Adx1m), Csv(r.AtEntry?.Plus1m), Csv(r.AtEntry?.Minus1m),
                Csv(r.AtExit?.Adx30), Csv(r.AtExit?.Plus30), Csv(r.AtExit?.Minus30),
                Csv(r.AtExit?.Adx1m), Csv(r.AtExit?.Plus1m), Csv(r.AtExit?.Minus1m)
            };
            try
            {
                lock (_csvLock) File.AppendAllText(_tradeCsv, string.Join(",", values) + Environment.NewLine);
            }
            catch (Exception ex)
            {
                Log("Trade CSV write failed: " + ex.Message + " | row: " + string.Join(",", values),
                    StrategyLoggingLevel.Error);
            }
            Log($"Trade logged {r.SignalId}: {r.Side} {reason}, entry {entry:F2} exit {exit:F2}, " +
                $"{pnlTicks:F1}t, net {net:F2} (fees {r.Fees:F2}), MAE {r.MaeTicks:F1}t MFE {r.MfeTicks:F1}t.",
                StrategyLoggingLevel.Trading);
        }

        private readonly object _csvLock = new object();

        private const string CsvHeader =
            "runId,signalId,symbol,side,quantity,entryTime,exitTime,entryPrice,exitPrice,exitReason," +
            "takeProfitTicks,stopLossTicks,maeTicks,mfeTicks,netPnL," +
            "entryAdx30s,entryPlusDi30s,entryMinusDi30s,entryAdx1m,entryPlusDi1m,entryMinusDi1m," +
            "exitAdx30s,exitPlusDi30s,exitMinusDi30s,exitAdx1m,exitPlusDi1m,exitMinusDi1m";

        // Dollar value of one tick; platform figure first, tick size x lot size as fallback.
        private double TickValue(double atPrice)
        {
            if (CurrentSymbol == null || _tickSize <= 0 || double.IsNaN(atPrice)) return double.NaN;
            try
            {
                double cost = CurrentSymbol.GetTickCost(atPrice);
                if (cost > 0 && !double.IsInfinity(cost)) return cost;
            }
            catch { }
            double lot = CurrentSymbol.LotSize;
            return lot > 0 ? _tickSize * lot : double.NaN;
        }

        // Broker fee members may be plain numbers or PnL items with a Value; NaN if unavailable.
        private static double PnlNumber(object o, string name)
        {
            try
            {
                object v = o?.GetType().GetProperty(name)?.GetValue(o);
                if (v == null) return double.NaN;
                object inner = v.GetType().GetProperty("Value")?.GetValue(v);
                return Convert.ToDouble(inner ?? v, CultureInfo.InvariantCulture);
            }
            catch { return double.NaN; }
        }

        // Writes the header to a new file; if an existing file has a different header,
        // it is archived alongside with a timestamp so old rows aren't mixed with new columns.
        private static void EnsureHeader(string path, string header)
        {
            Directory.CreateDirectory(Path.GetDirectoryName(path));
            if (File.Exists(path) && new FileInfo(path).Length > 0)
            {
                if (string.Equals(File.ReadLines(path).FirstOrDefault(), header, StringComparison.Ordinal)) return;
                File.Move(path, Path.Combine(Path.GetDirectoryName(path),
                    Path.GetFileNameWithoutExtension(path) + "-" + DateTime.Now.ToString("yyyyMMdd-HHmmss") + ".csv"));
            }
            File.AppendAllText(path, header + Environment.NewLine);
        }

        private static string Csv(double? value, string format = "F2")
        {
            return value == null || double.IsNaN(value.Value) || double.IsInfinity(value.Value)
                ? "" : value.Value.ToString(format, CultureInfo.InvariantCulture);
        }

        private static string CsvTime(DateTime value)
        {
            return value == DateTime.MinValue
                ? "" : value.ToString("yyyy-MM-dd HH:mm:ss.fff", CultureInfo.InvariantCulture);
        }

        // ------------------------------------------------------------------
        // Trading hours
        // ------------------------------------------------------------------

        // Entry window only (Eastern time of day), same format as strategyTesting.
        // Add more rows for more windows; an end of 0:00 means "until midnight".
        private bool IsTradingTimeValid(TimeSpan t)
        {
            var windows = new (int sh, int sm, int eh, int em)[]
            {
                ( 9,  30, 10,  0),
                //( 10,  0, 16,  0),

            };

            foreach (var (sh, sm, eh, em) in windows)
            {
                var start = TimeSpan.FromMinutes(sh * 60 + sm);
                var end = TimeSpan.FromMinutes(eh * 60 + em);
                bool inWindow = end == TimeSpan.Zero ? t >= start
                              : start < end ? t >= start && t < end
                                            : t >= start || t < end;
                if (inWindow) return true;
            }
            return false;
        }

        // ------------------------------------------------------------------
        // Account take profit / stop loss
        // ------------------------------------------------------------------

        // Account P&L since the baseline balance: realized balance change plus open P&L.
        private double AccountPnl()
        {
            if (CurrentAccount == null) return double.NaN;
            double baseline = StartingBalance > 0 ? StartingBalance : _baselineBalance;
            return CurrentAccount.Balance - baseline + OpenPnl();
        }

        private double OpenPnl()
        {
            double total = 0;
            foreach (Position p in Core.Instance.Positions.Where(p => IsOurAccount(p.Account) && IsOurSymbol(p.Symbol)))
            {
                double pnl = PnlNumber(p, "NetPnL");
                if (!double.IsNaN(pnl)) total += pnl;
            }
            return total;
        }

        // Returns "" when new entries are allowed, else the reason they are blocked.
        private string AccountLimitReason()
        {
            double pnl = AccountPnl();
            if (double.IsNaN(pnl)) return "";
            if (accountTakeProfit > 0 && pnl >= accountTakeProfit)
            {
                if (!_accountLimitLogged)
                    Log($"Account take profit reached (P&L {pnl:F2} >= {accountTakeProfit:F2}); no new entries.",
                        StrategyLoggingLevel.Trading);
                _accountLimitLogged = true;
                return "account_take_profit_hit";
            }
            if (accountStopLoss != 0 && pnl <= -Math.Abs(accountStopLoss))
            {
                if (!_accountLimitLogged)
                    Log($"Account stop loss reached (P&L {pnl:F2} <= {-Math.Abs(accountStopLoss):F2}); no new entries.",
                        StrategyLoggingLevel.Trading);
                _accountLimitLogged = true;
                return "account_stop_loss_hit";
            }
            _accountLimitLogged = false;
            return "";
        }

        // Account P&L at or below the account stop -> close every position and cancel working
        // orders. Re-checked every tick and by the housekeeping timer until flat. Caller holds _sync.
        private void CheckAccountStop(DateTime nowUtc)
        {
            if (accountStopLoss == 0) return;
            double pnl = AccountPnl();
            if (double.IsNaN(pnl) || pnl > -Math.Abs(accountStopLoss))
            {
                _accountStopLogged = false;
                return;
            }
            if (!_accountStopLogged)
                Log($"Account stop loss reached (P&L {pnl:F2} <= {-Math.Abs(accountStopLoss):F2}); closing all positions.",
                    StrategyLoggingLevel.Trading);
            _accountStopLogged = true;
            FlattenAll(nowUtc, "account stop loss");
        }

        private void FlattenAll(DateTime nowUtc, string label)
        {
            if (nowUtc < _nextFlattenUtc || CurrentAccount == null || CurrentSymbol == null) return;
            List<Position> positions = Core.Instance.Positions
                .Where(p => IsOurAccount(p.Account) && IsOurSymbol(p.Symbol)).ToList();
            bool working = Core.Instance.Orders.Any(o => IsOurAccount(o.Account) && IsOurSymbol(o.Symbol)
                && (o.Status == OrderStatus.Opened || o.Status == OrderStatus.PartiallyFilled));
            if (positions.Count == 0 && !working) return;

            _nextFlattenUtc = nowUtc.AddSeconds(5); // do not stack close orders while one is in flight
            if (working) CancelWorkingOrders(label);

            foreach (Position p in positions)
            {
                bool tracked = _paperPosition != null && p.Id == _paperPosition.Id;
                TradingOperationResult result = Core.Instance.ClosePosition(p);
                if (result.Status == TradingOperationResultStatus.Success)
                {
                    Log($"{label} close requested: position {p.Id} {p.Side} {p.Quantity}.", StrategyLoggingLevel.Trading);
                    if (tracked)
                    {
                        if (!_exitRequested) _exitReason = label;
                        _exitRequested = true;
                    }
                }
                else
                    Log($"{label} close FAILED for position {p.Id}: {result.Message}. Retrying in 5s.",
                        StrategyLoggingLevel.Error);
            }
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
                    CurrentSymbol.NewQuote -= OnNewQuote;
                    CurrentSymbol = Core.GetSymbol(symbolInfo);
                    if (CurrentSymbol == null)
                        throw new InvalidOperationException("Could not reacquire the selected symbol.");
                    _tickSize = CurrentSymbol.TickSize;
                    CurrentSymbol.NewLast += OnNewLast;
                    CurrentSymbol.NewQuote += OnNewQuote;

                    if (!string.IsNullOrEmpty(accountId))
                    {
                        Account account = Core.Instance.Accounts.FirstOrDefault(a => a.Id == accountId);
                        if (account != null) CurrentAccount = account;
                        else Log("Reconnect warning: selected account was not reacquired.", StrategyLoggingLevel.Error);
                    }

                    Core.Instance.TradeAdded -= OnTradeAdded;
                    Core.Instance.TradeAdded += OnTradeAdded;
                    Core.Instance.PositionAdded -= OnPositionAdded;
                    Core.Instance.PositionRemoved -= OnPositionRemoved;
                    Core.Instance.PositionAdded += OnPositionAdded;
                    Core.Instance.PositionRemoved += OnPositionRemoved;

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
                if (_paperEntryPending || _paperPosition != null)
                {
                    _paperTradingBlockedAfterReconnect = true;
                    Log("Paper entries blocked after connection loss. Restart the strategy after reconciling the account and orders.",
                        StrategyLoggingLevel.Error);
                }
            }
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
