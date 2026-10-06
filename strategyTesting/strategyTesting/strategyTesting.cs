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
    /// Keltner re-entry strategy (30-second bars).
    ///
    /// Bands: middle = EMA(close, KeltnerPeriod); width = EMA(true range, AtrPeriod);
    /// upper/lower = middle +/- multiplier * width. Computed in code from closed bars.
    ///
    /// LONG:  a bar CLOSES below the lower band (setup armed), then a later bar CLOSES
    ///        strictly above the lower band -> buy at market, only if ask &lt; frozen target.
    ///        Exit when the bid reaches the frozen target (last trade if no bid/ask).
    /// SHORT: mirror image — close above the upper band arms; a later close strictly
    ///        below the upper band sells, only if bid &gt; frozen target; exit when the ask
    ///        reaches the frozen target (last trade if no bid/ask).
    /// The target is the middle band of the signal bar, frozen at signal time.
    ///
    /// No stop loss or take-profit order is attached (by request). Positions are still
    /// closed at 4:00 PM ET when "Close all positions at 4:00 PM ET" is on.
    /// New entries are allowed only 18:00 -> 15:30 ET (IsTradingTimeValid); exits are never time-gated.
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

        [InputParameter("Bar period (seconds)", 2, 5, 600, 1, 0)]
        public int BarSeconds = 30;


        [InputParameter("Enable longs", 5)]
        public bool EnableLongs = true;

        [InputParameter("Enable shorts", 6)]
        public bool EnableShorts = true;

        [InputParameter("Close all positions at 4:00 PM ET", 11)]
        public bool FlattenAtClose = true;

        [InputParameter("Progress check after (minutes, 0=off)", 20, 0, 1440, 1, 0)]
        public int ProgressCheckMinutes = 45;

        [InputParameter("Progress recheck every (seconds)", 21, 1, 3600, 1, 0)]
        public int ProgressCheckSeconds = 30;

        [InputParameter("Minimum current progress to target (%)", 22, 0, 100, 1, 0)]
        public double MinProgressPct = 25;

        [InputParameter("Enable PAPER orders", 12)]
        public bool EnablePaperOrders = true;

        [InputParameter("Paper confirmation text", 13)]
        public string PaperConfirmation = "PAPER ONLY";

        [InputParameter("Paper quantity", 14, 1, 10, 1, 0)]
        public int PaperQuantity = 1;


        [InputParameter("Stoploss", 14)]
        public int stopLoss = 150;

        [InputParameter("Account TakeProfit", 15)]
        public double inputedAccountTakeProfit = 800.0;

        [InputParameter("Account Stoploss)", 16)]
        public double inputedAccountStopLoss = -400.0;


        [InputParameter("Starting Balance", 25)]
        public double StartingBalance { get; set; }


        private int KeltnerPeriod = 20; 
        private double KeltnerOffset = 1.0;



        [InputParameter("True-range EMA period (width)", 7, 1, 200, 1, 0)]
        public int AtrPeriod = 20;

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

        // 30-second bars + Keltner computed incrementally from closed bars:
        // middle = EMA(close), width = EMA(true range); upper/lower = middle +/- mult*width.
        private HistoricalData _history;
        private double _midEma, _widthEma, _prevClose;
        private int _barsSeen;
        private DateTime _lastBarUtc = DateTime.MinValue;

        // Latest quote seen (receive time is local; the feed gives no quote timestamp we rely on).
        private double _lastBid = double.NaN, _lastAsk = double.NaN, _lastTradePrice;

        private double accountTakeProfit;
        private double accountStopLoss;
        private DateTime _nextProgressCheckUtc = DateTime.MinValue;
        private DateTime _nextFlattenUtc = DateTime.MinValue;
        private DateTime _exitRequestedUtc = DateTime.MinValue;
        private double _baselineBalance;
        private bool _accountLimitLogged;
        private DateTime _lastQuoteUtc = DateTime.MinValue;

        private string _barCsv;
        private readonly List<string> _barBuffer = new List<string>();

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
            // Timings (UTC): bar callback received, calculation done, order acknowledged.
            public DateTime CallbackUtc, CalcDoneUtc, AckUtc;
            public string RejectReason = "";
            // Exit details. The row is written after the position closes so real fills are included.
            public string PositionId = "";
            public DateTime ExitUtc = DateTime.MinValue, ExitFillUtc = DateTime.MinValue, ClosedUtc = DateTime.MinValue;
            public string ExitReason = "";
            public double ExitTrigger = double.NaN, TargetAtExit = double.NaN, PeakProgress = double.NaN;
            public double MfePoints = double.NaN, MaePoints = double.NaN;
            public double ExitFillQty, ExitFillNotional, NetPnl = double.NaN, Fee = double.NaN;
        }

        private readonly List<TradeRecord> _pendingRecords = new List<TradeRecord>();
        private double _peakProgress;
        private double _mfePoints, _maePoints; // max favorable / adverse excursion (points, both >= 0)
        private bool _tradePropsLogged;

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

            BarSeconds = Math.Max(5, BarSeconds);
            KeltnerPeriod = Math.Max(2, KeltnerPeriod);
            AtrPeriod = Math.Max(1, AtrPeriod);
            PaperQuantity = Math.Max(1, PaperQuantity);

            _runId = Guid.NewGuid().ToString("N");
            string downloads = Path.Combine(
                Environment.GetFolderPath(Environment.SpecialFolder.UserProfile), "Downloads");
            _tradeCsv = Path.Combine(downloads, "strategyTesting_keltner_trades.csv");
            EnsureHeader(_tradeCsv,
                "runId,signalId,side,setupBarUtc,signalBarUtc,signalClose,upper,frozenTarget,lower," +
                "submitUtc,fillUtc,fillPrice,exitUtc,exitReason,exitTriggerPrice,exitFillPrice,exitFillUtc,exitFillQty," +
                "targetAtExit,peakProgress,mfeTicks,maeTicks,signedTicksTrigger,signedTicksFill,netPnl,fee," +
                "barCallbackUtc,calcDoneUtc,ackUtc,calcMs,submitLagMs,ackMs,fillMs,rejectReason");
            _barCsv = Path.Combine(downloads, "strategyTesting_keltner_bars.csv");
            EnsureHeader(_barCsv,
                "runId,barUtc,open,high,low,close,upper,middle,lower,trueRange,widthEma,barsSeen," +
                "setupState,result,rejectReason,heightTicks,bodyTicks,closeUpperTicks,closeLowerTicks," +
                "bid,ask,spreadTicks,quoteAgeMs,callbackUtc,calcDoneUtc,decisionUtc,calcMs,callbackLagMs");

            _lastBid = _lastAsk = double.NaN;
            _lastQuoteUtc = DateTime.MinValue;
            _accountLimitLogged = false;
            // If no Starting Balance is entered, account P&L is measured from the balance at start.
            _baselineBalance = CurrentAccount != null ? CurrentAccount.Balance : 0;
            _longArmed = _shortArmed = false;
            if (!LoadHistory()) return;

            CurrentSymbol.NewLast -= OnNewLast;
            CurrentSymbol.NewLast += OnNewLast;
            CurrentSymbol.NewQuote -= OnNewQuote;
            CurrentSymbol.NewQuote += OnNewQuote;
            Core.Instance.PositionAdded += OnPositionAdded;
            Core.Instance.PositionRemoved += OnPositionRemoved;
            Core.Instance.TradeAdded -= OnTradeAdded;
            Core.Instance.TradeAdded += OnTradeAdded;

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

            Log($"Keltner re-entry started for {CurrentSymbol.Name}: {BarSeconds}-sec bars, KC(EMA {KeltnerPeriod}, TR-EMA {AtrPeriod} x {KeltnerOffset}). " +
                $"Longs={EnableLongs}, Shorts={EnableShorts}. Mode={(EnablePaperOrders ? "PAPER REQUESTED" : "SHADOW")}. Stop loss {stopLoss} x qty {PaperQuantity} = {stopLoss * PaperQuantity} ticks.",
                StrategyLoggingLevel.Info);
            Log($"Trades: {_tradeCsv}", StrategyLoggingLevel.Info);


            stopLoss = stopLoss * PaperQuantity;
            accountTakeProfit = inputedAccountTakeProfit * PaperQuantity;
            accountStopLoss = inputedAccountStopLoss * PaperQuantity;
        }

        protected override void OnStop()
        {
            _stopping = true;
            if (CurrentSymbol != null)
            {
                CurrentSymbol.NewLast -= OnNewLast;
                CurrentSymbol.NewQuote -= OnNewQuote;
            }
            Core.Instance.PositionAdded -= OnPositionAdded;
            Core.Instance.PositionRemoved -= OnPositionRemoved;
            Core.Instance.TradeAdded -= OnTradeAdded;

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

            lock (_sync)
            {
                UnloadHistory();
                FinalizePending(DateTime.UtcNow, true);
            }
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
                _midEma = _widthEma = _prevClose = 0;
                _barsSeen = 0;
                _lastBarUtc = DateTime.MinValue;
                // Enough history to warm up the EMAs even across a weekend.
                _history = CurrentSymbol.GetHistory(new Period(BasePeriod.Second, BarSeconds),
                    HistoryType.Last, DateTime.UtcNow.AddDays(-3));
                _history.NewHistoryItem += OnNewHistoryItem;

                // Seed the EMAs oldest -> newest over every closed bar (offset 0 is the forming bar).
                BarCalc last = null;
                for (int offset = _history.Count - 1; offset >= 1; offset--)
                {
                    BarCalc b = AdvanceBar(_history[offset, SeekOriginHistory.End]);
                    if (b != null) last = b;
                }
                if (last == null || _barsSeen < KeltnerPeriod + 2)
                {
                    Log($"Only {_barsSeen} closed bars available; need at least {KeltnerPeriod + 2}.", StrategyLoggingLevel.Error);
                    return false;
                }
                Log($"Loaded {_barsSeen} closed {BarSeconds}s bars. Last closed bar: upper={last.Upper:F2}, " +
                    $"middle={last.Middle:F2}, lower={last.Lower:F2}. " +
                    "Compare these with the chart before trusting signals.", StrategyLoggingLevel.Info);
                return true;
            }
            catch (Exception ex)
            {
                Log("History load failed: " + ex.Message, StrategyLoggingLevel.Error);
                return false;
            }
        }

        private void UnloadHistory()
        {
            if (_history == null) return;
            _history.NewHistoryItem -= OnNewHistoryItem;
            _history.Dispose();
            _history = null;
        }

        private sealed class BarCalc
        {
            public DateTime Utc;
            public double Open, High, Low, Close, Tr, Upper, Middle, Lower;
        }

        // Feeds one closed bar into the EMAs. Returns null if the bar is stale or has bad data.
        // Width is an EMA of true range (first bar: high-low), middle is an EMA of close.
        private BarCalc AdvanceBar(IHistoryItem bar)
        {
            DateTime t = bar.TimeLeft;
            if (t <= _lastBarUtc) return null;
            double o = bar[PriceType.Open], h = bar[PriceType.High], l = bar[PriceType.Low], c = bar[PriceType.Close];
            if (double.IsNaN(o) || double.IsNaN(h) || double.IsNaN(l) || double.IsNaN(c)) return null;

            double tr = _barsSeen == 0
                ? h - l
                : Math.Max(h - l, Math.Max(Math.Abs(h - _prevClose), Math.Abs(l - _prevClose)));
            if (_barsSeen == 0) { _midEma = c; _widthEma = tr; }
            else
            {
                _midEma += 2.0 / (KeltnerPeriod + 1) * (c - _midEma);
                _widthEma += 2.0 / (AtrPeriod + 1) * (tr - _widthEma);
            }
            _barsSeen++;
            _prevClose = c;
            _lastBarUtc = t;
            return new BarCalc
            {
                Utc = t, Open = o, High = h, Low = l, Close = c, Tr = tr,
                Middle = _midEma,
                Upper = _midEma + KeltnerOffset * _widthEma,
                Lower = _midEma - KeltnerOffset * _widthEma
            };
        }

        // Fires when a new bar opens, so offset 1 is the bar that just closed.
        private void OnNewHistoryItem(object sender, HistoryEventArgs e)
        {
            DateTime callbackUtc = DateTime.UtcNow;
            if (_stopping) return;
            lock (_sync)
            {
                if (_history == null) return;
                HandleClosedPeriod(callbackUtc);
                // Normally exactly one new closed bar; catch up if a callback was missed.
                for (int offset = Math.Min(_history.Count - 1, 50); offset >= 1; offset--)
                {
                    BarCalc b = AdvanceBar(_history[offset, SeekOriginHistory.End]);
                    if (b != null) EvaluateBar(b, callbackUtc, DateTime.UtcNow);
                }
            }
        }

        private void EvaluateBar(BarCalc b, DateTime callbackUtc, DateTime calcDoneUtc)
        {
            string result = "NONE";
            string reject = "";
            DateTime decisionUtc = DateTime.MinValue;

            if (!IsTradingTimeValid(ToEastern(callbackUtc).TimeOfDay))
            {
                result = "SKIP"; reject = "outside_trading_hours";
                _longArmed = _shortArmed = false;
            }
            else if (_barsSeen < KeltnerPeriod + 2)
            {
                result = "SKIP"; reject = "warmup";
            }
            else if (_paperPosition != null || _paperEntryPending)
            {
                // Only look for setups while flat.
                result = "SKIP"; reject = "position_open";
                _longArmed = _shortArmed = false;
            }
            else if (b.Close < b.Lower)
            {
                if (EnableLongs && !_longArmed)
                {
                    _armedBarUtc = b.Utc;
                    Log($"LONG setup armed: bar {b.Utc:HH:mm:ss} closed {b.Close:F2} below lower band {b.Lower:F2}.",
                        StrategyLoggingLevel.Info);
                }
                _longArmed = EnableLongs;
                _shortArmed = false;
                result = EnableLongs ? "ARMED_LONG" : "SETUP_IGNORED";
                if (!EnableLongs) reject = "longs_disabled";
            }
            else if (b.Close > b.Upper)
            {
                if (EnableShorts && !_shortArmed)
                {
                    _armedBarUtc = b.Utc;
                    Log($"SHORT setup armed: bar {b.Utc:HH:mm:ss} closed {b.Close:F2} above upper band {b.Upper:F2}.",
                        StrategyLoggingLevel.Info);
                }
                _shortArmed = EnableShorts;
                _longArmed = false;
                result = EnableShorts ? "ARMED_SHORT" : "SETUP_IGNORED";
                if (!EnableShorts) reject = "shorts_disabled";
            }
            // Re-entry needs a close STRICTLY back across the band; a close exactly on it stays armed.
            else if (_longArmed && b.Close > b.Lower)
            {
                _longArmed = false;
                reject = Signal(Side.Buy, b, callbackUtc, calcDoneUtc, out decisionUtc);
                result = reject.Length == 0 ? "ENTRY_SENT" : "ENTRY_REJECTED";
            }
            else if (_shortArmed && b.Close < b.Upper)
            {
                _shortArmed = false;
                reject = Signal(Side.Sell, b, callbackUtc, calcDoneUtc, out decisionUtc);
                result = reject.Length == 0 ? "ENTRY_SENT" : "ENTRY_REJECTED";
            }
            else if (_longArmed || _shortArmed)
            {
                result = "HOLD_ARMED";
            }

            WriteBarRow(b, result, reject, callbackUtc, calcDoneUtc, decisionUtc);
        }

        private bool GetQuote(out double bid, out double ask)
        {
            bid = _lastBid;
            ask = _lastAsk;
            if (!(bid > 0) || !(ask > 0))
            {
                bid = CurrentSymbol != null ? CurrentSymbol.Bid : double.NaN;
                ask = CurrentSymbol != null ? CurrentSymbol.Ask : double.NaN;
            }
            return bid > 0 && ask > 0 && !double.IsNaN(bid) && !double.IsNaN(ask);
        }

        // Returns "" when an entry order was submitted, otherwise the rejection reason.
        private string Signal(Side side, BarCalc b, DateTime callbackUtc, DateTime calcDoneUtc, out DateTime decisionUtc)
        {
            decisionUtc = DateTime.UtcNow;
            var record = new TradeRecord
            {
                SignalId = _runId + "-S" + (++_signalSequence).ToString("D6"),
                Side = side,
                SetupBarUtc = _armedBarUtc,
                SignalBarUtc = b.Utc,
                SignalClose = b.Close,
                Upper = b.Upper,
                Middle = b.Middle, // frozen target for this trade
                Lower = b.Lower,
                SubmitUtc = decisionUtc,
                CallbackUtc = callbackUtc,
                CalcDoneUtc = calcDoneUtc
            };
            Log($"{side} signal {record.SignalId}: bar {b.Utc:HH:mm:ss} closed {b.Close:F2} back inside " +
                $"(U {b.Upper:F2} / frozen target M {b.Middle:F2} / L {b.Lower:F2}).", StrategyLoggingLevel.Trading);

            // Entry gate: buy only if ask is still below the target; sell only if bid is still above it.
            double bid = double.NaN, ask = double.NaN;
            string reject = "";
            string limitReason = AccountLimitReason();
            if (limitReason.Length > 0) reject = limitReason;
            else if (!GetQuote(out bid, out ask)) reject = "no_quote";
            else if (side == Side.Buy && !(ask < b.Middle)) reject = "ask_not_below_target";
            else if (side == Side.Sell && !(bid > b.Middle)) reject = "bid_not_above_target";

            if (reject.Length == 0 && !TryPlacePaperOrder(record))
                reject = record.RejectReason.Length > 0 ? record.RejectReason : "entry_refused";

            if (reject.Length > 0)
            {
                record.RejectReason = reject;
                Log($"{side} entry rejected ({reject}): bid {bid:F2}, ask {ask:F2}, target {b.Middle:F2}.",
                    StrategyLoggingLevel.Info);
                // Shadow mode (or entry refused): log the signal with no fill.
                record.ExitReason = "NO_ORDER";
                WriteTradeRow(record);
            }
            return reject;
        }

        // ------------------------------------------------------------------
        // Exit: bid reaches the frozen target (longs) / ask reaches it (shorts);
        // last trade is used only when no bid/ask is available.
        // ------------------------------------------------------------------

        private void OnNewLast(Symbol symbol, Last last)
        {
            if (_stopping || last == null || last.Price <= 0) return;
            lock (_sync)
            {
                _lastTradePrice = last.Price;
                CheckExit();
            }
        }

        private void OnNewQuote(Symbol symbol, Quote quote)
        {
            if (_stopping || quote == null) return;
            lock (_sync)
            {
                if (quote.Bid > 0) _lastBid = quote.Bid;
                if (quote.Ask > 0) _lastAsk = quote.Ask;
                _lastQuoteUtc = DateTime.UtcNow;
                CheckExit();
            }
        }

        // Account P&L since the baseline balance (realized). Used only to block NEW entries;
        // open positions are still managed by the target, stop loss and session close.
        private double AccountPnl()
        {
            if (CurrentAccount == null) return double.NaN;
            double baseline = StartingBalance > 0 ? StartingBalance : _baselineBalance;
            return CurrentAccount.Balance - baseline;
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
                        StrategyLoggingLevel.Info);
                _accountLimitLogged = true;
                return "account_take_profit_hit";
            }
            if (accountStopLoss != 0 && pnl <= -Math.Abs(accountStopLoss))
            {
                if (!_accountLimitLogged)
                    Log($"Account stop loss reached (P&L {pnl:F2} <= {-Math.Abs(accountStopLoss):F2}); no new entries.",
                        StrategyLoggingLevel.Info);
                _accountLimitLogged = true;
                return "account_stop_loss_hit";
            }
            _accountLimitLogged = false;
            return "";
        }

        // Progress stop: after ProgressCheckMinutes in the trade, then every ProgressCheckSeconds,
        // close if current progress toward the frozen target is below MinProgressPct.
        private void CheckProgressStop(DateTime nowUtc)
        {
            if (ProgressCheckMinutes <= 0 || _paperPosition == null || _exitRequested || _openRecord == null ||
                _openRecord.FillUtc == DateTime.MinValue) return;
            if ((nowUtc - _openRecord.FillUtc).TotalMinutes < ProgressCheckMinutes) return;
            if (nowUtc < _nextProgressCheckUtc) return;
            _nextProgressCheckUtc = nowUtc.AddSeconds(Math.Max(1, ProgressCheckSeconds));

            bool isLong = _paperPosition.Side == Side.Buy;
            double bid, ask;
            double exitPx = GetQuote(out bid, out ask) ? (isLong ? bid : ask)
                : (_lastTradePrice > 0 ? _lastTradePrice : double.NaN);
            if (double.IsNaN(exitPx)) return; // no price to judge; try again next interval

            // Current progress = how far the exit-side price is from entry toward the frozen target.
            double entry = double.IsNaN(_openRecord.FillPrice) ? _paperPosition.OpenPrice : _openRecord.FillPrice;
            double distance = Math.Abs(_openRecord.Middle - entry);
            double progress = distance > 0 ? (isLong ? exitPx - entry : entry - exitPx) / distance : 1.0;
            if (progress >= MinProgressPct / 100.0) return;

            _exitRequested = true;
            _exitRequestedUtc = nowUtc;
            TradingOperationResult result = Core.Instance.ClosePosition(_paperPosition);
            if (result.Status == TradingOperationResultStatus.Success)
            {
                Log($"PAPER progress-stop exit: progress {progress:P0} < {MinProgressPct:F0}% after " +
                    $"{(nowUtc - _openRecord.FillUtc).TotalMinutes:F1} min; signal={_paperSignalId}", StrategyLoggingLevel.Trading);
                MarkExit(_openRecord, nowUtc, "PROGRESS_STOP", exitPx, _openRecord.Middle);
            }
            else
            {
                _exitRequested = false;
                Log("PAPER progress-stop exit failed: " + result.Message, StrategyLoggingLevel.Error);
            }
        }

        private void CheckExit()
        {
            if (_paperPosition == null || _exitRequested || _openRecord == null) return;
            double target = _openRecord.Middle;
            bool isLong = _paperPosition.Side == Side.Buy;

            double bid, ask, trigger;
            string basis;
            if (GetQuote(out bid, out ask))
            {
                trigger = isLong ? bid : ask;
                basis = isLong ? "BID" : "ASK";
            }
            else if (_lastTradePrice > 0)
            {
                trigger = _lastTradePrice;
                basis = "LAST";
            }
            else return;

            // Stop loss (ticks from the fill price) is checked first; it wins if both are somehow true.
            double entry = double.IsNaN(_openRecord.FillPrice) ? _paperPosition.OpenPrice : _openRecord.FillPrice;
            // Peak progress = best favorable move so far as a fraction of entry -> frozen target (floored at 0).
            double distance = Math.Abs(target - entry);
            if (distance > 0)
            {
                double progressNow = (isLong ? trigger - entry : entry - trigger) / distance;
                if (progressNow > _peakProgress) _peakProgress = progressNow;
            }
            // MFE / MAE in points from the fill, measured on the exit-side price (bid for longs, ask for shorts).
            double moved = isLong ? trigger - entry : entry - trigger;
            if (moved > _mfePoints) _mfePoints = moved;
            if (-moved > _maePoints) _maePoints = -moved;
            bool stopHit = stopLoss > 0 && entry > 0 &&
                (isLong ? trigger <= entry - stopLoss * _tickSize
                        : trigger >= entry + stopLoss * _tickSize);
            bool targetHit = isLong ? trigger >= target : trigger <= target;
            if (!stopHit && !targetHit) return;
            string reason = (stopHit ? "STOP_LOSS_" : "FROZEN_TARGET_") + basis;

            _exitRequested = true;
            _exitRequestedUtc = DateTime.UtcNow;
            TradingOperationResult result = Core.Instance.ClosePosition(_paperPosition);
            if (result.Status == TradingOperationResultStatus.Success)
            {
                Log($"PAPER exit requested ({(stopHit ? "STOP LOSS" : "frozen target")}): {basis} {trigger:F2}, " +
                    $"entry {entry:F2}, target {target:F2}; signal={_paperSignalId}", StrategyLoggingLevel.Trading);
                MarkExit(_openRecord, DateTime.UtcNow, reason, trigger, target);
            }
            else
            {
                _exitRequested = false;
                Log("PAPER exit failed: " + result.Message, StrategyLoggingLevel.Error);
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
                CheckProgressStop(nowUtc);
                FinalizePending(nowUtc, false);
                ReconcileOrphanedPositions(nowUtc);
            }
        }

        // ------------------------------------------------------------------
        // Orders and positions
        // ------------------------------------------------------------------

        private bool TryPlacePaperOrder(TradeRecord record)
        {
            if (!EnablePaperOrders) { record.RejectReason = "shadow_mode"; return false; }
            if (_paperTradingBlockedAfterReconnect)
            {
                Log("Signal not traded: paper execution is blocked after reconnect until strategy restart.",
                    StrategyLoggingLevel.Error);
                record.RejectReason = "blocked_after_reconnect";
                return false;
            }
            if (!string.Equals(PaperConfirmation?.Trim(), "PAPER ONLY", StringComparison.Ordinal))
            {
                Log("Signal not traded: Paper confirmation must equal PAPER ONLY.", StrategyLoggingLevel.Error);
                record.RejectReason = "confirmation_text";
                return false;
            }
            if (CurrentAccount == null)
            {
                Log("Signal not traded: no account selected.", StrategyLoggingLevel.Error);
                record.RejectReason = "no_account";
                return false;
            }
            if (_paperEntryPending || _paperPosition != null) { record.RejectReason = "position_open"; return false; }
            if (Core.Instance.Positions.Any(p => IsOurAccount(p.Account) && IsOurSymbol(p.Symbol)))
            { record.RejectReason = "account_has_position"; return false; }
            if (Core.Instance.Orders.Any(o => IsOurAccount(o.Account) && IsOurSymbol(o.Symbol)
                && (o.Status == OrderStatus.Opened || o.Status == OrderStatus.PartiallyFilled)))
            { record.RejectReason = "working_order_exists"; return false; }

            _paperEntryPending = true;
            _paperPendingSide = record.Side;
            _paperSignalId = record.SignalId;
            _openRecord = record;

            record.SubmitUtc = DateTime.UtcNow;
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
            record.AckUtc = DateTime.UtcNow;
            if (result.Status != TradingOperationResultStatus.Success)
            {
                _paperEntryPending = false;
                _paperSignalId = "";
                _openRecord = null;
                record.RejectReason = "order_failed";
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
                    _nextProgressCheckUtc = DateTime.MinValue;
                    _peakProgress = 0;
                    _mfePoints = _maePoints = 0;
                    if (_openRecord != null)
                    {
                        _openRecord.PositionId = position.Id;
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
                if (_openRecord != null)
                {
                    MarkExit(_openRecord, DateTime.UtcNow, "CLOSED_ELSEWHERE", double.NaN, _openRecord.Middle);
                    // Write once the closing fill notifications have had a moment to arrive.
                    _openRecord.ClosedUtc = DateTime.UtcNow;
                    _pendingRecords.Add(_openRecord);
                }
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
            bool flatten = FlattenAtClose && IsFlattenTimeEt(nowUtc);
            if (flatten && !_closedState)
            {
                _longArmed = _shortArmed = false;
                _closedState = true;
                _nextFlattenUtc = DateTime.MinValue;
            }
            else if (!flatten && _closedState)
            {
                _closedState = false;
            }
            if (flatten) FlattenAll(nowUtc);
        }

        // From 4:00 PM ET, close every position (and cancel working orders) on our account/symbol.
        // Keeps checking while the window is open, so a failed close or a late fill is retried.
        private void FlattenAll(DateTime nowUtc)
        {
            if (nowUtc < _nextFlattenUtc || CurrentAccount == null || CurrentSymbol == null) return;
            List<Position> positions = Core.Instance.Positions
                .Where(p => IsOurAccount(p.Account) && IsOurSymbol(p.Symbol)).ToList();
            bool working = Core.Instance.Orders.Any(o => IsOurAccount(o.Account) && IsOurSymbol(o.Symbol)
                && (o.Status == OrderStatus.Opened || o.Status == OrderStatus.PartiallyFilled));
            if (positions.Count == 0 && !working) return;

            _nextFlattenUtc = nowUtc.AddSeconds(5); // do not stack close orders while one is in flight
            if (working) CancelWorkingOrders("4:00 PM ET close");

            foreach (Position p in positions)
            {
                bool tracked = _paperPosition != null && p.Id == _paperPosition.Id;
                // A close already requested in the last 5 seconds (e.g. target/stop) is still in flight.
                if (tracked && _exitRequested && (nowUtc - _exitRequestedUtc).TotalSeconds < 5) continue;

                TradingOperationResult result = Core.Instance.ClosePosition(p);
                if (result.Status == TradingOperationResultStatus.Success)
                {
                    Log($"4:00 PM ET close requested: position {p.Id} {p.Side} {p.Quantity}.", StrategyLoggingLevel.Trading);
                    if (tracked)
                    {
                        if (!_exitRequested && _openRecord != null)
                            MarkExit(_openRecord, nowUtc, "SESSION_CLOSE", double.NaN, _openRecord.Middle);
                        _exitRequested = true;
                        _exitRequestedUtc = nowUtc;
                    }
                }
                else
                    Log($"4:00 PM ET close FAILED for position {p.Id}: {result.Message}. Retrying in 5s.",
                        StrategyLoggingLevel.Error);
            }
        }

        // Positions are flattened from 4:00 PM ET until the 6:00 PM ET reopen.
        private bool IsFlattenTimeEt(DateTime utc)
        {
            DateTime et = ToEastern(utc);
            return et.Hour >= 16 && et.Hour < 18;
        }

        // Entry window only (Eastern time of day). Exits, stops and the 4 PM close are never gated by this.
        private bool IsTradingTimeValid(TimeSpan t)
        {
            var windows = new (int sh, int sm, int eh, int em)[]
            {
                ( 8,  45, 15,  30),
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

        // Records why/when an exit was requested (first reason wins) plus peak progress at that moment.
        private void MarkExit(TradeRecord r, DateTime exitUtc, string reason, double trigger, double target)
        {
            if (r == null || r.ExitReason.Length > 0) return;
            r.ExitUtc = exitUtc;
            r.ExitReason = reason;
            r.ExitTrigger = trigger;
            r.TargetAtExit = target;
            r.PeakProgress = _peakProgress;
            r.MfePoints = _mfePoints;
            r.MaePoints = _maePoints;
        }

        // Writes closed trades once their exit fills have had time to arrive (or immediately when forced).
        private void FinalizePending(DateTime nowUtc, bool force)
        {
            for (int i = _pendingRecords.Count - 1; i >= 0; i--)
            {
                TradeRecord r = _pendingRecords[i];
                if (!force && (nowUtc - r.ClosedUtc).TotalSeconds < 5) continue;
                _pendingRecords.RemoveAt(i);
                WriteTradeRow(r);
            }
        }

        private TradeRecord FindRecord(string positionId)
        {
            if (string.IsNullOrEmpty(positionId)) return null;
            if (_openRecord != null && _openRecord.PositionId == positionId) return _openRecord;
            return _pendingRecords.FirstOrDefault(r => r.PositionId == positionId);
        }

        // Collects the broker's actual fills: exit fills (opposite side) give the real exit price and P&L.
        private void OnTradeAdded(Trade t)
        {
            lock (_sync)
            {
                if (_stopping || t == null) return;
                if (!IsOurAccount(t.Account) || !IsOurSymbol(t.Symbol)) return;

                if (!_tradePropsLogged)
                {
                    _tradePropsLogged = true;
                    Log("Trade properties: " + string.Join("; ", t.GetType().GetProperties()
                        .Select(p => { object v = null; try { v = p.GetValue(t); } catch { } return p.Name + "=" + v; })),
                        StrategyLoggingLevel.Info);
                }

                // Match by position id; if the broker's id differs, fall back to the trade we are managing
                // (open record) or one that closed in the last 10 seconds.
                TradeRecord r = FindRecord(t.PositionId);
                string matchedBy = "positionId";
                if (r == null)
                {
                    matchedBy = "fallback";
                    r = _openRecord != null && _openRecord.FillUtc != DateTime.MinValue
                        ? _openRecord
                        : _pendingRecords.LastOrDefault(p => (DateTime.UtcNow - p.ClosedUtc).TotalSeconds < 10);
                }

                object sideObj = Prop(t, "Side");
                bool sideKnown = sideObj is Side;
                Log($"Trade event: order={t.OrderId} position={t.PositionId} side={sideObj} price={t.Price:F4} " +
                    $"qty={t.Quantity} matched={(r == null ? "none" : matchedBy)}", StrategyLoggingLevel.Info);
                if (r == null) return;

                double fee = PnlNumber(t, "Fee");
                if (!double.IsNaN(fee)) r.Fee = (double.IsNaN(r.Fee) ? 0 : r.Fee) + fee;

                // Exit fill = opposite side to the entry; if side is unreadable, only count it once an exit is underway.
                bool isExit = sideKnown ? (Side)sideObj != r.Side
                                        : (r != _openRecord || _exitRequested);
                if (!isExit) return;

                r.ExitFillQty += t.Quantity;
                r.ExitFillNotional += t.Price * t.Quantity;
                r.ExitFillUtc = DateTime.UtcNow;
                double net = PnlNumber(t, "NetPnl");
                if (!double.IsNaN(net)) r.NetPnl = (double.IsNaN(r.NetPnl) ? 0 : r.NetPnl) + net;
            }
        }

        private static object Prop(object o, string name)
        {
            return o == null ? null : o.GetType().GetProperty(name)?.GetValue(o);
        }

        // Broker P&L/fee members may be plain numbers or PnL items with a Value; blank if unavailable.
        private static double PnlNumber(object o, string name)
        {
            try
            {
                object v = Prop(o, name);
                if (v == null) return double.NaN;
                object inner = Prop(v, "Value");
                return Convert.ToDouble(inner ?? v, CultureInfo.InvariantCulture);
            }
            catch { return double.NaN; }
        }

        private void WriteTradeRow(TradeRecord r)
        {
            double dir = r.Side == Side.Buy ? 1.0 : -1.0;
            double exitFill = r.ExitFillQty > 0 ? r.ExitFillNotional / r.ExitFillQty : double.NaN;
            double pointsTrigger = double.IsNaN(r.FillPrice) || double.IsNaN(r.ExitTrigger)
                ? double.NaN : (r.ExitTrigger - r.FillPrice) * dir;
            double pointsFill = double.IsNaN(r.FillPrice) || double.IsNaN(exitFill)
                ? double.NaN : (exitFill - r.FillPrice) * dir;
            var values = new List<string>
            {
                _runId, r.SignalId, r.Side.ToString(), CsvTime(r.SetupBarUtc), CsvTime(r.SignalBarUtc),
                Csv(r.SignalClose), Csv(r.Upper), Csv(r.Middle), Csv(r.Lower),
                CsvTime(r.SubmitUtc), CsvTime(r.FillUtc), Csv(r.FillPrice),
                CsvTime(r.ExitUtc), r.ExitReason, Csv(r.ExitTrigger), Csv(exitFill), CsvTime(r.ExitFillUtc),
                r.ExitFillQty > 0 ? r.ExitFillQty.ToString(CultureInfo.InvariantCulture) : "",
                Csv(r.TargetAtExit), Csv(r.PeakProgress),
                Csv(r.MfePoints / _tickSize, "F1"), Csv(r.MaePoints / _tickSize, "F1"),
                Csv(pointsTrigger / _tickSize, "F1"), Csv(pointsFill / _tickSize, "F1"),
                Csv(r.NetPnl), Csv(r.Fee),
                CsvTime(r.CallbackUtc), CsvTime(r.CalcDoneUtc), CsvTime(r.AckUtc),
                Ms(r.CallbackUtc, r.CalcDoneUtc), Ms(r.CalcDoneUtc, r.SubmitUtc),
                Ms(r.SubmitUtc, r.AckUtc), Ms(r.SubmitUtc, r.FillUtc), r.RejectReason ?? ""
            };
            lock (_csvSync) _tradeBuffer.Add(string.Join(",", values));
        }

        private static string Ms(DateTime from, DateTime to)
        {
            return from == DateTime.MinValue || to == DateTime.MinValue
                ? "" : (to - from).TotalMilliseconds.ToString("F1", CultureInfo.InvariantCulture);
        }

        // One row per closed bar (every checkpoint), including rejected entries.
        private void WriteBarRow(BarCalc b, string result, string reject,
            DateTime callbackUtc, DateTime calcDoneUtc, DateTime decisionUtc)
        {
            double bid, ask;
            bool haveQuote = GetQuote(out bid, out ask);
            DateTime now = DateTime.UtcNow;
            string setup = _longArmed ? "LONG_ARMED" : _shortArmed ? "SHORT_ARMED" : "NONE";
            double quoteAge = _lastQuoteUtc == DateTime.MinValue ? double.NaN : (now - _lastQuoteUtc).TotalMilliseconds;
            var values = new List<string>
            {
                _runId, CsvTime(b.Utc), Csv(b.Open), Csv(b.High), Csv(b.Low), Csv(b.Close),
                Csv(b.Upper), Csv(b.Middle), Csv(b.Lower), Csv(b.Tr), Csv(_widthEma), _barsSeen.ToString(CultureInfo.InvariantCulture),
                setup, result, reject,
                Csv((b.High - b.Low) / _tickSize, "F1"), Csv((b.Close - b.Open) / _tickSize, "F1"),
                Csv((b.Close - b.Upper) / _tickSize, "F1"), Csv((b.Close - b.Lower) / _tickSize, "F1"),
                haveQuote ? Csv(bid) : "", haveQuote ? Csv(ask) : "",
                haveQuote ? Csv((ask - bid) / _tickSize, "F1") : "", Csv(quoteAge, "F0"),
                CsvTime(callbackUtc), CsvTime(calcDoneUtc), CsvTime(decisionUtc),
                Ms(callbackUtc, calcDoneUtc),
                Ms(b.Utc.AddSeconds(BarSeconds), callbackUtc)
            };
            lock (_csvSync) _barBuffer.Add(string.Join(",", values));
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
                FlushBuffer(_tradeBuffer, _tradeCsv);
                FlushBuffer(_barBuffer, _barCsv);
            }
        }

        private void FlushBuffer(List<string> buffer, string path)
        {
            if (string.IsNullOrEmpty(path)) return;
            List<string> rows;
            lock (_csvSync) rows = new List<string>(buffer);
            if (rows.Count == 0) return;
            try
            {
                File.AppendAllLines(path, rows);
            }
            catch (Exception ex)
            {
                Log("CSV flush failed; rows retained: " + ex.Message, StrategyLoggingLevel.Error);
                return;
            }
            lock (_csvSync) buffer.RemoveRange(0, Math.Min(rows.Count, buffer.Count));
        }

        private static string Csv(double value, string format = "F4")
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
