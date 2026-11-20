using System;
using System.Collections.Generic;
using System.Diagnostics.Metrics;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using TradingPlatform.BusinessLayer;

namespace CandleMomentum
{
    /// <summary>
    /// Intraday futures basket: MES, MNQ, MGC, MCL, MHG, one basket at a time, QtyPerLeg contracts per leg (input, default 1)
    ///
    /// Signal: checked 2 seconds after every 1-minute close. If EVERY symbol's last two completed 1-minute
    /// candles point the same way (both close > open, or both close < open; a doji is no direction),
    /// a basket opens: each symbol goes long if its two candles were up, short if they were down.
    /// No new baskets and no open basket during the blackout 9:00-10:15 ET (an open basket is
    /// flattened at 9:00, BLACKOUT_EXIT), or from 16:00 until the 18:00 reopen (flattened at 16:00,
    /// DAILY_CLOSE_EXIT), so no basket is held through the daily close or the weekend.
    ///
    /// Legs whose bid/ask is fresh and spread normal are entered at market at once; any other leg
    /// waits and joins when its quote is good, up to 5 minutes after entry, else it is dropped. An
    /// on-time leg unfilled after 5 minutes flattens the basket; a late leg that fails is just dropped.
    ///
    /// Exits (checked every second on basket P&L at last trade prices, net of entry fees):
    /// TAKE_PROFIT at +$50, STOP_LOSS at -$150, ACCOUNT_STOP when this run's realized P&L plus the
    /// open basket reaches -$300 (also stops all further baskets until restart). All three are inputs.
    ///
    /// Logs: Downloads\CandleMomentum_baskets.csv (one row per basket), CandleMomentum_days.csv (one row
    /// per day the strategy runs through). Nothing is saved between runs: daily and cumulative P&L
    /// and the account stop start at zero each time the strategy starts.
    /// </summary>
    public class CandleMomentum : Strategy, ICurrentAccount
    {

        [InputParameter("Account", 1)]
        public Account CurrentAccount { get; set; }

        [InputParameter("MES symbol (front month)", 2)]
        public Symbol MesSymbol { get; set; }

        [InputParameter("MNQ symbol (front month)", 3)]
        public Symbol MnqSymbol { get; set; }

        [InputParameter("MGC symbol (front month)", 4)]
        public Symbol MgcSymbol { get; set; }

        [InputParameter("MCL symbol (front month)", 5)]
        public Symbol MclSymbol { get; set; }

        [InputParameter("MHG symbol (front month)", 6)]
        public Symbol MhgSymbol { get; set; }

        // Contracts per leg, same for every symbol in the basket.
        [InputParameter("Quantity per symbol", 7, 1, 100, 1, 0)]
        public int QtyPerLeg = 1;

        // Fees: per side, per contract, all-in. Defaults are the AMP Futures estimate.
        // On = P&L, stops and limits use these; off = use the fee the broker reports on each fill.
        // Both are logged either way (fees_broker / fees_estimated).
        [InputParameter("Use estimated fees below (off = broker-reported fees)", 9)]
        public bool UseFeeEstimates = true;

        [InputParameter("MES fee per side ($)", 10, 0, 100, 0.01, 2)]
        public double FeeMes = 0.60;

        [InputParameter("MNQ fee per side ($)", 11, 0, 100, 0.01, 2)]
        public double FeeMnq = 0.60;

        [InputParameter("MGC fee per side ($)", 12, 0, 100, 0.01, 2)]
        public double FeeMgc = 0.85;

        [InputParameter("MCL fee per side ($)", 13, 0, 100, 0.01, 2)]
        public double FeeMcl = 0.75;

        [InputParameter("MHG fee per side ($)", 14, 0, 100, 0.01, 2)]
        public double FeeMhg = 0.80;

        // Dollar amounts for the whole basket (all legs together), not scaled by quantity.
        [InputParameter("Basket stop loss ($)", 15, 1, 100000, 1, 2)]
        public double BasketStopLoss = 30.00;

        [InputParameter("Basket take profit ($)", 16, 1, 100000, 1, 2)]
        public double BasketTakeProfit = 50.00;

        // Realized P&L of this run plus the open basket. Hitting it flattens and stops new baskets.
        [InputParameter("Account stop loss ($, this run)", 17, 1, 1000000, 1, 2)]
        public double AccountStopLoss = 300.00;

        [InputParameter("Starting Balance", 18)]
        public double StartingBalance { get; set; }

        // ------------------------------------------------------------------
        // Constants
        // ------------------------------------------------------------------

        private static readonly (string Key, double DollarsPerPoint, double SpecTick)[] SymbolSpecs =
        {
            ("MES", 5.00, 0.25),
            ("MNQ", 2.00, 0.25),
            ("MGC", 10.00, 0.10),
            ("MCL", 100.00, 0.01),
            ("MHG", 2500.00, 0.0005),
        };

        // No-trade windows, Eastern time, start inclusive / end exclusive. An open basket is
        // flattened when a window starts and no new basket opens inside one.
        //  - 9:00-10:15 morning blackout.
        //  - 16:00-18:00 forced daily close: flat by 16:00, no new baskets until the 18:00 reopen,
        //    so nothing is carried through the 17:00 close or over the weekend.
        private static readonly (TimeSpan Start, TimeSpan End, string ExitReason)[] NoTradeWindows =
        {
            (new TimeSpan(9, 0, 0),  new TimeSpan(10, 15, 0), "BLACKOUT_EXIT"),
            (new TimeSpan(16, 0, 0), new TimeSpan(18, 0, 0),  "DAILY_CLOSE_EXIT"),
        };

        // Pre-send check, per leg: the bid/ask must have updated within QuoteMaxAgeSeconds and the
        // spread must be at most MaxSpreadTicks. Legs that pass are sent at once; a leg that fails
        // waits and joins the basket as soon as its quote passes, up to LateJoinMinutes after entry;
        // after that it is dropped and the basket runs without it.
        private const int QuoteMaxAgeSeconds = 15;
        private const double MaxSpreadTicks = 5;
        private const int EntryFillTimeoutMinutes = 5;
        private const int LateJoinMinutes = 5;

        // Check the signal this long after each minute starts so the last trades of the previous
        // minute are in the bars. If the check can't run within SignalLateLimit of the minute
        // start, that minute is skipped.
        private static readonly TimeSpan EntryGrace = TimeSpan.FromSeconds(2);
        private static readonly TimeSpan SignalLateLimit = TimeSpan.FromSeconds(10);

        // A symbol missing its latest bar while other symbols have theirs gets its history
        // re-fetched, at most this often (thin symbols like MHG often just have no trades).
        private static readonly TimeSpan HistoryReloadMinInterval = TimeSpan.FromMinutes(15);

        // ------------------------------------------------------------------
        // Types
        // ------------------------------------------------------------------

        private sealed class Slot
        {
            public int Index;
            public string Key;
            public double DollarsPerPoint;
            public double SpecTick;
            public Symbol Symbol;
            public double TickSize;
            public double FeePerSide;
            public HistoricalData History;
            public DateTime LastReloadUtc = DateTime.MinValue;
            // Live bid/ask from NewQuote; QuoteTimeUtc = when it last arrived (MinValue = none yet).
            public double QuoteBid = double.NaN, QuoteAsk = double.NaN;
            public DateTime QuoteTimeUtc = DateTime.MinValue;
        }

        private sealed class Leg
        {
            public Slot Slot;
            public Side Side;
            public int Dir;
            public double EntryRef;
            public string EntryOrderId;
            // Sent = entry order sent. A leg whose quote failed the pre-send check waits (not Sent)
            // and joins when its quote is good; Dropped = never joined, or its late order failed.
            public bool Sent, Late, Dropped, Settled;
            public DateTime SentUtc;
            public bool Active => Sent && !Dropped;
            public bool Filled(int qty) => EntryQty >= qty - 1e-9;
            public bool OrderFailed;
            public string FailNote = "";
            public double EntryQty, EntryNotional, ExitQty, ExitNotional;
            public double BrokerFees, EstimatedFees;   // both accumulated per fill
            public bool UseEstimatedFees;
            public double Fees => UseEstimatedFees ? EstimatedFees : BrokerFees;
            public double ExitPriceFallback = double.NaN;
            public DateTime MissingSinceUtc = DateTime.MinValue;
            public double EntryFill => EntryQty > 0 ? EntryNotional / EntryQty : double.NaN;
            public double ExitFill => ExitQty > 0 ? ExitNotional / ExitQty : ExitPriceFallback;
            public double TouchAtSend = double.NaN;     // ask for a buy, bid for a sell, when sent
            public string TouchSource = "";
            // Fill vs the bid/ask at send. Positive = worse.
            public double TouchSlippageTicks => double.IsNaN(EntryFill) || double.IsNaN(TouchAtSend) || Slot.TickSize <= 0
                ? double.NaN : (EntryFill - TouchAtSend) * Dir / Slot.TickSize;
            // Fill vs entry_ref (second signal candle's close): logged only. Positive = worse.
            public double SlippageTicks => double.IsNaN(EntryFill) || Slot.TickSize <= 0
                ? double.NaN : (EntryFill - EntryRef) * Dir / Slot.TickSize;
        }

        private sealed class BasketLog
        {
            public DateTime DateEt;
            public int Number;                 // basket number within the day
            public DateTime FirstCandleEt;     // start of the first of the two signal candles
            public DateTime EntryEt;
            public string Outcome = "";
            public string Detail = "";
            // Two-candle move: second candle close vs first candle open, percent.
            public readonly Dictionary<string, double> MovePct = new Dictionary<string, double>();
            public readonly Dictionary<string, double> EntryRef = new Dictionary<string, double>();
            public readonly List<string> Longs = new List<string>();
            public readonly List<string> Shorts = new List<string>();
            public readonly List<Leg> Legs = new List<Leg>();
            public DateTime FilledEt = DateTime.MinValue;
            public DateTime ExitEt = DateTime.MinValue;
            public double Mae = double.NaN, Mfe = double.NaN;     // basket P&L low / high, dollars
            public double Gross = double.NaN, Fees = double.NaN, Net = double.NaN;
            public double BrokerFees = double.NaN, EstimatedFees = double.NaN;
            public bool ExitPriceEstimated;

            public void AddDetail(string text)
            {
                Detail = string.IsNullOrEmpty(Detail) ? text : Detail + " | " + text;
            }
        }

        private enum BasketState { Idle, Entering, InBasket, Exiting }

        // ------------------------------------------------------------------
        // State
        // ------------------------------------------------------------------

        private readonly object _sync = new object();
        private readonly object _csvLock = new object();
        private readonly List<Slot> _slots = new List<Slot>();
        private bool _stopping;
        private bool _ready;

        private BasketState _state = BasketState.Idle;
        private BasketLog _current;
        private DateTime _enterStartUtc, _exitStartUtc, _lastCloseRequestUtc = DateTime.MinValue, _flatSinceUtc;
        private DateTime _lastMinuteLoggedEt = DateTime.MinValue;
        private DateTime _lastSignalCheckEt = DateTime.MinValue;
        private string _lastBlockReason = "";
        private string _exitReason = "";
        private bool _exitSlowLogged, _exitFailureLogged, _blackoutLogged;

        // Daily / cumulative (this run only; reset on every start)
        private DateTime _dayEt = DateTime.MinValue;
        private double _dailyPnl, _cumulativePnl;
        private bool _strategyKilled, _dayRowWritten;
        private int _basketsStarted, _basketsTraded;

        private string _basketsCsv, _daysCsv;
        private System.Timers.Timer _timer;
        private System.Timers.Timer _connectionWatchdog;
        private bool _lastKnownConnected = true;
        private bool _rebindInProgress;
        private readonly Dictionary<Connection, EventHandler<ConnectionStateChangedEventArgs>>
            _connectionHandlers = new Dictionary<Connection, EventHandler<ConnectionStateChangedEventArgs>>();

        public CandleMomentum()
        {
            Name = "CandleMomentum";
            Description = "Basket MES/MNQ/MGC/MCL/MHG: when every symbol has 2 consecutive 1-minute candles in the same " +
                          "direction, each symbol trades its own direction. Basket TP/SL, account stop, no trading 9:00-10:15 ET, flat at 16:00 ET until the 18:00 reopen.";
        }

        // ------------------------------------------------------------------
        // Lifecycle
        // ------------------------------------------------------------------

        protected override void OnRun()
        {
            _stopping = false;
            _ready = false;
            _slots.Clear();

            Symbol[] chosen = { MesSymbol, MnqSymbol, MgcSymbol, MclSymbol, MhgSymbol };
            for (int i = 0; i < SymbolSpecs.Length; i++)
            {
                if (chosen[i] == null)
                {
                    Log($"{SymbolSpecs[i].Key} symbol must be selected.", StrategyLoggingLevel.Error);
                    return;
                }
                Symbol symbol = Core.GetSymbol(chosen[i].CreateInfo());
                if (symbol == null || symbol.TickSize <= 0)
                {
                    Log($"{SymbolSpecs[i].Key}: symbol could not be loaded or has an invalid tick size.", StrategyLoggingLevel.Error);
                    return;
                }
                _slots.Add(new Slot
                {
                    Index = i,
                    Key = SymbolSpecs[i].Key,
                    DollarsPerPoint = SymbolSpecs[i].DollarsPerPoint,
                    SpecTick = SymbolSpecs[i].SpecTick,
                    FeePerSide = Math.Max(0, new[] { FeeMes, FeeMnq, FeeMgc, FeeMcl, FeeMhg }[i]),
                    Symbol = symbol,
                    TickSize = symbol.TickSize
                });
            }
            if (CurrentAccount == null)
            {
                Log("Account must be selected.", StrategyLoggingLevel.Error);
                return;
            }
            if (QtyPerLeg < 1)
            {
                Log("Quantity per symbol must be at least 1.", StrategyLoggingLevel.Error);
                return;
            }
            if (BasketStopLoss <= 0 || BasketTakeProfit <= 0 || AccountStopLoss <= 0)
            {
                Log("Basket stop loss, basket take profit and account stop loss must all be above 0.", StrategyLoggingLevel.Error);
                return;
            }
            if (_slots.Select(s => s.Symbol.Id).Distinct().Count() != _slots.Count)
            {
                Log("The same symbol is selected in more than one slot.", StrategyLoggingLevel.Error);
                return;
            }
            foreach (Slot s in _slots)
            {
                bool tickOk = Math.Abs(s.TickSize - s.SpecTick) < s.SpecTick * 1e-6;
                string expiry = s.Symbol.ExpirationDate == default ? "n/a" : s.Symbol.ExpirationDate.ToString("yyyy-MM-dd");
                Log($"{s.Key} = {s.Symbol.Name}, tick {s.TickSize}, ${s.DollarsPerPoint}/point " +
                    $"(${s.DollarsPerPoint * s.TickSize:F2}/tick), expires {expiry}." +
                    $" Fee ${s.FeePerSide:F2}/side." +
                    (tickOk ? "" : $" WARNING: spec tick is {s.SpecTick}; check the symbol."),
                    tickOk ? StrategyLoggingLevel.Info : StrategyLoggingLevel.Error);
            }

            string downloads = Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.UserProfile), "Downloads");
            _basketsCsv = Path.Combine(downloads, "CandleMomentum_baskets.csv");
            _daysCsv = Path.Combine(downloads, "CandleMomentum_days.csv");
            try
            {
                EnsureHeader(_basketsCsv, BasketsHeader());
                EnsureHeader(_daysCsv, DaysHeader);
            }
            catch (Exception ex) { Log("CSV setup failed: " + ex.Message, StrategyLoggingLevel.Error); }

            lock (_sync)
            {
                _state = BasketState.Idle;
                _current = null;
                ResetSessionState();
                if (!LoadHistories()) return;
            }

            foreach (Slot s in _slots)
            {
                s.Symbol.NewQuote -= OnNewQuote;
                s.Symbol.NewQuote += OnNewQuote;
            }
            Core.Instance.TradeAdded -= OnTradeAdded;
            Core.Instance.TradeAdded += OnTradeAdded;

            Core.Instance.Connections.ConnectionAdded += OnConnectionAdded;
            Core.Instance.Connections.ConnectionRemoved += OnConnectionRemoved;
            foreach (Connection connection in Core.Instance.Connections.All)
                SubscribeToConnection(connection);
            _lastKnownConnected = Core.Instance.Connections.All.Any(c => c.State == ConnectionState.Connected);
            _connectionWatchdog = new System.Timers.Timer(15000) { AutoReset = true };
            _connectionWatchdog.Elapsed += (s, e) => CheckConnectionHealth();
            _connectionWatchdog.Start();

            lock (_sync)
            {
                DateTime startEt = ToEastern(DateTime.UtcNow);
                RollDayIfNeeded(startEt);
                // Don't act on the minute that is already under way; start with the next minute close.
                _lastSignalCheckEt = TruncateMinute(startEt);
            }

            _ready = true;
            _timer = new System.Timers.Timer(1000) { AutoReset = true };
            _timer.Elapsed += (s, e) => OnTimer();
            _timer.Start();

            Log($"CandleMomentum started. Signal: every symbol's last 2 completed 1-minute candles in the same direction, " +
                $"checked {EntryGrace.TotalSeconds:F0}s after each minute close. No trading " +
                string.Join(", ", NoTradeWindows.Select((t, i) => WindowText(i))) + " ET (open basket flattened at each window start). Entry MARKET, {QtyPerLeg} per leg, fill timeout {EntryFillTimeoutMinutes} min, " +
                $"pre-send check: bid/ask under {QuoteMaxAgeSeconds}s old and spread <= {MaxSpreadTicks} ticks. " +
                $"Basket TP +${BasketTakeProfit:F2}, SL -${BasketStopLoss:F2}, account stop -${AccountStopLoss:F2}. " +
                $"P&L uses {(UseFeeEstimates ? "ESTIMATED fees (inputs)" : "BROKER-reported fees")}. Logs: {_basketsCsv}, {_daysCsv}.",
                StrategyLoggingLevel.Info);
        }

        protected override void OnStop()
        {
            _stopping = true;
            _timer?.Stop();
            _timer?.Dispose();
            _timer = null;
            _connectionWatchdog?.Stop();
            _connectionWatchdog?.Dispose();
            _connectionWatchdog = null;

            // Flatten before detaching, so closing fills still reach OnTradeAdded.
            if (_ready)
            {
                FlattenOnStop();
                lock (_sync)
                {
                    if (_dayEt != DateTime.MinValue && !_dayRowWritten) WriteDayRow("strategy stopped (partial day)");
                }
            }

            foreach (Slot s in _slots)
            {
                if (s.Symbol == null) continue;
                s.Symbol.NewQuote -= OnNewQuote;
            }
            Core.Instance.TradeAdded -= OnTradeAdded;
            foreach (var item in _connectionHandlers.ToList())
                item.Key.StateChanged -= item.Value;
            _connectionHandlers.Clear();
            Core.Instance.Connections.ConnectionAdded -= OnConnectionAdded;
            Core.Instance.Connections.ConnectionRemoved -= OnConnectionRemoved;

            lock (_sync)
            {
                UnloadHistories();
            }
            Log("CandleMomentum stopped.", StrategyLoggingLevel.Info);
        }

        // On stop: cancel working orders and close every position on the basket symbols in this
        // account, wait up to StopFlattenWaitSeconds for the closes and their fills, then log the
        // open basket (exit reason STOPPED) and add its P&L to the daily / cumulative totals.
        private const int StopFlattenWaitSeconds = 5;

        private void FlattenOnStop()
        {
            DateTime nowUtc = DateTime.UtcNow;
            lock (_sync)
            {
                // Stopping is a deliberate user action: allow symbols that hit the refusal limit one
                // more try, but keep waiting on closes the broker already accepted.
                ResetCloseTracking(keepAccepted: true);
                if (_state == BasketState.Entering || _state == BasketState.InBasket)
                {
                    BeginExit("STOPPED", "strategy stopped", nowUtc, ToEastern(nowUtc));
                }
                else if (_state == BasketState.Exiting)
                {
                    _current.AddDetail("strategy stopped while exiting");
                    CancelWorkingOrders("strategy stopped");
                    CloseAllPositions(nowUtc, "strategy stopped");
                }
                else if (AnyPositionsOrWorkingOrders())
                {
                    Log("Strategy stopped: closing positions / cancelling orders on basket symbols.", StrategyLoggingLevel.Trading);
                    CancelWorkingOrders("strategy stopped");
                    CloseAllPositions(nowUtc, "strategy stopped");
                }
                else return;
            }

            DateTime deadline = DateTime.UtcNow.AddSeconds(StopFlattenWaitSeconds);
            bool flat = false;
            while (DateTime.UtcNow < deadline)
            {
                lock (_sync)
                {
                    flat = !AnyPositionsOrWorkingOrders();
                    bool fillsIn = _current == null || _current.Legs.All(l => l.ExitQty >= l.EntryQty - 1e-9);
                    if (flat && fillsIn) break;
                    if (!flat && (DateTime.UtcNow - _lastCloseRequestUtc).TotalSeconds >= 2)
                    {
                        CancelWorkingOrders("strategy stopped retry");
                        CloseAllPositions(DateTime.UtcNow, "strategy stopped retry");
                    }
                }
                System.Threading.Thread.Sleep(250);
            }

            lock (_sync)
            {
                flat = !AnyPositionsOrWorkingOrders();
                if (_current != null)
                {
                    if (!flat) _current.AddDetail("not confirmed flat when the strategy stopped");
                    FinishBasket();
                }
                if (flat)
                    Log("Strategy stopped: basket symbols are flat.", StrategyLoggingLevel.Trading);
                else
                    Log($"Strategy stopped: positions or orders on basket symbols still open after {StopFlattenWaitSeconds}s. " +
                        "Check the platform and flatten manually.", StrategyLoggingLevel.Error);
            }
        }

        protected override void OnRemove()
        {
            MesSymbol = MnqSymbol = MgcSymbol = MclSymbol = MhgSymbol = null;
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
        // Market data
        // ------------------------------------------------------------------

        private bool LoadHistories()
        {
            try
            {
                UnloadHistories();
                foreach (Slot s in _slots)
                {
                    s.History = s.Symbol.GetHistory(Period.MIN1, HistoryType.Last, DateTime.UtcNow.AddHours(-2));
                    s.LastReloadUtc = DateTime.UtcNow;
                }
                Log("Loaded 1-minute bars: " + string.Join(", ", _slots.Select(s => $"{s.Key} {s.History?.Count ?? 0}")) + ".",
                    StrategyLoggingLevel.Info);
                return true;
            }
            catch (Exception ex)
            {
                Log("History load failed: " + ex.Message, StrategyLoggingLevel.Error);
                return false;
            }
        }

        // Backup for a history that stopped updating: fetch this symbol's 1-minute bars again.
        private bool ReloadHistory(Slot s)
        {
            s.LastReloadUtc = DateTime.UtcNow;
            try
            {
                HistoricalData fresh = s.Symbol.GetHistory(Period.MIN1, HistoryType.Last, DateTime.UtcNow.AddHours(-2));
                if (fresh == null) return false;
                s.History?.Dispose();
                s.History = fresh;
                return true;
            }
            catch (Exception ex)
            {
                Log($"{s.Key}: history reload failed: {ex.Message}", StrategyLoggingLevel.Error);
                return false;
            }
        }

        private void UnloadHistories()
        {
            foreach (Slot s in _slots)
            {
                s.History?.Dispose();
                s.History = null;
            }
        }

        private void OnNewQuote(Symbol symbol, Quote quote)
        {
            if (_stopping || quote == null) return;
            if (double.IsNaN(quote.Bid) || double.IsNaN(quote.Ask) || quote.Bid <= 0 || quote.Ask <= 0) return;
            lock (_sync)
            {
                Slot slot = _slots.FirstOrDefault(s => SameSymbol(s.Symbol, symbol));
                if (slot == null) return;
                slot.QuoteBid = quote.Bid;
                slot.QuoteAsk = quote.Ask;
                slot.QuoteTimeUtc = DateTime.UtcNow;
            }
        }

        // "" if this slot's bid/ask is fresh and the spread is normal, else the reason it isn't.
        private string QuoteProblem(Slot s, DateTime nowUtc)
        {
            if (s.QuoteTimeUtc == DateTime.MinValue) return $"{s.Key} no bid/ask received";
            double age = (nowUtc - s.QuoteTimeUtc).TotalSeconds;
            if (age > QuoteMaxAgeSeconds) return $"{s.Key} bid/ask {age:F0}s old > {QuoteMaxAgeSeconds}s";
            double spreadTicks = (s.QuoteAsk - s.QuoteBid) / s.TickSize;
            if (spreadTicks < -1e-6) return $"{s.Key} crossed quote bid {s.QuoteBid} ask {s.QuoteAsk}";
            if (spreadTicks > MaxSpreadTicks + 1e-6)
                return $"{s.Key} spread {spreadTicks:F0} ticks > {MaxSpreadTicks} (bid {s.QuoteBid} ask {s.QuoteAsk})";
            return "";
        }

        // The 1-minute bar that starts at minuteEt, or null if there is none (no trades that minute).
        private static HistoryItemBar FindBar(Slot slot, DateTime minuteEt)
        {
            HistoricalData h = slot.History;
            if (h == null) return null;
            int n = Math.Min(h.Count, 10);
            for (int k = 0; k < n; k++)
            {
                if (!(h[k, SeekOriginHistory.End] is HistoryItemBar bar)) continue;
                DateTime tEt = TruncateMinute(ToEastern(bar.TimeLeft));
                if (tEt == minuteEt) return bar;
                if (tEt < minuteEt) return null;
            }
            return null;
        }

        // +1 = up candle (close > open), -1 = down candle, 0 = no direction.
        private static int CandleDir(HistoryItemBar bar)
        {
            if (bar.Close > bar.Open) return 1;
            if (bar.Close < bar.Open) return -1;
            return 0;
        }

        // ------------------------------------------------------------------
        // Main loop (1 second)
        // ------------------------------------------------------------------

        private void OnTimer()
        {
            if (_stopping || !_ready) return;
            lock (_sync)
            {
                if (_stopping) return;
                try { Step(DateTime.UtcNow); }
                catch (Exception ex) { Log("Step error: " + ex, StrategyLoggingLevel.Error); }
            }
        }

        private void Step(DateTime nowUtc)
        {
            DateTime nowEt = ToEastern(nowUtc);
            RollDayIfNeeded(nowEt);

            EnforceBlackout(nowUtc, nowEt);
            switch (_state)
            {
                case BasketState.Entering: ManageEntering(nowUtc, nowEt); break;
                case BasketState.InBasket: ManageInBasket(nowUtc, nowEt); break;
                case BasketState.Exiting: ManageExiting(nowUtc, nowEt); break;
            }

            CheckForSignal(nowUtc, nowEt);
        }

        // The no-trade window containing this time, or -1.
        private static int NoTradeWindowAt(TimeSpan timeOfDayEt)
        {
            for (int i = 0; i < NoTradeWindows.Length; i++)
                if (timeOfDayEt >= NoTradeWindows[i].Start && timeOfDayEt < NoTradeWindows[i].End) return i;
            return -1;
        }

        private static bool InBlackout(TimeSpan timeOfDayEt) => NoTradeWindowAt(timeOfDayEt) >= 0;

        private static string WindowText(int i) => $"{NoTradeWindows[i].Start:hh\\:mm}-{NoTradeWindows[i].End:hh\\:mm}";

        private void RollDayIfNeeded(DateTime nowEt)
        {
            DateTime today = nowEt.Date;
            if (today == _dayEt) return;
            if (_dayEt != DateTime.MinValue && !_dayRowWritten)
                WriteDayRow("");
            _dayEt = today;
            _dailyPnl = 0;
            _dayRowWritten = false;
            _basketsStarted = 0;
            _basketsTraded = 0;
            Log($"New day {today:yyyy-MM-dd}. Cumulative P&L {_cumulativePnl:F2}" +
                (_strategyKilled ? " - ACCOUNT_STOP hit, no new baskets until restart." : "."), StrategyLoggingLevel.Info);
        }

        // No trading in a no-trade window: an open or entering basket is flattened when it starts.
        private void EnforceBlackout(DateTime nowUtc, DateTime nowEt)
        {
            int w = NoTradeWindowAt(nowEt.TimeOfDay);
            if (w < 0) { _blackoutLogged = false; return; }
            if (!_blackoutLogged)
            {
                _blackoutLogged = true;
                Log($"No-trade window {WindowText(w)} ET: no new baskets.", StrategyLoggingLevel.Info);
            }
            if (_state == BasketState.Entering || _state == BasketState.InBasket)
                BeginExit(NoTradeWindows[w].ExitReason, $"no trading {WindowText(w)} ET, basket P&L {Fmt(BasketPnl(_current))}",
                    nowUtc, nowEt);
        }

        // ------------------------------------------------------------------
        // Signal and entry
        // ------------------------------------------------------------------

        // Once per minute, just after the minute closes: do all symbols have two consecutive
        // completed 1-minute candles in the same direction? If so, open the basket.
        private void CheckForSignal(DateTime nowUtc, DateTime nowEt)
        {
            DateTime minute = TruncateMinute(nowEt);
            if (minute == _lastSignalCheckEt) return;
            TimeSpan into = nowEt - minute;
            if (into < EntryGrace) return;
            _lastSignalCheckEt = minute;
            if (into > SignalLateLimit) return;
            if (_state != BasketState.Idle || _strategyKilled) return;
            if (InBlackout(nowEt.TimeOfDay)) return;

            DateTime c1Et = minute.AddMinutes(-2), c2Et = minute.AddMinutes(-1);
            var bars = new Dictionary<Slot, (HistoryItemBar B1, HistoryItemBar B2)>();
            foreach (Slot s in _slots)
                bars[s] = (FindBar(s, c1Et), FindBar(s, c2Et));

            // A symbol missing its latest bar while others have theirs may have a stale history.
            if (bars.Values.Any(b => b.B2 != null))
            {
                foreach (Slot s in _slots.Where(s => bars[s].B2 == null && nowUtc - s.LastReloadUtc >= HistoryReloadMinInterval).ToList())
                {
                    bool reloaded = ReloadHistory(s);
                    if (reloaded) bars[s] = (FindBar(s, c1Et), FindBar(s, c2Et));
                    Log($"{s.Key}: no {c2Et:HH:mm} bar while other symbols have one; reloaded history - " +
                        (!reloaded ? "reload failed" : bars[s].B2 == null ? "still no bar" : "bar found") + ".",
                        StrategyLoggingLevel.Info);
                }
            }

            var dirs = new Dictionary<Slot, int>();
            foreach (Slot s in _slots)
            {
                var (b1, b2) = bars[s];
                if (b1 == null || b2 == null) return;            // no candle that minute: no signal
                int d1 = CandleDir(b1), d2 = CandleDir(b2);
                if (d1 == 0 || d1 != d2) return;                 // not two candles in the same direction
                dirs[s] = d1;
            }

            string candlesText = string.Join(", ", _slots.Select(s =>
                $"{s.Key} {(dirs[s] > 0 ? "UP" : "DOWN")} {bars[s].B1.Open}->{bars[s].B2.Close}"));

            // Pre-entry checks, before any order is sent. A bad quote only holds back that leg
            // (see LateJoinMinutes); it does not block the basket.
            string block = "";
            if (CurrentAccount == null) block = "no account";
            else if (!Core.Instance.Connections.All.Any(c => c.State == ConnectionState.Connected)) block = "not connected";
            else if (AnyPositionsOrWorkingOrders()) block = "a position or working order already exists on a basket symbol";
            if (block.Length > 0)
            {
                if (block != _lastBlockReason)
                    Log($"Signal {c1Et:HH:mm}-{c2Et:HH:mm} ({candlesText}) not entered: {block}. " +
                        "Logged once until the reason changes.", StrategyLoggingLevel.Error);
                _lastBlockReason = block;
                return;
            }
            _lastBlockReason = "";

            var log = new BasketLog
            {
                DateEt = _dayEt,
                Number = ++_basketsStarted,
                FirstCandleEt = c1Et,
                EntryEt = nowEt
            };
            foreach (Slot s in _slots)
            {
                var (b1, b2) = bars[s];
                log.MovePct[s.Key] = b1.Open > 0 ? (b2.Close / b1.Open - 1) * 100 : double.NaN;
                log.EntryRef[s.Key] = b2.Close;
                (dirs[s] > 0 ? log.Longs : log.Shorts).Add(s.Key);
                log.Legs.Add(new Leg
                {
                    Slot = s,
                    Side = dirs[s] > 0 ? Side.Buy : Side.Sell,
                    Dir = dirs[s],
                    EntryRef = b2.Close,
                    UseEstimatedFees = UseFeeEstimates
                });
            }

            _current = log;
            _state = BasketState.Entering;
            _enterStartUtc = nowUtc;
            Log($"Basket {log.Number}: SIGNAL {c1Et:HH:mm}-{c2Et:HH:mm}: {candlesText}. " +
                $"LONG {string.Join(",", log.Longs)} / SHORT {string.Join(",", log.Shorts)}.", StrategyLoggingLevel.Trading);

            var waiting = new List<string>();
            foreach (Leg leg in log.Legs)
            {
                string problem = QuoteProblem(leg.Slot, nowUtc);
                if (problem.Length == 0) PlaceEntry(leg, log.Number, nowUtc);
                else waiting.Add(problem);
            }
            if (waiting.Count > 0)
            {
                log.AddDetail("waiting to join: " + string.Join("; ", waiting));
                Log($"Basket {log.Number}: {waiting.Count} leg(s) held back by the quote check, will join when the quote is good " +
                    $"(until {log.EntryEt.AddMinutes(LateJoinMinutes):HH:mm:ss}): {string.Join("; ", waiting)}.",
                    StrategyLoggingLevel.Trading);
            }

            Log($"Basket {log.Number}: entering; " +
                string.Join(", ", log.Legs.Select(l => $"{l.Side} {l.Slot.Key} ref {l.EntryRef} " +
                    (!l.Sent ? "WAITING for quote" : $"{(l.Side == Side.Buy ? "ask" : "bid")} {Fmt(l.TouchAtSend, "G10")}") +
                    (l.OrderFailed ? $" FAILED ({l.FailNote})" : ""))) + ".", StrategyLoggingLevel.Trading);
        }

        // Send entries for held-back legs whose quote is now good; drop them after the deadline.
        private void JoinWaitingLegs(DateTime nowUtc, DateTime nowEt)
        {
            BasketLog log = _current;
            DateTime deadlineEt = log.EntryEt.AddMinutes(LateJoinMinutes);
            foreach (Leg leg in log.Legs.Where(l => !l.Sent && !l.Dropped))
            {
                if (nowEt >= deadlineEt)
                {
                    leg.Dropped = true;
                    string why = QuoteProblem(leg.Slot, nowUtc);
                    log.AddDetail($"LEG_DROPPED: {leg.Slot.Key} never passed the quote check ({why})");
                    Log($"Basket {log.Number}: LEG_DROPPED - {leg.Slot.Key} quote still not good at {deadlineEt:HH:mm:ss} ({why}); " +
                        "basket continues without it.", StrategyLoggingLevel.Error);
                    continue;
                }
                if (QuoteProblem(leg.Slot, nowUtc).Length > 0) continue;
                leg.Late = true;
                PlaceEntry(leg, log.Number, nowUtc);
                log.AddDetail($"{leg.Slot.Key} joined late at {nowEt:HH:mm:ss}");
                Log($"Basket {log.Number}: {leg.Slot.Key} quote now good; joining late - {leg.Side} at market " +
                    $"({leg.TouchSource} {Fmt(leg.TouchAtSend, "G10")}){(leg.OrderFailed ? $" FAILED ({leg.FailNote})" : "")}.",
                    StrategyLoggingLevel.Trading);
            }
        }

        // A late leg that was refused or never filled is dropped instead of ending the basket.
        private void CheckLateLegs(DateTime nowUtc)
        {
            BasketLog log = _current;
            foreach (Leg leg in log.Legs.Where(l => l.Late && l.Active && !l.Settled && !l.Filled(QtyPerLeg)))
            {
                string problem = null;
                if (leg.OrderFailed) problem = $"order failed: {leg.FailNote}";
                else if (leg.EntryQty <= 0)
                {
                    Order order = Core.Instance.Orders.FirstOrDefault(o => o.Id == leg.EntryOrderId);
                    if (order != null && (order.Status == OrderStatus.Refused || order.Status == OrderStatus.Cancelled))
                        problem = $"order {order.Status}";
                }
                if (problem == null && nowUtc >= leg.SentUtc.AddMinutes(EntryFillTimeoutMinutes))
                {
                    problem = $"unfilled after {EntryFillTimeoutMinutes} min";
                    Order order = Core.Instance.Orders.FirstOrDefault(o => o.Id == leg.EntryOrderId);
                    if (order != null && IsWorking(order)) Core.Instance.CancelOrder((IOrder)order);
                }
                if (problem == null) continue;
                if (leg.EntryQty > 0)
                {
                    log.AddDetail($"{leg.Slot.Key} late entry partly filled ({leg.EntryQty}/{QtyPerLeg}): {problem}");
                    Log($"Basket {log.Number}: {leg.Slot.Key} late entry partly filled ({leg.EntryQty}/{QtyPerLeg}): {problem}; " +
                        "keeping the filled part.", StrategyLoggingLevel.Error);
                    leg.Settled = true; // don't re-check this leg
                    continue;
                }
                leg.Dropped = true;
                log.AddDetail($"LEG_DROPPED: {leg.Slot.Key} late entry {problem}");
                Log($"Basket {log.Number}: LEG_DROPPED - {leg.Slot.Key} late entry {problem}; basket continues without it.",
                    StrategyLoggingLevel.Error);
            }
        }

        private void PlaceEntry(Leg leg, int basketNumber, DateTime nowUtc)
        {
            leg.Sent = true;
            leg.SentUtc = nowUtc;
            Symbol sym = leg.Slot.Symbol;
            var p = new PlaceOrderRequestParameters
            {
                Symbol = sym,
                Account = CurrentAccount,
                Side = leg.Side,
                Quantity = QtyPerLeg,
                TimeInForce = TimeInForce.Day,
                Comment = $"CM_B{basketNumber}_{leg.Slot.Key}"
            };
            // Market order. Record the ask (buy) / bid (sell) it was sent against, for the log only;
            // the pre-send check has already confirmed this quote is fresh.
            leg.TouchAtSend = leg.Side == Side.Buy ? leg.Slot.QuoteAsk : leg.Slot.QuoteBid;
            leg.TouchSource = leg.Side == Side.Buy ? "ask" : "bid";
            p.OrderTypeId = OrderType.Market;

            TradingOperationResult result = Core.Instance.PlaceOrder(p);
            if (result.Status != TradingOperationResultStatus.Success)
            {
                leg.OrderFailed = true;
                leg.FailNote = result.Message ?? "order refused";
                return;
            }
            leg.EntryOrderId = result.OrderId;
        }

        private void ManageEntering(DateTime nowUtc, DateTime nowEt)
        {
            BasketLog log = _current;
            JoinWaitingLegs(nowUtc, nowEt);
            CheckLateLegs(nowUtc);

            // Initial (on-time) legs: any failure ends the basket.
            foreach (Leg leg in log.Legs.Where(l => l.Sent && !l.Late))
            {
                if (leg.OrderFailed)
                {
                    BeginExit("NO_BASKET", $"{leg.Slot.Key} entry order failed: {leg.FailNote}", nowUtc, nowEt);
                    return;
                }
                if (leg.EntryQty <= 0 && !string.IsNullOrEmpty(leg.EntryOrderId))
                {
                    Order order = Core.Instance.Orders.FirstOrDefault(o => o.Id == leg.EntryOrderId);
                    if (order != null && (order.Status == OrderStatus.Refused || order.Status == OrderStatus.Cancelled))
                    {
                        BeginExit("NO_BASKET", $"{leg.Slot.Key} entry order {order.Status}", nowUtc, nowEt);
                        return;
                    }
                }
            }

            // Every sent leg filled (or settled) and at least one in: the basket is open. Legs still
            // waiting for a quote keep trying to join from ManageInBasket.
            List<Leg> active = log.Legs.Where(l => l.Active).ToList();
            if (active.Count > 0 && active.All(l => l.Filled(QtyPerLeg) || l.Settled))
            {
                _state = BasketState.InBasket;
                log.FilledEt = nowEt;
                _lastMinuteLoggedEt = TruncateMinute(nowEt);
                string waitingNow = string.Join(",", log.Legs.Where(l => !l.Sent && !l.Dropped).Select(l => l.Slot.Key));
                Log($"Basket {log.Number}: IN_BASKET; fills " +
                    string.Join(", ", active.Select(l => $"{l.Side} {l.Slot.Key} {l.EntryFill} (ref {l.EntryRef} {l.SlippageTicks:F1}t, {l.TouchSource} {Fmt(l.TouchAtSend, "G10")} {Fmt(l.TouchSlippageTicks, "F1")}t)")) +
                    (waitingNow.Length > 0 ? $"; still waiting to join: {waitingNow}" : "") + ".",
                    StrategyLoggingLevel.Trading);
                return;
            }

            // Nothing sent and nothing left that could join: no basket.
            if (active.Count == 0 && log.Legs.All(l => l.Dropped))
            {
                BeginExit("NO_BASKET", "no leg passed the quote check before the late-join deadline", nowUtc, nowEt);
                return;
            }

            Leg slow = log.Legs.FirstOrDefault(l => l.Sent && !l.Late && !l.Filled(QtyPerLeg)
                                                    && nowUtc >= l.SentUtc.AddMinutes(EntryFillTimeoutMinutes));
            if (slow != null)
            {
                string unfilled = string.Join(",", log.Legs.Where(l => l.Sent && !l.Late && !l.Filled(QtyPerLeg)).Select(l => l.Slot.Key));
                BeginExit("NO_BASKET", $"unfilled after {EntryFillTimeoutMinutes} min: {unfilled}", nowUtc, nowEt);
            }
        }

        // ------------------------------------------------------------------
        // In basket and exit
        // ------------------------------------------------------------------

        private void ManageInBasket(DateTime nowUtc, DateTime nowEt)
        {
            BasketLog log = _current;
            double pnl = BasketPnl(log);
            if (!double.IsNaN(pnl))
            {
                if (double.IsNaN(log.Mae) || pnl < log.Mae) log.Mae = pnl;
                if (double.IsNaN(log.Mfe) || pnl > log.Mfe) log.Mfe = pnl;
            }

            JoinWaitingLegs(nowUtc, nowEt);
            CheckLateLegs(nowUtc);

            // A leg closed outside the strategy leaves a partial basket: exit the rest.
            // Only legs that have a fill are expected to have a position.
            foreach (Leg leg in log.Legs.Where(l => l.EntryQty > 0))
            {
                if (HasPosition(leg.Slot)) { leg.MissingSinceUtc = DateTime.MinValue; continue; }
                if (leg.MissingSinceUtc == DateTime.MinValue) { leg.MissingSinceUtc = nowUtc; continue; }
                if ((nowUtc - leg.MissingSinceUtc).TotalSeconds >= 5)
                {
                    BeginExit("EXIT_FAILURE", $"{leg.Slot.Key} position closed outside the strategy", nowUtc, nowEt);
                    return;
                }
            }

            // Checked every second.
            if (!double.IsNaN(pnl))
            {
                if (_cumulativePnl + pnl <= -AccountStopLoss)
                {
                    _strategyKilled = true;
                    BeginExit("ACCOUNT_STOP", $"realized {_cumulativePnl:F2} + basket {pnl:F2} <= -{AccountStopLoss:F2}", nowUtc, nowEt);
                    return;
                }
                if (pnl <= -BasketStopLoss)
                {
                    BeginExit("STOP_LOSS", $"basket P&L {pnl:F2} <= -{BasketStopLoss:F2}", nowUtc, nowEt);
                    return;
                }
                if (pnl >= BasketTakeProfit)
                {
                    BeginExit("TAKE_PROFIT", $"basket P&L {pnl:F2} >= {BasketTakeProfit:F2}", nowUtc, nowEt);
                    return;
                }
            }

            DateTime minute = TruncateMinute(nowEt);
            if (minute == _lastMinuteLoggedEt) return;
            _lastMinuteLoggedEt = minute;
            Log($"Basket {log.Number} {minute:HH:mm}: P&L {Fmt(pnl)} (MAE {Fmt(log.Mae)}, MFE {Fmt(log.Mfe)}).",
                StrategyLoggingLevel.Info);
        }

        // Net of fees paid so far, at the last trade price of each leg.
        private static double BasketPnl(BasketLog log)
        {
            double total = 0;
            foreach (Leg leg in log.Legs)
            {
                if (leg.EntryQty <= 0) continue;
                double last = leg.Slot.Symbol?.Last ?? double.NaN;
                if (double.IsNaN(last) || last <= 0) return double.NaN;
                total += leg.Dir * (last - leg.EntryFill) * leg.Slot.DollarsPerPoint * leg.EntryQty - leg.Fees;
            }
            return total;
        }

        private void BeginExit(string reason, string detail, DateTime nowUtc, DateTime nowEt)
        {
            BasketLog log = _current;
            _exitReason = reason;
            _state = BasketState.Exiting;
            _exitStartUtc = nowUtc;
            _flatSinceUtc = DateTime.MinValue;
            _exitSlowLogged = false;
            _exitFailureLogged = reason == "EXIT_FAILURE";
            log.ExitEt = nowEt;
            log.AddDetail(detail);
            foreach (Leg leg in log.Legs)
            {
                leg.ExitPriceFallback = leg.Slot.Symbol?.Last ?? double.NaN;
                if (!leg.Sent && !leg.Dropped)
                {
                    leg.Dropped = true;
                    log.AddDetail($"{leg.Slot.Key} never joined (basket exited first)");
                }
            }

            Log($"Basket {log.Number}: {reason} - {detail}. Exiting all legs at market.", StrategyLoggingLevel.Trading);
            ResetCloseTracking(keepAccepted: false);
            CancelWorkingOrders(reason);
            CloseAllPositions(nowUtc, reason);
        }

        private void ManageExiting(DateTime nowUtc, DateTime nowEt)
        {
            BasketLog log = _current;
            if (AnyPositionsOrWorkingOrders())
            {
                _flatSinceUtc = DateTime.MinValue;
                if ((nowUtc - _lastCloseRequestUtc).TotalSeconds >= 5)
                {
                    CancelWorkingOrders(_exitReason + " retry");
                    CloseAllPositions(nowUtc, _exitReason + " retry");
                }
                if (!_exitSlowLogged && (nowUtc - _exitStartUtc).TotalSeconds >= 60)
                {
                    _exitSlowLogged = true;
                    Log($"Basket {log.Number}: still not flat 60s after {_exitReason}. Accepted closes are re-sent only after " +
                        $"{CloseAcceptedWaitSeconds}s with no fill; refused ones up to {CloseMaxRefusals} times. Check the platform.",
                        StrategyLoggingLevel.Error);
                }
                return;
            }
            if (_flatSinceUtc == DateTime.MinValue) _flatSinceUtc = nowUtc;

            // Give racing entry fills a moment to appear, then wait for the closing executions.
            bool fillsIn = log.Legs.All(l => l.ExitQty >= l.EntryQty - 1e-9);
            if ((fillsIn && (nowUtc - _exitStartUtc).TotalSeconds >= 3) || (nowUtc - _flatSinceUtc).TotalSeconds >= 10)
                FinishBasket();
        }

        private void FinishBasket()
        {
            BasketLog log = _current;
            double gross = 0, fees = 0;
            bool anyFilled = false, priceMissing = false;
            double brokerFees = 0, estimatedFees = 0;
            foreach (Leg leg in log.Legs)
            {
                // Exit execution not seen: still charge the estimated exit side.
                if (leg.ExitQty < leg.EntryQty - 1e-9)
                    leg.EstimatedFees += (leg.EntryQty - leg.ExitQty) * leg.Slot.FeePerSide;
                fees += leg.Fees;
                brokerFees += leg.BrokerFees;
                estimatedFees += leg.EstimatedFees;
                if (leg.EntryQty <= 0) continue;
                anyFilled = true;
                if (leg.ExitQty < leg.EntryQty - 1e-9) log.ExitPriceEstimated = true;
                double exit = leg.ExitFill;
                if (double.IsNaN(exit)) { priceMissing = true; continue; }
                gross += leg.Dir * (exit - leg.EntryFill) * leg.Slot.DollarsPerPoint * leg.EntryQty;
            }
            if (log.ExitPriceEstimated)
                log.AddDetail("exit execution not seen for every leg; last price at exit used where missing");

            log.BrokerFees = brokerFees;
            log.EstimatedFees = estimatedFees;
            if (!anyFilled) { log.Gross = 0; log.Fees = fees; log.Net = -fees; }
            else if (priceMissing) { log.Gross = double.NaN; log.Fees = fees; log.Net = double.NaN; }
            else { log.Gross = gross; log.Fees = fees; log.Net = gross - fees; }

            _state = BasketState.Idle;
            _current = null;
            if (anyFilled) _basketsTraded++;

            if (double.IsNaN(log.Net))
                Log($"Basket {log.Number}: net P&L unknown (missing exit price); daily and cumulative P&L NOT updated. " +
                    "Check the account.", StrategyLoggingLevel.Error);
            else
            {
                _dailyPnl += log.Net;
                _cumulativePnl += log.Net;
            }

            if (!_strategyKilled && _cumulativePnl <= -AccountStopLoss)
            {
                _strategyKilled = true;
                log.AddDetail($"ACCOUNT_STOP: cumulative {_cumulativePnl:F2} <= -{AccountStopLoss:F2}");
            }

            log.Outcome = _exitReason;
            WriteBasketRow(log);
            Log($"Basket {log.Number}: closed {_exitReason}, gross {Fmt(log.Gross)}, fees {Fmt(log.Fees)}, net {Fmt(log.Net)}. " +
                $"Day {_dailyPnl:F2}, cumulative {_cumulativePnl:F2}. -> IDLE", StrategyLoggingLevel.Trading);
            if (_strategyKilled)
                Log($"ACCOUNT_STOP: cumulative P&L {_cumulativePnl:F2} (limit -{AccountStopLoss:F2}). " +
                    "No further baskets until the strategy is restarted.", StrategyLoggingLevel.Trading);
        }

        // ------------------------------------------------------------------
        // Orders, positions, executions
        // ------------------------------------------------------------------

        private void OnTradeAdded(Trade trade)
        {
            // No _stopping check: closing fills during FlattenOnStop must still be recorded.
            if (trade == null || !IsOurAccount(trade.Account)) return;
            if (trade.Price <= 0 || trade.Quantity <= 0) return;
            lock (_sync)
            {
                if (_current == null) return;
                Leg leg = _current.Legs.FirstOrDefault(l => SameSymbol(l.Slot.Symbol, trade.Symbol));
                if (leg == null) return;

                double fee = PnlNumber(trade, "Fee");
                bool isEntry = (!string.IsNullOrEmpty(leg.EntryOrderId) && trade.OrderId == leg.EntryOrderId)
                               || ((_state == BasketState.Entering || (leg.Late && leg.Active))
                                   && trade.Side == leg.Side && leg.EntryQty < QtyPerLeg);
                if (isEntry)
                {
                    leg.EntryQty += trade.Quantity;
                    leg.EntryNotional += trade.Price * trade.Quantity;
                }
                else if (trade.Side != leg.Side && leg.ExitQty < leg.EntryQty)
                {
                    leg.ExitQty += trade.Quantity;
                    leg.ExitNotional += trade.Price * trade.Quantity;
                }
                else
                {
                    Log($"Unmatched execution on {leg.Slot.Key}: {trade.Side} {trade.Quantity} @ {trade.Price} (order {trade.OrderId}).",
                        StrategyLoggingLevel.Error);
                    return;
                }
                if (!double.IsNaN(fee)) leg.BrokerFees += Math.Abs(fee);
                leg.EstimatedFees += trade.Quantity * leg.Slot.FeePerSide;
            }
        }

        private bool AnyPositionsOrWorkingOrders()
        {
            return Core.Instance.Positions.Any(p => IsOurAccount(p.Account) && IsBasketSymbol(p.Symbol))
                || Core.Instance.Orders.Any(o => IsOurAccount(o.Account) && IsBasketSymbol(o.Symbol) && IsWorking(o));
        }

        private bool HasPosition(Slot slot)
        {
            return Core.Instance.Positions.Any(p => IsOurAccount(p.Account) && SameSymbol(p.Symbol, slot.Symbol));
        }

        private static bool IsWorking(Order o)
        {
            return o.Status == OrderStatus.Opened || o.Status == OrderStatus.PartiallyFilled;
        }

        private void CancelWorkingOrders(string reason)
        {
            foreach (Order order in Core.Instance.Orders
                         .Where(o => IsOurAccount(o.Account) && IsBasketSymbol(o.Symbol) && IsWorking(o)).ToList())
            {
                TradingOperationResult result = Core.Instance.CancelOrder((IOrder)order);
                if (result.Status != TradingOperationResultStatus.Success)
                    Log($"Cancel failed ({reason}): order {order.Id} {order.Symbol?.Name}: {result.Message}", StrategyLoggingLevel.Error);
            }
        }

        // Per-symbol close bookkeeping. A close is a market order on the opposite side, so
        // re-sending one while the platform's position view is stale could open a new position.
        private sealed class CloseTrack
        {
            public DateTime AcceptedUtc = DateTime.MinValue; // last close the broker accepted
            public int Refusals;                              // consecutive refusals
            public bool GaveUp;
        }

        private const int CloseAcceptedWaitSeconds = 60; // after an accepted close, wait this long for the fill
        private const int CloseMaxRefusals = 5;          // stop retrying a symbol after this many refusals in a row
        private readonly Dictionary<string, CloseTrack> _closeTracks = new Dictionary<string, CloseTrack>();

        private void ResetCloseTracking(bool keepAccepted)
        {
            if (!keepAccepted) { _closeTracks.Clear(); return; }
            foreach (CloseTrack t in _closeTracks.Values) { t.Refusals = 0; t.GaveUp = false; }
        }

        private void CloseAllPositions(DateTime nowUtc, string reason)
        {
            _lastCloseRequestUtc = nowUtc;
            List<Position> open = Core.Instance.Positions
                .Where(p => IsOurAccount(p.Account) && IsBasketSymbol(p.Symbol)).ToList();

            // Forget symbols that are no longer open.
            foreach (string key in _closeTracks.Keys.ToList())
                if (!open.Any(p => p.Symbol?.Name == key)) _closeTracks.Remove(key);

            foreach (Position p in open)
            {
                string key = p.Symbol?.Name ?? "?";
                if (!_closeTracks.TryGetValue(key, out CloseTrack track))
                    _closeTracks[key] = track = new CloseTrack();

                if (track.GaveUp) continue;
                if (track.AcceptedUtc != DateTime.MinValue)
                {
                    if ((nowUtc - track.AcceptedUtc).TotalSeconds < CloseAcceptedWaitSeconds) continue; // still waiting for the fill
                    Log($"Close for {key} was accepted {CloseAcceptedWaitSeconds}s ago but the position still shows open; sending again ({reason}).",
                        StrategyLoggingLevel.Error);
                }

                TradingOperationResult result = Core.Instance.ClosePosition(p);
                if (result.Status == TradingOperationResultStatus.Success)
                {
                    track.AcceptedUtc = nowUtc;
                    track.Refusals = 0;
                    Log($"Close requested ({reason}): {key} {p.Side} {p.Quantity}.", StrategyLoggingLevel.Trading);
                }
                else if (++track.Refusals >= CloseMaxRefusals)
                {
                    track.GaveUp = true;
                    _current?.AddDetail($"close retries stopped on {key} after {CloseMaxRefusals} refusals");
                    Log($"Close REFUSED {CloseMaxRefusals} times in a row on {key} ({result.Message}). No more retries for {key}. " +
                        "The position may already be flat at the broker and the platform's view stale - check the broker and flatten manually if needed.",
                        StrategyLoggingLevel.Error);
                }
                else
                {
                    Log($"Close refused ({reason}): {key} {p.Side} {p.Quantity}: {result.Message}. " +
                        $"Refusal {track.Refusals}/{CloseMaxRefusals}; will retry.", StrategyLoggingLevel.Error);
                }
            }
        }

        private bool IsOurAccount(Account account)
        {
            return account != null && CurrentAccount != null
                && (ReferenceEquals(account, CurrentAccount) || account.Id == CurrentAccount.Id);
        }

        private bool IsBasketSymbol(Symbol symbol)
        {
            return _slots.Any(s => SameSymbol(s.Symbol, symbol));
        }

        private static bool SameSymbol(Symbol a, Symbol b)
        {
            return a != null && b != null && (ReferenceEquals(a, b) || a.Id == b.Id);
        }

        // ------------------------------------------------------------------
        // Logs
        // ------------------------------------------------------------------

        private string BasketsHeader()
        {
            var cols = new List<string> { "date", "basket_number", "signal_candles", "entry_time", "exit_reason", "detail" };
            cols.AddRange(SymbolSpecs.Select(s => "two_candle_move_pct_" + s.Key));
            cols.AddRange(new[] { "long_legs", "short_legs" });
            cols.AddRange(SymbolSpecs.Select(s => "entry_ref_" + s.Key));
            cols.AddRange(SymbolSpecs.Select(s => "entry_fill_" + s.Key));
            cols.AddRange(SymbolSpecs.Select(s => "slippage_ticks_" + s.Key));
            cols.AddRange(SymbolSpecs.Select(s => "touch_at_send_" + s.Key));
            cols.AddRange(SymbolSpecs.Select(s => "touch_slippage_ticks_" + s.Key));
            cols.AddRange(new[] { "basket_filled_time", "exit_time" });
            cols.AddRange(SymbolSpecs.Select(s => "exit_price_" + s.Key));
            cols.AddRange(new[] { "exit_price_estimated", "gross_pnl", "fees", "net_pnl", "fee_source", "fees_broker", "fees_estimated" });
            cols.AddRange(SymbolSpecs.Select(s => "leg_pnl_" + s.Key));
            cols.AddRange(new[] { "mae", "mfe", "daily_pnl_after", "cumulative_pnl_after" });
            return string.Join(",", cols);
        }

        private const string DaysHeader = "date,baskets_started,baskets_traded,daily_net_pnl,cumulative_pnl,account_stop_hit,note";

        private void WriteBasketRow(BasketLog log)
        {
            Leg LegOf(string key) => log.Legs.FirstOrDefault(l => l.Slot.Key == key);
            double LegPnl(Leg l) => l == null || l.EntryQty <= 0 || double.IsNaN(l.ExitFill)
                ? double.NaN : l.Dir * (l.ExitFill - l.EntryFill) * l.Slot.DollarsPerPoint * l.EntryQty;

            var v = new List<string>
            {
                log.DateEt.ToString("yyyy-MM-dd", CultureInfo.InvariantCulture),
                log.Number.ToString(CultureInfo.InvariantCulture),
                log.FirstCandleEt.ToString("HH:mm", CultureInfo.InvariantCulture) + "-" +
                    log.FirstCandleEt.AddMinutes(1).ToString("HH:mm", CultureInfo.InvariantCulture),
                CsvTime(log.EntryEt),
                log.Outcome,
                CsvText(log.Detail)
            };
            foreach (var s in SymbolSpecs) v.Add(Csv(Get(log.MovePct, s.Key), "F4"));
            v.Add(string.Join(";", log.Longs));
            v.Add(string.Join(";", log.Shorts));
            foreach (var s in SymbolSpecs) v.Add(Csv(Get(log.EntryRef, s.Key), "G10"));
            foreach (var s in SymbolSpecs) v.Add(Csv(LegOf(s.Key)?.EntryFill, "G10"));
            foreach (var s in SymbolSpecs) v.Add(Csv(LegOf(s.Key)?.SlippageTicks, "F1"));
            foreach (var s in SymbolSpecs) v.Add(Csv(LegOf(s.Key)?.TouchAtSend, "G10"));
            foreach (var s in SymbolSpecs) v.Add(Csv(LegOf(s.Key)?.TouchSlippageTicks, "F1"));
            v.Add(CsvTime(log.FilledEt));
            v.Add(CsvTime(log.ExitEt));
            foreach (var s in SymbolSpecs)
            {
                Leg l = LegOf(s.Key);
                v.Add(l == null || l.EntryQty <= 0 ? "" : Csv(l.ExitFill, "G10"));
            }
            v.Add(log.Legs.Any(l => l.EntryQty > 0) ? (log.ExitPriceEstimated ? "1" : "0") : "");
            v.Add(Csv(log.Gross));
            v.Add(Csv(log.Fees));
            v.Add(Csv(log.Net));
            v.Add(log.Legs.Count == 0 ? "" : (log.Legs[0].UseEstimatedFees ? "estimated" : "broker"));
            v.Add(Csv(log.BrokerFees));
            v.Add(Csv(log.EstimatedFees));
            foreach (var s in SymbolSpecs) v.Add(Csv(LegPnl(LegOf(s.Key))));
            v.Add(Csv(log.Mae));
            v.Add(Csv(log.Mfe));
            v.Add(Csv(_dailyPnl));
            v.Add(Csv(_cumulativePnl));
            AppendCsv(_basketsCsv, v);
        }

        private void WriteDayRow(string note)
        {
            _dayRowWritten = true;
            AppendCsv(_daysCsv, new List<string>
            {
                _dayEt.ToString("yyyy-MM-dd", CultureInfo.InvariantCulture),
                _basketsStarted.ToString(CultureInfo.InvariantCulture),
                _basketsTraded.ToString(CultureInfo.InvariantCulture),
                Csv(_dailyPnl), Csv(_cumulativePnl),
                _strategyKilled ? "1" : "0",
                CsvText(note)
            });
            Log($"Day {_dayEt:yyyy-MM-dd}: {_basketsStarted} baskets started, {_basketsTraded} traded, net {_dailyPnl:F2}, " +
                $"cumulative {_cumulativePnl:F2}.", StrategyLoggingLevel.Info);
        }

        private void AppendCsv(string path, List<string> values)
        {
            string row = string.Join(",", values);
            try
            {
                lock (_csvLock) File.AppendAllText(path, row + Environment.NewLine);
            }
            catch (Exception ex)
            {
                Log("CSV write failed: " + ex.Message + " | row: " + row, StrategyLoggingLevel.Error);
            }
        }

        // In-memory only: everything starts fresh each time the strategy starts.
        private void ResetSessionState()
        {
            _cumulativePnl = 0; _strategyKilled = false;
            _dayEt = DateTime.MinValue; _dailyPnl = 0; _dayRowWritten = false;
            _basketsStarted = 0; _basketsTraded = 0;
            _lastSignalCheckEt = DateTime.MinValue;
            _lastBlockReason = "";
            _blackoutLogged = false;
        }

        private static double Get(Dictionary<string, double> d, string key)
        {
            return d.TryGetValue(key, out double v) ? v : double.NaN;
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

        private static string CsvText(string text)
        {
            if (string.IsNullOrEmpty(text)) return "";
            return "\"" + text.Replace("\"", "\"\"") + "\"";
        }

        private static string CsvTime(DateTime value)
        {
            return value == DateTime.MinValue ? "" : value.ToString("yyyy-MM-dd HH:mm:ss", CultureInfo.InvariantCulture);
        }

        private static string Fmt(double value, string format = "F2")
        {
            return double.IsNaN(value) ? "n/a" : value.ToString(format, CultureInfo.InvariantCulture);
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
                WarnConnectionLost();
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
                WarnConnectionLost();
            }
            else if (connected && !_lastKnownConnected)
            {
                _lastKnownConnected = true;
                Log("Connection watchdog: connection restored.", StrategyLoggingLevel.Info);
                RebindAfterReconnect();
            }
        }

        private void WarnConnectionLost()
        {
            lock (_sync)
            {
                if (_state != BasketState.Idle)
                    Log($"Connection lost while {_state}; the strategy keeps managing the basket when data returns. " +
                        "Check the positions.", StrategyLoggingLevel.Error);
            }
        }

        private void RebindAfterReconnect()
        {
            lock (_sync)
            {
                if (_stopping || _rebindInProgress) return;
                _rebindInProgress = true;
                try
                {
                    foreach (Slot s in _slots)
                    {
                        s.Symbol.NewQuote -= OnNewQuote;
                        Symbol fresh = Core.GetSymbol(s.Symbol.CreateInfo());
                        if (fresh != null) s.Symbol = fresh;
                        else Log($"Reconnect: {s.Key} symbol not reacquired.", StrategyLoggingLevel.Error);
                        s.Symbol.NewQuote += OnNewQuote;
                        s.QuoteTimeUtc = DateTime.MinValue;   // wait for a fresh quote after reconnect
                    }
                    string accountId = CurrentAccount?.Id;
                    if (!string.IsNullOrEmpty(accountId))
                    {
                        Account account = Core.Instance.Accounts.FirstOrDefault(a => a.Id == accountId);
                        if (account != null) CurrentAccount = account;
                        else Log("Reconnect: account not reacquired.", StrategyLoggingLevel.Error);
                    }
                    Core.Instance.TradeAdded -= OnTradeAdded;
                    Core.Instance.TradeAdded += OnTradeAdded;
                    if (!LoadHistories())
                        Log("Reconnect: bar reload failed; signals may use stale bars.", StrategyLoggingLevel.Error);
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

        // ------------------------------------------------------------------
        // Time
        // ------------------------------------------------------------------

        private static readonly TimeZoneInfo Eastern =
            TimeZoneInfo.FindSystemTimeZoneById("Eastern Standard Time");

        private static DateTime ToEastern(DateTime utc)
        {
            DateTime normalized = utc.Kind == DateTimeKind.Utc ? utc
                : utc.Kind == DateTimeKind.Unspecified ? DateTime.SpecifyKind(utc, DateTimeKind.Utc)
                : utc.ToUniversalTime();
            return TimeZoneInfo.ConvertTimeFromUtc(normalized, Eastern);
        }

        private static DateTime TruncateMinute(DateTime t)
        {
            return new DateTime(t.Year, t.Month, t.Day, t.Hour, t.Minute, 0, t.Kind);
        }
    }
}
