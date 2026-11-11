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
    /// Intraday futures basket: MES, MNQ, MGC, MCL, MHG, one basket at a time, 1 contract per leg
    ///
    /// Three attempts per day (ET). For each attempt the 15 one-minute bars before entry are
    /// ranked by return; long the top 3, short the bottom 2 (top 2 / bottom 2 if MHG is thin and
    /// removed). Skipped if the top-to-bottom spread is under 0.10%. All legs are entered
    /// together at market, only if every leg's bid/ask is fresh and its spread normal (else
    /// NO_BASKET with no orders sent); any leg unfilled after 5 minutes flattens the basket. Exits: the attempt's exit time
    /// (TIME_EXIT), or basket P&L at or below -$250 at a 1-minute close once 5 minutes have
    /// passed since entry time (CAP_EXIT). Daily -$500 and cumulative -$1000 kill switches.
    /// Flat by 15:30 ET, always.
    ///
    /// Logs: Downloads\Basket_attempts.csv (one row per attempt), Basket_days.csv (one row per
    /// trading day the strategy runs through). Nothing is saved between runs: daily and
    /// cumulative P&L and the kill switches start at zero each time the strategy starts.
    /// </summary>
    public class strategyTesting : Strategy, ICurrentAccount
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


        // Fees: per side, per contract, all-in. Defaults are the AMP Futures estimate.
        // On = P&L, cap and limits use these; off = use the fee the broker reports on each fill.
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


        [InputParameter("Starting Balance", 18)]
        public double StartingBalance { get; set; }

        // ------------------------------------------------------------------
        // Constants (spec section 1)
        // ------------------------------------------------------------------

        private const int QtyPerLeg = 1;

        private static readonly (string Key, double DollarsPerPoint, double SpecTick)[] SymbolSpecs =
        {
            ("MES", 5.00, 0.25),
            ("MNQ", 2.00, 0.25),
            ("MGC", 10.00, 0.10),
            ("MCL", 100.00, 0.01),
            ("MHG", 2500.00, 0.0005),
        };

        private sealed class AttemptSpec
        {
            public int Number;
            public TimeSpan RankStart, Entry, Exit;
        }

        private static readonly AttemptSpec[] Attempts =
        {
            new AttemptSpec { Number = 1, RankStart = new TimeSpan(9, 15, 0),  Entry = new TimeSpan(9, 30, 0),  Exit = new TimeSpan(10, 14, 0) },
            new AttemptSpec { Number = 2, RankStart = new TimeSpan(10, 45, 0), Entry = new TimeSpan(11, 00, 0), Exit = new TimeSpan(11, 59, 0) },
            new AttemptSpec { Number = 3, RankStart = new TimeSpan(14, 45, 0), Entry = new TimeSpan(15, 0, 0),  Exit = new TimeSpan(15, 30, 0) },
        };

        private static readonly TimeSpan FlatBy = new TimeSpan(15, 30, 0);

        private const double NoSignalMinSpreadPct = 0.10;
        private const int MhgMinTicksInWindow = 20;

        private const double MaxLossPerBasket = 250.00;
        private const int CapActiveAfterMinutes = 5;
        private const double MaxLossPerDay = 500.00;
        private const double MaxCumulativeDrawdown = 1000.00;

        // Pre-send check, per leg: the bid/ask must have updated within QuoteMaxAgeSeconds and the
        // spread must be at most MaxSpreadTicks. If any leg fails, the attempt is NO_BASKET and no
        // orders are sent. Fills are not checked afterwards (no open-then-close).
        private const int QuoteMaxAgeSeconds = 15;
        private const double MaxSpreadTicks = 5;
        private const int EntryFillTimeoutMinutes = 5;

        // Wait this long after the entry minute starts so the last trades of the previous
        // minute are in the bars. An attempt is skipped if the strategy wasn't running within
        // EntryLateLimit of its entry time.
        private static readonly TimeSpan EntryGrace = TimeSpan.FromSeconds(2);
        private static readonly TimeSpan EntryLateLimit = TimeSpan.FromSeconds(60);

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
            // Trade prints counted from NewLast, keyed by ET minute start.
            public readonly Dictionary<DateTime, int> TradesPerMinuteEt = new Dictionary<DateTime, int>();
            public DateTime CountingSinceEt = DateTime.MaxValue;
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
            // Fill vs the bid/ask at send: what the safety limit checks. Positive = worse.
            public double TouchSlippageTicks => double.IsNaN(EntryFill) || double.IsNaN(TouchAtSend) || Slot.TickSize <= 0
                ? double.NaN : (EntryFill - TouchAtSend) * Dir / Slot.TickSize;
            // Fill vs entry_ref (last-minute close): logged only. Positive = worse.
            public double SlippageTicks => double.IsNaN(EntryFill) || Slot.TickSize <= 0
                ? double.NaN : (EntryFill - EntryRef) * Dir / Slot.TickSize;
        }

        private sealed class AttemptLog
        {
            public DateTime DateEt;
            public AttemptSpec Spec;
            public string Outcome = "";
            public string Detail = "";
            public readonly Dictionary<string, double> ReturnPct = new Dictionary<string, double>();
            public readonly Dictionary<string, double> EntryRef = new Dictionary<string, double>();
            public int MhgTicks = -1;
            public string MhgTickSource = "";
            public bool MhgRemoved;
            public readonly List<string> Longs = new List<string>();
            public readonly List<string> Shorts = new List<string>();
            public double SpreadPct = double.NaN;
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
        private AttemptLog _current;
        private DateTime _enterStartUtc, _exitStartUtc, _lastCloseRequestUtc = DateTime.MinValue, _flatSinceUtc;
        private DateTime _lastMinuteEvaluatedEt = DateTime.MinValue;
        private string _exitReason = "";
        private bool _exitSlowLogged, _exitFailureLogged;

        // Daily / cumulative (this run only; reset on every start)
        private DateTime _dayEt = DateTime.MinValue;
        private double _dailyPnl, _cumulativePnl;
        private bool _dayKilled, _strategyKilled, _dayRowWritten, _flatByLogged;
        private readonly bool[] _attemptHandled = new bool[3];
        private readonly bool[] _rankingLogged = new bool[3];
        private int _attemptsLogged, _basketsTraded;

        private string _attemptsCsv, _daysCsv;
        private System.Timers.Timer _timer;
        private System.Timers.Timer _connectionWatchdog;
        private bool _lastKnownConnected = true;
        private bool _rebindInProgress;
        private readonly Dictionary<Connection, EventHandler<ConnectionStateChangedEventArgs>>
            _connectionHandlers = new Dictionary<Connection, EventHandler<ConnectionStateChangedEventArgs>>();

        public strategyTesting()
        {
            Name = "strategyTesting";
            Description = "Intraday basket: rank MES/MNQ/MGC/MCL/MHG over 15 minutes, long top 3 / short bottom 2, " +
                          "time exit or -$250 cap, daily and cumulative kill switches, flat by 15:30 ET.";
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
            _attemptsCsv = Path.Combine(downloads, "Basket_attempts.csv");
            _daysCsv = Path.Combine(downloads, "Basket_days.csv");
            try
            {
                EnsureHeader(_attemptsCsv, AttemptsHeader());
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

            DateTime nowEt = ToEastern(DateTime.UtcNow);
            foreach (Slot s in _slots)
            {
                s.CountingSinceEt = TruncateMinute(nowEt).AddMinutes(1);
                s.Symbol.NewLast -= OnNewLast;
                s.Symbol.NewLast += OnNewLast;
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

            // Attempts run purely by entry time: any attempt whose entry is still ahead runs. One whose
            // entry has already passed is skipped for this session (logged here, no CSV row).
            lock (_sync)
            {
                DateTime startEt = ToEastern(DateTime.UtcNow);
                RollDayIfNeeded(startEt);
                for (int i = 0; i < Attempts.Length; i++)
                {
                    bool passed = startEt.TimeOfDay > Attempts[i].Entry + EntryLateLimit;
                    _attemptHandled[i] = _rankingLogged[i] = passed;
                    Log($"Attempt {Attempts[i].Number} (entry {Attempts[i].Entry:hh\\:mm}): " +
                        (passed ? "entry time already passed; not run this session." : "scheduled."),
                        StrategyLoggingLevel.Info);
                }
            }

            _ready = true;
            _timer = new System.Timers.Timer(1000) { AutoReset = true };
            _timer.Elapsed += (s, e) => OnTimer();
            _timer.Start();

            Log("Basket strategy started. Attempts (ET): " +
                string.Join("; ", Attempts.Select(a => $"#{a.Number} rank {a.RankStart:hh\\:mm}-{a.Entry.Subtract(TimeSpan.FromMinutes(1)):hh\\:mm}, " +
                                                       $"entry {a.Entry:hh\\:mm}, exit {a.Exit:hh\\:mm}")) +
                $". Flat by {FlatBy:hh\\:mm}. Entry MARKET, " +
                $"{QtyPerLeg} per leg, fill timeout {EntryFillTimeoutMinutes} min, pre-send check: bid/ask under {QuoteMaxAgeSeconds}s old and spread <= {MaxSpreadTicks} ticks. " +
                $"Cap -${MaxLossPerBasket:F2} after {CapActiveAfterMinutes} min, day -${MaxLossPerDay:F2}, cumulative -${MaxCumulativeDrawdown:F2}. " +
                $"P&L uses {(UseFeeEstimates ? "ESTIMATED fees (inputs)" : "BROKER-reported fees")}.",
                StrategyLoggingLevel.Info);
            Log($"State: day {_dayEt:yyyy-MM-dd} P&L {_dailyPnl:F2}{(_dayKilled ? " (DAY_KILLED)" : "")}, " +
                $"cumulative {_cumulativePnl:F2}{(_strategyKilled ? " (STRATEGY_KILLED)" : "")}. Logs: {_attemptsCsv}, {_daysCsv}.",
                _strategyKilled ? StrategyLoggingLevel.Error : StrategyLoggingLevel.Info);
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
            if (_ready) FlattenOnStop();

            foreach (Slot s in _slots)
            {
                if (s.Symbol == null) continue;
                s.Symbol.NewLast -= OnNewLast;
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
            Log("Basket strategy stopped.", StrategyLoggingLevel.Info);
        }

        // On stop: cancel working orders and close every position on the basket symbols in this
        // account, wait up to StopFlattenWaitSeconds for the closes and their fills, then log the
        // open attempt (exit reason STOPPED) and add its P&L to the daily / cumulative totals.
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
                    s.History = s.Symbol.GetHistory(Period.MIN1, HistoryType.Last, DateTime.UtcNow.AddDays(-1));
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
            try
            {
                HistoricalData fresh = s.Symbol.GetHistory(Period.MIN1, HistoryType.Last, DateTime.UtcNow.AddDays(-1));
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

        private void OnNewLast(Symbol symbol, Last last)
        {
            if (_stopping || last == null) return;
            lock (_sync)
            {
                Slot slot = _slots.FirstOrDefault(s => SameSymbol(s.Symbol, symbol));
                if (slot == null) return;
                DateTime t = last.Time == default ? DateTime.UtcNow : last.Time;
                DateTime minute = TruncateMinute(ToEastern(t));
                slot.TradesPerMinuteEt.TryGetValue(minute, out int n);
                slot.TradesPerMinuteEt[minute] = n + 1;
                if (slot.TradesPerMinuteEt.Count > 600)
                {
                    DateTime cutoff = minute.AddHours(-6);
                    foreach (DateTime k in slot.TradesPerMinuteEt.Keys.Where(k => k < cutoff).ToList())
                        slot.TradesPerMinuteEt.Remove(k);
                }
            }
        }

        // Window endpoints, both from bars inside [firstMinuteEt, lastMinuteEt]; nothing is carried
        // in from before the window. First = close of the first-minute bar, or of the earliest bar in
        // the window if that one is missing. Last = close of the last-minute bar only; if that bar is
        // missing, Last is NaN and the symbol has no valid return (it is also the entry reference).
        // Also returns the trade count over the window.
        private (double First, DateTime FirstT, double Last, int Ticks, string TickSource) WindowStats(Slot slot, DateTime firstMinuteEt, DateTime lastMinuteEt)
        {
            double first = double.NaN, lastClose = double.NaN;
            DateTime firstT = DateTime.MaxValue;
            long barTicks = 0;
            HistoricalData h = slot.History;
            if (h != null)
            {
                for (int k = 0; k < h.Count; k++)
                {
                    if (!(h[k, SeekOriginHistory.Begin] is HistoryItemBar bar)) continue;
                    DateTime tEt = TruncateMinute(ToEastern(bar.TimeLeft));
                    if (tEt < firstMinuteEt || tEt > lastMinuteEt) continue;
                    if (tEt < firstT) { first = bar.Close; firstT = tEt; }
                    if (tEt == lastMinuteEt) lastClose = bar.Close;
                    barTicks += (long)bar.Ticks;
                }
            }

            // Prefer our own trade count when we were listening for the whole window.
            if (slot.CountingSinceEt <= firstMinuteEt)
            {
                int counted = slot.TradesPerMinuteEt.Where(kv => kv.Key >= firstMinuteEt && kv.Key <= lastMinuteEt).Sum(kv => kv.Value);
                return (first, firstT, lastClose, counted, "trades");
            }
            return (first, firstT, lastClose, (int)Math.Min(int.MaxValue, barTicks), "bars");
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

            switch (_state)
            {
                case BasketState.Entering: ManageEntering(nowUtc, nowEt); break;
                case BasketState.InBasket: ManageInBasket(nowUtc, nowEt); break;
                case BasketState.Exiting: ManageExiting(nowUtc, nowEt); break;
            }

            EnforceFlatBy(nowUtc, nowEt);
            ScheduleAttempts(nowUtc, nowEt);
            WriteDayRowIfDone(nowEt);
        }

        private void RollDayIfNeeded(DateTime nowEt)
        {
            DateTime today = nowEt.Date;
            if (today == _dayEt) return;
            if (_dayEt != DateTime.MinValue && IsTradingDay(_dayEt) && !_dayRowWritten)
                WriteDayRow("strategy was not running at 15:30 this day");
            _dayEt = today;
            _dailyPnl = 0;
            _dayKilled = false;
            _dayRowWritten = false;
            _flatByLogged = false;
            _attemptsLogged = 0;
            _basketsTraded = 0;
            for (int i = 0; i < _attemptHandled.Length; i++) { _attemptHandled[i] = false; _rankingLogged[i] = false; }
            if (IsTradingDay(today))
                Log($"New trading day {today:yyyy-MM-dd}. Cumulative P&L {_cumulativePnl:F2}" +
                    (_strategyKilled ? " - STRATEGY_KILLED, no attempts until reset." : "."), StrategyLoggingLevel.Info);
        }

        private void ScheduleAttempts(DateTime nowUtc, DateTime nowEt)
        {
            if (!IsTradingDay(_dayEt)) return;
            TimeSpan tod = nowEt.TimeOfDay;
            for (int i = 0; i < Attempts.Length; i++)
            {
                if (_attemptHandled[i]) continue;
                AttemptSpec a = Attempts[i];
                if (tod < a.RankStart) continue;
                if (!_rankingLogged[i] && tod < a.Entry)
                {
                    _rankingLogged[i] = true;
                    Log($"Attempt {a.Number}: IDLE -> RANKING, window {a.RankStart:hh\\:mm}-{a.Entry.Subtract(TimeSpan.FromMinutes(1)):hh\\:mm}.",
                        StrategyLoggingLevel.Info);
                }
                if (tod < a.Entry + EntryGrace) continue;

                _attemptHandled[i] = true;
                var log = new AttemptLog { DateEt = _dayEt, Spec = a };
                if (tod > a.Entry + EntryLateLimit)
                    FinishAttempt(log, "SKIPPED", "strategy was not running at entry time");
                else if (_strategyKilled)
                    FinishAttempt(log, "STRATEGY_KILLED", $"cumulative P&L {_cumulativePnl:F2}");
                else if (_dayKilled)
                    FinishAttempt(log, "DAY_KILLED", $"daily P&L {_dailyPnl:F2}");
                else if (_state != BasketState.Idle)
                    FinishAttempt(log, "SKIPPED", $"previous basket still {_state}");
                else
                    RunAttempt(log, nowUtc);
            }
        }

        // ------------------------------------------------------------------
        // Ranking and entry
        // ------------------------------------------------------------------

        private void RunAttempt(AttemptLog log, DateTime nowUtc)
        {
            AttemptSpec a = log.Spec;
            DateTime firstMinuteEt = _dayEt + a.RankStart;
            DateTime lastMinuteEt = _dayEt + a.Entry - TimeSpan.FromMinutes(1);

            var returns = new Dictionary<Slot, double>();
            var missing = new List<string>();
            foreach (Slot s in _slots)
            {
                var st = WindowStats(s, firstMinuteEt, lastMinuteEt);
                if (double.IsNaN(st.Last))
                {
                    // Last-minute bar missing: reload once in case the history stopped updating.
                    bool reloaded = ReloadHistory(s);
                    if (reloaded) st = WindowStats(s, firstMinuteEt, lastMinuteEt);
                    string result = !reloaded ? "reload failed"
                        : double.IsNaN(st.Last) ? $"still no {lastMinuteEt:HH:mm} bar" : $"{lastMinuteEt:HH:mm} bar found";
                    log.AddDetail($"{s.Key} bars reloaded ({result})");
                    Log($"Attempt {a.Number}: {s.Key} had no {lastMinuteEt:HH:mm} bar; reloaded history - {result}.",
                        double.IsNaN(st.Last) ? StrategyLoggingLevel.Error : StrategyLoggingLevel.Info);
                }
                double ret = st.First > 0 && st.Last > 0 ? (st.Last / st.First - 1) * 100 : double.NaN;
                returns[s] = ret;
                log.ReturnPct[s.Key] = ret;
                log.EntryRef[s.Key] = st.Last;
                if (s.Key == "MHG") { log.MhgTicks = st.Ticks; log.MhgTickSource = st.TickSource; }
                if (double.IsNaN(st.Last))
                    missing.Add($"{s.Key} (no {lastMinuteEt:HH:mm} bar)");
                else if (double.IsNaN(st.First))
                    missing.Add($"{s.Key} (no bar in window)");
                else if (st.FirstT != firstMinuteEt)
                    log.AddDetail($"{s.Key} no {firstMinuteEt:HH:mm} bar; first price from {st.FirstT:HH:mm}");
            }

            List<Slot> candidates = _slots.ToList();
            Slot mhg = _slots.First(s => s.Key == "MHG");
            string mhgDrop = log.MhgTicks < MhgMinTicksInWindow
                ? $"{log.MhgTicks} ticks ({log.MhgTickSource}) < {MhgMinTicksInWindow}"
                : double.IsNaN(returns[mhg]) ? $"no valid return (missing {lastMinuteEt:HH:mm} bar)" : null;
            if (mhgDrop != null)
            {
                candidates.Remove(mhg);
                missing.RemoveAll(m => m.StartsWith("MHG", StringComparison.Ordinal));
                log.MhgRemoved = true;
                log.AddDetail("THIN_SYMBOL_SKIP: MHG " + mhgDrop);
                Log($"Attempt {a.Number}: THIN_SYMBOL_SKIP - MHG {mhgDrop}; basket is long 2 / short 2.",
                    StrategyLoggingLevel.Info);
            }
            string returnsText = string.Join(", ", _slots.Select(s => $"{s.Key} {Fmt(returns[s], "F3")}%"));

            if (missing.Count > 0)
            {
                FinishAttempt(log, "NO_DATA", "no valid return for " + string.Join("; ", missing) + "; returns " + returnsText);
                return;
            }

            List<Slot> ranked = candidates.OrderByDescending(s => returns[s]).ThenBy(s => s.Index).ToList();
            log.SpreadPct = returns[ranked.First()] - returns[ranked.Last()];
            int nLong = ranked.Count - 2;
            List<Slot> longs = ranked.Take(nLong).ToList();
            List<Slot> shorts = ranked.Skip(nLong).ToList();
            log.Longs.AddRange(longs.Select(s => s.Key));
            log.Shorts.AddRange(shorts.Select(s => s.Key));

            if (log.SpreadPct < NoSignalMinSpreadPct)
            {
                FinishAttempt(log, "NO_SIGNAL", $"spread {log.SpreadPct:F3}% < {NoSignalMinSpreadPct:F2}%; returns {returnsText}");
                return;
            }

            Log($"Attempt {a.Number}: ranked {returnsText}; spread {log.SpreadPct:F3}%. " +
                $"LONG {string.Join(",", log.Longs)} / SHORT {string.Join(",", log.Shorts)}.", StrategyLoggingLevel.Trading);

            // Pre-entry checks, before any order is sent. A failure here still uses the attempt.
            string block = "";
            if (CurrentAccount == null) block = "no account";
            else if (!Core.Instance.Connections.All.Any(c => c.State == ConnectionState.Connected)) block = "not connected";
            else if (AnyPositionsOrWorkingOrders()) block = "a position or working order already exists on a basket symbol";
            else
            {
                var problems = longs.Concat(shorts).Select(s => QuoteProblem(s, nowUtc)).Where(x => x.Length > 0).ToList();
                if (problems.Count > 0) block = "quote check failed: " + string.Join("; ", problems);
            }
            if (block.Length > 0)
            {
                FinishAttempt(log, "NO_BASKET", "not entered: " + block);
                return;
            }

            _current = log;
            _state = BasketState.Entering;
            _enterStartUtc = nowUtc;
            foreach (Slot s in longs.Concat(shorts))
            {
                bool isLong = longs.Contains(s);
                log.Legs.Add(new Leg
                {
                    Slot = s,
                    Side = isLong ? Side.Buy : Side.Sell,
                    Dir = isLong ? 1 : -1,
                    EntryRef = log.EntryRef[s.Key],
                    UseEstimatedFees = UseFeeEstimates
                });
            }

            foreach (Leg leg in log.Legs)
                PlaceEntry(leg, a.Number);

            Log($"Attempt {a.Number}: RANKING -> entering basket; " +
                string.Join(", ", log.Legs.Select(l => $"{l.Side} {l.Slot.Key} ref {l.EntryRef} " +
                    $"{(l.Side == Side.Buy ? "ask" : "bid")} {Fmt(l.TouchAtSend, "G10")}" +
                    (l.OrderFailed ? $" FAILED ({l.FailNote})" : ""))) + ".", StrategyLoggingLevel.Trading);
        }

        private void PlaceEntry(Leg leg, int attemptNumber)
        {
            Symbol sym = leg.Slot.Symbol;
            var p = new PlaceOrderRequestParameters
            {
                Symbol = sym,
                Account = CurrentAccount,
                Side = leg.Side,
                Quantity = QtyPerLeg,
                TimeInForce = TimeInForce.Day,
                Comment = $"BASKET_A{attemptNumber}_{leg.Slot.Key}"
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
            AttemptLog log = _current;
            foreach (Leg leg in log.Legs)
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

            if (log.Legs.All(l => l.EntryQty >= QtyPerLeg - 1e-9))
            {
                _state = BasketState.InBasket;
                log.FilledEt = nowEt;
                _lastMinuteEvaluatedEt = TruncateMinute(nowEt);
                Log($"Attempt {log.Spec.Number}: IN_BASKET; fills " +
                    string.Join(", ", log.Legs.Select(l => $"{l.Side} {l.Slot.Key} {l.EntryFill} (ref {l.EntryRef} {l.SlippageTicks:F1}t, {l.TouchSource} {Fmt(l.TouchAtSend, "G10")} {Fmt(l.TouchSlippageTicks, "F1")}t)")) + ".",
                    StrategyLoggingLevel.Trading);
                return;
            }

            if (nowUtc >= _enterStartUtc.AddMinutes(EntryFillTimeoutMinutes))
            {
                string unfilled = string.Join(",", log.Legs.Where(l => l.EntryQty < QtyPerLeg - 1e-9).Select(l => l.Slot.Key));
                BeginExit("NO_BASKET", $"unfilled after {EntryFillTimeoutMinutes} min: {unfilled}", nowUtc, nowEt);
            }
        }

        // ------------------------------------------------------------------
        // In basket and exit
        // ------------------------------------------------------------------

        private void ManageInBasket(DateTime nowUtc, DateTime nowEt)
        {
            AttemptLog log = _current;
            double pnl = BasketPnl(log);
            if (!double.IsNaN(pnl))
            {
                if (double.IsNaN(log.Mae) || pnl < log.Mae) log.Mae = pnl;
                if (double.IsNaN(log.Mfe) || pnl > log.Mfe) log.Mfe = pnl;
            }

            // A leg closed outside the strategy leaves a partial basket: exit the rest.
            foreach (Leg leg in log.Legs)
            {
                if (HasPosition(leg.Slot)) { leg.MissingSinceUtc = DateTime.MinValue; continue; }
                if (leg.MissingSinceUtc == DateTime.MinValue) { leg.MissingSinceUtc = nowUtc; continue; }
                if ((nowUtc - leg.MissingSinceUtc).TotalSeconds >= 5)
                {
                    BeginExit("EXIT_FAILURE", $"{leg.Slot.Key} position closed outside the strategy", nowUtc, nowEt);
                    return;
                }
            }

            DateTime minute = TruncateMinute(nowEt);
            if (minute == _lastMinuteEvaluatedEt) return;
            _lastMinuteEvaluatedEt = minute;

            // Evaluated at each 1-minute close.
            if (nowEt.TimeOfDay >= log.Spec.Exit)
            {
                BeginExit("TIME_EXIT", $"exit time {log.Spec.Exit:hh\\:mm}, basket P&L {Fmt(pnl)}", nowUtc, nowEt);
                return;
            }
            DateTime capActiveEt = log.DateEt + log.Spec.Entry + TimeSpan.FromMinutes(CapActiveAfterMinutes);
            if (nowEt >= capActiveEt && !double.IsNaN(pnl) && pnl <= -MaxLossPerBasket)
            {
                BeginExit("CAP_EXIT", $"basket P&L {pnl:F2} <= -{MaxLossPerBasket:F2}", nowUtc, nowEt);
                return;
            }
            Log($"Attempt {log.Spec.Number} {minute:HH:mm}: basket P&L {Fmt(pnl)} (MAE {Fmt(log.Mae)}, MFE {Fmt(log.Mfe)}).",
                StrategyLoggingLevel.Info);
        }

        // Net of fees paid so far, at the last trade price of each leg.
        private static double BasketPnl(AttemptLog log)
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
            AttemptLog log = _current;
            _exitReason = reason;
            _state = BasketState.Exiting;
            _exitStartUtc = nowUtc;
            _flatSinceUtc = DateTime.MinValue;
            _exitSlowLogged = false;
            _exitFailureLogged = reason == "EXIT_FAILURE";
            log.ExitEt = nowEt;
            log.AddDetail(detail);
            foreach (Leg leg in log.Legs)
                leg.ExitPriceFallback = leg.Slot.Symbol?.Last ?? double.NaN;

            Log($"Attempt {log.Spec.Number}: {reason} - {detail}. Exiting all legs at market.", StrategyLoggingLevel.Trading);
            ResetCloseTracking(keepAccepted: false);
            CancelWorkingOrders(reason);
            CloseAllPositions(nowUtc, reason);
        }

        private void ManageExiting(DateTime nowUtc, DateTime nowEt)
        {
            AttemptLog log = _current;
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
                    Log($"Attempt {log.Spec.Number}: still not flat 60s after {_exitReason}. Accepted closes are re-sent only after " +
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
            AttemptLog log = _current;
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
            if (_exitReason == "TIME_EXIT" || _exitReason == "CAP_EXIT") _basketsTraded++;

            if (double.IsNaN(log.Net))
                Log($"Attempt {log.Spec.Number}: net P&L unknown (missing exit price); daily and cumulative P&L NOT updated. " +
                    "Check the account.", StrategyLoggingLevel.Error);
            else
            {
                _dailyPnl += log.Net;
                _cumulativePnl += log.Net;
            }
            FinishAttempt(log, _exitReason, null);
            Log($"Attempt {log.Spec.Number}: closed {_exitReason}, gross {Fmt(log.Gross)}, fees {Fmt(log.Fees)}, net {Fmt(log.Net)}. " +
                $"Day {_dailyPnl:F2}, cumulative {_cumulativePnl:F2}. -> IDLE", StrategyLoggingLevel.Trading);

            if (!_dayKilled && _dailyPnl <= -MaxLossPerDay)
            {
                _dayKilled = true;
                Log($"DAY_KILLED: daily P&L {_dailyPnl:F2} <= -{MaxLossPerDay:F2}. No further attempts today.", StrategyLoggingLevel.Trading);
            }
            if (!_strategyKilled && _cumulativePnl <= -MaxCumulativeDrawdown)
            {
                _strategyKilled = true;
                Log($"STRATEGY_KILLED: cumulative P&L {_cumulativePnl:F2} <= -{MaxCumulativeDrawdown:F2}. " +
                    "No further attempts until the strategy is restarted.", StrategyLoggingLevel.Trading);
            }
        }

        // Never carry a position past 15:30.
        private void EnforceFlatBy(DateTime nowUtc, DateTime nowEt)
        {
            if (nowEt.TimeOfDay < FlatBy) return;
            if (_state == BasketState.InBasket || _state == BasketState.Entering)
            {
                BeginExit("EXIT_FAILURE", $"basket still {_state} at {FlatBy:hh\\:mm}", nowUtc, nowEt);
                return;
            }
            if (_state == BasketState.Exiting)
            {
                // Attempt 3's time exit fires at 15:30 itself, so give any exit 30s to complete
                // before calling it a failure. ManageExiting keeps retrying the close meanwhile.
                if (!_exitFailureLogged && (nowUtc - _exitStartUtc).TotalSeconds >= 30 && AnyPositionsOrWorkingOrders())
                {
                    _exitFailureLogged = true;
                    _current.AddDetail($"EXIT_FAILURE: legs still open after {FlatBy:hh\\:mm} (30s after {_exitReason})");
                    Log($"EXIT_FAILURE: legs still open after {FlatBy:hh\\:mm}, 30s after {_exitReason}; still flattening at market.",
                        StrategyLoggingLevel.Error);
                }
                return;
            }
            if (!AnyPositionsOrWorkingOrders()) return;
            if (!_flatByLogged)
            {
                _flatByLogged = true;
                Log($"EXIT_FAILURE: position or working order on a basket symbol at {FlatBy:hh\\:mm} with no basket open; flattening at market.",
                    StrategyLoggingLevel.Error);
            }
            if ((nowUtc - _lastCloseRequestUtc).TotalSeconds >= 5)
            {
                CancelWorkingOrders("flat-by");
                CloseAllPositions(nowUtc, "flat-by");
            }
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
                               || (_state == BasketState.Entering && trade.Side == leg.Side && leg.EntryQty < QtyPerLeg);
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

        private void FinishAttempt(AttemptLog log, string outcome, string detail)
        {
            log.Outcome = outcome;
            if (!string.IsNullOrEmpty(detail)) log.AddDetail(detail);
            _attemptsLogged++;
            if (outcome != "TIME_EXIT" && outcome != "CAP_EXIT" && outcome != "NO_BASKET" && outcome != "EXIT_FAILURE")
                Log($"Attempt {log.Spec.Number}: {outcome} - {log.Detail}. -> IDLE", StrategyLoggingLevel.Trading);
            WriteAttemptRow(log);
        }

        private string AttemptsHeader()
        {
            var cols = new List<string> { "date", "attempt_number", "entry_time", "exit_reason", "detail" };
            cols.AddRange(SymbolSpecs.Select(s => "return_pct_" + s.Key));
            cols.AddRange(new[] { "mhg_window_ticks", "mhg_removed", "long_legs", "short_legs", "ranking_spread_pct" });
            cols.AddRange(SymbolSpecs.Select(s => "entry_ref_" + s.Key));
            cols.AddRange(SymbolSpecs.Select(s => "entry_fill_" + s.Key));
            cols.AddRange(SymbolSpecs.Select(s => "slippage_ticks_" + s.Key));
            cols.AddRange(SymbolSpecs.Select(s => "touch_at_send_" + s.Key));
            cols.AddRange(SymbolSpecs.Select(s => "touch_slippage_ticks_" + s.Key));
            cols.AddRange(new[] { "basket_filled_time", "exit_time" });
            cols.AddRange(SymbolSpecs.Select(s => "exit_price_" + s.Key));
            cols.AddRange(new[] { "exit_price_estimated", "gross_pnl", "fees", "net_pnl", "fee_source", "fees_broker", "fees_estimated" });
            cols.AddRange(SymbolSpecs.Select(s => "leg_pnl_" + s.Key));
            cols.AddRange(new[] { "mnq_share_of_basket_pnl", "mae", "mfe", "daily_pnl_after", "cumulative_pnl_after" });
            return string.Join(",", cols);
        }

        private const string DaysHeader = "date,attempts_logged,baskets_traded,daily_net_pnl,cumulative_pnl,day_killed,strategy_killed,note";

        private void WriteAttemptRow(AttemptLog log)
        {
            Leg LegOf(string key) => log.Legs.FirstOrDefault(l => l.Slot.Key == key);
            double LegPnl(Leg l) => l == null || l.EntryQty <= 0 || double.IsNaN(l.ExitFill)
                ? double.NaN : l.Dir * (l.ExitFill - l.EntryFill) * l.Slot.DollarsPerPoint * l.EntryQty;

            var v = new List<string>
            {
                log.DateEt.ToString("yyyy-MM-dd", CultureInfo.InvariantCulture),
                log.Spec.Number.ToString(CultureInfo.InvariantCulture),
                (log.DateEt + log.Spec.Entry).ToString("HH:mm", CultureInfo.InvariantCulture),
                log.Outcome,
                CsvText(log.Detail)
            };
            foreach (var s in SymbolSpecs) v.Add(Csv(Get(log.ReturnPct, s.Key), "F4"));
            v.Add(log.MhgTicks < 0 ? "" : log.MhgTicks.ToString(CultureInfo.InvariantCulture));
            v.Add(log.MhgTicks < 0 ? "" : (log.MhgRemoved ? "1" : "0"));
            v.Add(string.Join(";", log.Longs));
            v.Add(string.Join(";", log.Shorts));
            v.Add(Csv(log.SpreadPct, "F4"));
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
            double mnq = LegPnl(LegOf("MNQ"));
            v.Add(!double.IsNaN(mnq) && !double.IsNaN(log.Gross) && Math.Abs(log.Gross) > 1e-9 ? Csv(mnq / log.Gross, "F3") : "");
            v.Add(Csv(log.Mae));
            v.Add(Csv(log.Mfe));
            v.Add(Csv(_dailyPnl));
            v.Add(Csv(_cumulativePnl));
            AppendCsv(_attemptsCsv, v);
        }

        private void WriteDayRowIfDone(DateTime nowEt)
        {
            if (_dayRowWritten || !IsTradingDay(_dayEt) || nowEt.Date != _dayEt) return;
            if (nowEt.TimeOfDay < FlatBy || _state != BasketState.Idle || !_attemptHandled.All(h => h)) return;
            WriteDayRow("");
        }

        private void WriteDayRow(string note)
        {
            _dayRowWritten = true;
            AppendCsv(_daysCsv, new List<string>
            {
                _dayEt.ToString("yyyy-MM-dd", CultureInfo.InvariantCulture),
                _attemptsLogged.ToString(CultureInfo.InvariantCulture),
                _basketsTraded.ToString(CultureInfo.InvariantCulture),
                Csv(_dailyPnl), Csv(_cumulativePnl),
                _dayKilled ? "1" : "0", _strategyKilled ? "1" : "0",
                CsvText(note)
            });
            Log($"Day {_dayEt:yyyy-MM-dd}: {_attemptsLogged} attempts, {_basketsTraded} baskets, net {_dailyPnl:F2}, " +
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
            _dayEt = DateTime.MinValue; _dailyPnl = 0; _dayKilled = false; _dayRowWritten = false;
            _attemptsLogged = 0; _basketsTraded = 0;
            for (int i = 0; i < _attemptHandled.Length; i++) { _attemptHandled[i] = false; _rankingLogged[i] = false; }
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
                MarkDataGap();
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
                MarkDataGap();
            }
            else if (connected && !_lastKnownConnected)
            {
                _lastKnownConnected = true;
                Log("Connection watchdog: connection restored.", StrategyLoggingLevel.Info);
                RebindAfterReconnect();
            }
        }

        // Our own trade counts have a hole now; fall back to bar tick counts until a full window passes.
        private void MarkDataGap()
        {
            lock (_sync)
            {
                foreach (Slot s in _slots) s.CountingSinceEt = DateTime.MaxValue;
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
                    DateTime nextMinuteEt = TruncateMinute(ToEastern(DateTime.UtcNow)).AddMinutes(1);
                    foreach (Slot s in _slots)
                    {
                        s.Symbol.NewLast -= OnNewLast;
                        s.Symbol.NewQuote -= OnNewQuote;
                        Symbol fresh = Core.GetSymbol(s.Symbol.CreateInfo());
                        if (fresh != null) s.Symbol = fresh;
                        else Log($"Reconnect: {s.Key} symbol not reacquired.", StrategyLoggingLevel.Error);
                        s.Symbol.NewLast += OnNewLast;
                        s.Symbol.NewQuote += OnNewQuote;
                        s.QuoteTimeUtc = DateTime.MinValue;   // wait for a fresh quote after reconnect
                        s.CountingSinceEt = nextMinuteEt;
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
                        Log("Reconnect: bar reload failed; ranking may use stale bars.", StrategyLoggingLevel.Error);
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

        private static bool IsTradingDay(DateTime dateEt)
        {
            return dateEt != DateTime.MinValue
                && dateEt.DayOfWeek != DayOfWeek.Saturday && dateEt.DayOfWeek != DayOfWeek.Sunday;
        }
    }
}
