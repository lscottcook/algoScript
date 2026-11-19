using System;
using System.Collections.Generic;
using System.Diagnostics.Metrics;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using TradingPlatform.BusinessLayer;

namespace QuickBasketJoin
{
    /// <summary>
    /// Manual futures basket: MES, MNQ, MGC, MCL, MHG. Pick Buy / Sell / Off for each symbol, then
    /// click Start: one basket opens right away at market, QtyPerLeg contracts per leg.
    ///
    /// Legs whose bid/ask is fresh and spread normal are sent immediately; any other leg waits and
    /// joins when its quote is good, up to 5 minutes after start, else it is dropped. An on-time leg
    /// unfilled after 5 minutes flattens the basket; a late leg that fails is just dropped.
    ///
    /// Exits, checked every second: basket stop loss (P&L at or below -stop x quantity, once 5 minutes
    /// have passed since start, CAP_EXIT), basket take profit (P&L at or above +target x quantity,
    /// TP_EXIT), a leg closed by hand (MANUAL_CLOSE: the remaining legs are closed),
    /// or stopping the strategy (STOPPED: everything is flattened). One basket per start; afterwards
    /// the strategy sits idle until it is stopped and started again.
    ///
    /// Log: Downloads\QuickBasket_baskets.csv (one row per basket).
    /// </summary>
    public class QuickBasketJoin : Strategy, ICurrentAccount
    {
        private const string DirOff = "Off", DirBuy = "Buy", DirSell = "Sell";

        [InputParameter("Account", 1)]
        public Account CurrentAccount { get; set; }

        [InputParameter("MES symbol (front month)", 2)]
        public Symbol MesSymbol { get; set; }

        [InputParameter("MES direction", 3, variants: new object[] { DirOff, DirOff, DirBuy, DirBuy, DirSell, DirSell })]
        public string MesDirection = DirOff;

        [InputParameter("MNQ symbol (front month)", 4)]
        public Symbol MnqSymbol { get; set; }

        [InputParameter("MNQ direction", 5, variants: new object[] { DirOff, DirOff, DirBuy, DirBuy, DirSell, DirSell })]
        public string MnqDirection = DirOff;

        [InputParameter("MGC symbol (front month)", 6)]
        public Symbol MgcSymbol { get; set; }

        [InputParameter("MGC direction", 7, variants: new object[] { DirOff, DirOff, DirBuy, DirBuy, DirSell, DirSell })]
        public string MgcDirection = DirOff;

        [InputParameter("MCL symbol (front month)", 8)]
        public Symbol MclSymbol { get; set; }

        [InputParameter("MCL direction", 9, variants: new object[] { DirOff, DirOff, DirBuy, DirBuy, DirSell, DirSell })]
        public string MclDirection = DirOff;

        [InputParameter("MHG symbol (front month)", 10)]
        public Symbol MhgSymbol { get; set; }

        [InputParameter("MHG direction", 11, variants: new object[] { DirOff, DirOff, DirBuy, DirBuy, DirSell, DirSell })]
        public string MhgDirection = DirOff;

        // Contracts per leg, same for every symbol in the basket. Stop loss and take profit scale with it.
        [InputParameter("Quantity per symbol", 12, 1, 100, 1, 0)]
        public int QtyPerLeg = 1;

        // Basket P&L limits, per contract ($). Multiplied by quantity. 0 = off.
        [InputParameter("Basket stop loss per contract ($, 0 = off)", 13, 0, 100000, 1, 2)]
        public double StopLossPerContract = 250.00;

        [InputParameter("Basket take profit per contract ($, 0 = off)", 14, 0, 100000, 1, 2)]
        public double TakeProfitPerContract = 250.00;

        // Fees: per side, per contract, all-in. Defaults are the AMP Futures estimate.
        // On = P&L, stop and target use these; off = use the fee the broker reports on each fill.
        // Both are logged either way (fees_broker / fees_estimated).
        [InputParameter("Use estimated fees below (off = broker-reported fees)", 15)]
        public bool UseFeeEstimates = true;

        [InputParameter("MES fee per side ($)", 16, 0, 100, 0.01, 2)]
        public double FeeMes = 0.60;

        [InputParameter("MNQ fee per side ($)", 17, 0, 100, 0.01, 2)]
        public double FeeMnq = 0.60;

        [InputParameter("MGC fee per side ($)", 18, 0, 100, 0.01, 2)]
        public double FeeMgc = 0.85;

        [InputParameter("MCL fee per side ($)", 19, 0, 100, 0.01, 2)]
        public double FeeMcl = 0.75;

        [InputParameter("MHG fee per side ($)", 20, 0, 100, 0.01, 2)]
        public double FeeMhg = 0.80;

        [InputParameter("Starting Balance", 21)]
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

        private double MaxLossPerBasket => StopLossPerContract * QtyPerLeg;
        private double TakeProfitPerBasket => TakeProfitPerContract * QtyPerLeg;
        private const int CapActiveAfterMinutes = 5;

        // Pre-send check, per leg: the bid/ask must have updated within QuoteMaxAgeSeconds and the
        // spread must be at most MaxSpreadTicks. Legs that pass are sent at entry; a leg that fails
        // waits and joins the basket as soon as its quote passes, up to LateJoinMinutes after entry;
        // after that it is dropped and the basket runs without it.
        private const int QuoteMaxAgeSeconds = 15;
        private const double MaxSpreadTicks = 5;
        private const int EntryFillTimeoutMinutes = 5;
        private const int LateJoinMinutes = 5;

        // After Start, wait up to this long for every leg's first bid/ask before sending the entry.
        // Legs still without a good quote then join late (see LateJoinMinutes).
        private const int StartQuoteWaitSeconds = 10;

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
            public Side Side;
            // Live bid/ask from NewQuote; QuoteTimeUtc = when it last arrived (MinValue = none yet).
            public double QuoteBid = double.NaN, QuoteAsk = double.NaN;
            public DateTime QuoteTimeUtc = DateTime.MinValue;
        }

        private sealed class Leg
        {
            public Slot Slot;
            public Side Side;
            public int Dir;
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
        }

        private sealed class BasketLog
        {
            public DateTime StartEt;
            public string Outcome = "";
            public string Detail = "";
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

        private enum BasketState { WaitingForQuotes, Entering, InBasket, Exiting, Done }

        // ------------------------------------------------------------------
        // State
        // ------------------------------------------------------------------

        private readonly object _sync = new object();
        private readonly object _csvLock = new object();
        private readonly List<Slot> _slots = new List<Slot>();
        private bool _stopping;
        private bool _ready;

        private BasketState _state = BasketState.Done;
        private BasketLog _current;
        private DateTime _startUtc, _enterStartUtc, _exitStartUtc, _lastCloseRequestUtc = DateTime.MinValue, _flatSinceUtc;
        private DateTime _lastMinuteEvaluatedEt = DateTime.MinValue;
        private string _exitReason = "";
        private bool _exitSlowLogged;

        private string _basketsCsv;
        private System.Timers.Timer _timer;
        private System.Timers.Timer _connectionWatchdog;
        private bool _lastKnownConnected = true;
        private bool _rebindInProgress;
        private readonly Dictionary<Connection, EventHandler<ConnectionStateChangedEventArgs>>
            _connectionHandlers = new Dictionary<Connection, EventHandler<ConnectionStateChangedEventArgs>>();

        public QuickBasketJoin()
        {
            Name = "QuickBasketJoin";
            Description = "Manual basket: choose Buy / Sell / Off for MES/MNQ/MGC/MCL/MHG, Start opens every leg at market. " +
                          "Basket stop loss and take profit (x quantity); close by hand or stop the strategy to flatten.";
        }

        // ------------------------------------------------------------------
        // Lifecycle
        // ------------------------------------------------------------------

        protected override void OnRun()
        {
            _stopping = false;
            _ready = false;
            _slots.Clear();
            _state = BasketState.Done;
            _current = null;

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

            Symbol[] chosen = { MesSymbol, MnqSymbol, MgcSymbol, MclSymbol, MhgSymbol };
            string[] directions = { MesDirection, MnqDirection, MgcDirection, MclDirection, MhgDirection };
            double[] fees = { FeeMes, FeeMnq, FeeMgc, FeeMcl, FeeMhg };
            for (int i = 0; i < SymbolSpecs.Length; i++)
            {
                string dir = directions[i] ?? DirOff;
                if (dir == DirOff) continue;
                if (dir != DirBuy && dir != DirSell)
                {
                    Log($"{SymbolSpecs[i].Key}: unknown direction '{dir}'.", StrategyLoggingLevel.Error);
                    return;
                }
                if (chosen[i] == null)
                {
                    Log($"{SymbolSpecs[i].Key} is set to {dir} but no symbol is selected.", StrategyLoggingLevel.Error);
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
                    FeePerSide = Math.Max(0, fees[i]),
                    Symbol = symbol,
                    TickSize = symbol.TickSize,
                    Side = dir == DirBuy ? Side.Buy : Side.Sell
                });
            }
            if (_slots.Count == 0)
            {
                Log("Every direction is Off: set at least one symbol to Buy or Sell.", StrategyLoggingLevel.Error);
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
                Log($"{s.Key} = {s.Symbol.Name} {s.Side.ToString().ToUpperInvariant()}, tick {s.TickSize}, ${s.DollarsPerPoint}/point " +
                    $"(${s.DollarsPerPoint * s.TickSize:F2}/tick), expires {expiry}." +
                    $" Fee ${s.FeePerSide:F2}/side." +
                    (tickOk ? "" : $" WARNING: spec tick is {s.SpecTick}; check the symbol."),
                    tickOk ? StrategyLoggingLevel.Info : StrategyLoggingLevel.Error);
            }

            // Pre-entry checks, before any order is sent.
            if (!Core.Instance.Connections.All.Any(c => c.State == ConnectionState.Connected))
            {
                Log("Not connected: no basket opened.", StrategyLoggingLevel.Error);
                return;
            }
            if (AnyPositionsOrWorkingOrders())
            {
                Log("A position or working order already exists on a basket symbol in this account: no basket opened. " +
                    "Flatten those symbols and start again.", StrategyLoggingLevel.Error);
                return;
            }

            string downloads = Path.Combine(Environment.GetFolderPath(Environment.SpecialFolder.UserProfile), "Downloads");
            _basketsCsv = Path.Combine(downloads, "QuickBasket_baskets.csv");
            try { EnsureHeader(_basketsCsv, BasketsHeader()); }
            catch (Exception ex) { Log("CSV setup failed: " + ex.Message, StrategyLoggingLevel.Error); }

            foreach (Slot s in _slots)
            {
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

            lock (_sync)
            {
                _startUtc = DateTime.UtcNow;
                _current = new BasketLog { StartEt = ToEastern(_startUtc) };
                foreach (Slot s in _slots)
                {
                    _current.Legs.Add(new Leg
                    {
                        Slot = s,
                        Side = s.Side,
                        Dir = s.Side == Side.Buy ? 1 : -1,
                        UseEstimatedFees = UseFeeEstimates
                    });
                }
                _state = BasketState.WaitingForQuotes;
            }

            _ready = true;
            _timer = new System.Timers.Timer(1000) { AutoReset = true };
            _timer.Elapsed += (s, e) => OnTimer();
            _timer.Start();

            Log("QuickBasketJoin started: " +
                string.Join(", ", _slots.Select(s => $"{s.Side.ToString().ToUpperInvariant()} {s.Key}")) +
                $", {QtyPerLeg} per leg, entry MARKET. Pre-send check: bid/ask under {QuoteMaxAgeSeconds}s old and spread <= {MaxSpreadTicks} ticks; " +
                $"late join up to {LateJoinMinutes} min, fill timeout {EntryFillTimeoutMinutes} min. " +
                $"Stop loss {(MaxLossPerBasket > 0 ? $"-${MaxLossPerBasket:F2} (after {CapActiveAfterMinutes} min)" : "off")}, " +
                $"take profit {(TakeProfitPerBasket > 0 ? $"+${TakeProfitPerBasket:F2}" : "off")}, checked every second." +
                $"P&L uses {(UseFeeEstimates ? "ESTIMATED fees (inputs)" : "BROKER-reported fees")}. Log: {_basketsCsv}.",
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
            if (_ready) FlattenOnStop();
            _ready = false;

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

            Log("QuickBasketJoin stopped.", StrategyLoggingLevel.Info);
        }

        // On stop: cancel working orders and close every position on the basket symbols in this
        // account, wait up to StopFlattenWaitSeconds for the closes and their fills, then log the
        // open basket (exit reason STOPPED).
        private const int StopFlattenWaitSeconds = 5;

        private void FlattenOnStop()
        {
            DateTime nowUtc = DateTime.UtcNow;
            lock (_sync)
            {
                // Stopping is a deliberate user action: allow symbols that hit the refusal limit one
                // more try, but keep waiting on closes the broker already accepted.
                ResetCloseTracking(keepAccepted: true);
                if (_state == BasketState.WaitingForQuotes)
                {
                    // Nothing was sent yet.
                    BeginExit("STOPPED", "strategy stopped before any order was sent", nowUtc, ToEastern(nowUtc));
                }
                else if (_state == BasketState.Entering || _state == BasketState.InBasket)
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
                if (_current != null && _state == BasketState.Exiting)
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

        // Subscribed only so the trade feed stays on and Symbol.Last (used for basket P&L) keeps updating.
        private void OnNewLast(Symbol symbol, Last last) { }

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
            switch (_state)
            {
                case BasketState.WaitingForQuotes: TryOpenBasket(nowUtc, nowEt); break;
                case BasketState.Entering: ManageEntering(nowUtc, nowEt); break;
                case BasketState.InBasket: ManageInBasket(nowUtc, nowEt); break;
                case BasketState.Exiting: ManageExiting(nowUtc, nowEt); break;
            }
        }

        // ------------------------------------------------------------------
        // Entry
        // ------------------------------------------------------------------

        // Sends the entry once every leg has a good quote, or StartQuoteWaitSeconds after Start,
        // whichever comes first. Legs without a good quote by then join late.
        private void TryOpenBasket(DateTime nowUtc, DateTime nowEt)
        {
            BasketLog log = _current;
            bool allGood = log.Legs.All(l => QuoteProblem(l.Slot, nowUtc).Length == 0);
            if (!allGood && (nowUtc - _startUtc).TotalSeconds < StartQuoteWaitSeconds) return;

            _state = BasketState.Entering;
            _enterStartUtc = nowUtc;

            var waiting = new List<string>();
            foreach (Leg leg in log.Legs)
            {
                string problem = QuoteProblem(leg.Slot, nowUtc);
                if (problem.Length == 0) PlaceEntry(leg, nowUtc);
                else waiting.Add(problem);
            }
            if (waiting.Count > 0)
            {
                log.AddDetail("waiting to join: " + string.Join("; ", waiting));
                Log($"{waiting.Count} leg(s) held back by the quote check, will join when the quote is good " +
                    $"(until {ToEastern(_enterStartUtc.AddMinutes(LateJoinMinutes)):HH\\:mm\\:ss}): {string.Join("; ", waiting)}.",
                    StrategyLoggingLevel.Trading);
            }

            Log("Entering basket: " +
                string.Join(", ", log.Legs.Select(l => $"{l.Side} {l.Slot.Key} " +
                    (!l.Sent ? "WAITING for quote" : $"{l.TouchSource} {Fmt(l.TouchAtSend, "G10")}") +
                    (l.OrderFailed ? $" FAILED ({l.FailNote})" : ""))) + ".", StrategyLoggingLevel.Trading);
        }

        // Send entries for held-back legs whose quote is now good; drop them after the deadline.
        private void JoinWaitingLegs(DateTime nowUtc, DateTime nowEt)
        {
            BasketLog log = _current;
            DateTime deadlineUtc = _enterStartUtc.AddMinutes(LateJoinMinutes);
            foreach (Leg leg in log.Legs.Where(l => !l.Sent && !l.Dropped))
            {
                if (nowUtc >= deadlineUtc)
                {
                    leg.Dropped = true;
                    string why = QuoteProblem(leg.Slot, nowUtc);
                    log.AddDetail($"LEG_DROPPED: {leg.Slot.Key} never passed the quote check ({why})");
                    Log($"LEG_DROPPED - {leg.Slot.Key} quote still not good after {LateJoinMinutes} min ({why}); " +
                        "basket continues without it.", StrategyLoggingLevel.Error);
                    continue;
                }
                if (QuoteProblem(leg.Slot, nowUtc).Length > 0) continue;
                leg.Late = true;
                PlaceEntry(leg, nowUtc);
                log.AddDetail($"{leg.Slot.Key} joined late at {nowEt:HH:mm:ss}");
                Log($"{leg.Slot.Key} quote now good; joining late - {leg.Side} at market " +
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
                    Log($"{leg.Slot.Key} late entry partly filled ({leg.EntryQty}/{QtyPerLeg}): {problem}; " +
                        "keeping the filled part.", StrategyLoggingLevel.Error);
                    leg.Settled = true; // don't re-check this leg
                    continue;
                }
                leg.Dropped = true;
                log.AddDetail($"LEG_DROPPED: {leg.Slot.Key} late entry {problem}");
                Log($"LEG_DROPPED - {leg.Slot.Key} late entry {problem}; basket continues without it.",
                    StrategyLoggingLevel.Error);
            }
        }

        private void PlaceEntry(Leg leg, DateTime nowUtc)
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
                Comment = $"QBASKET_{leg.Slot.Key}"
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
                _lastMinuteEvaluatedEt = TruncateMinute(nowEt);
                string waitingNow = string.Join(",", log.Legs.Where(l => !l.Sent && !l.Dropped).Select(l => l.Slot.Key));
                Log("IN_BASKET; fills " +
                    string.Join(", ", active.Select(l => $"{l.Side} {l.Slot.Key} {l.EntryFill} ({l.TouchSource} {Fmt(l.TouchAtSend, "G10")} {Fmt(l.TouchSlippageTicks, "F1")}t)")) +
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

            // A leg closed by hand: close the rest of the basket.
            // Only legs that have a fill are expected to have a position.
            foreach (Leg leg in log.Legs.Where(l => l.EntryQty > 0))
            {
                if (HasPosition(leg.Slot)) { leg.MissingSinceUtc = DateTime.MinValue; continue; }
                if (leg.MissingSinceUtc == DateTime.MinValue) { leg.MissingSinceUtc = nowUtc; continue; }
                if ((nowUtc - leg.MissingSinceUtc).TotalSeconds >= 5)
                {
                    BeginExit("MANUAL_CLOSE", $"{leg.Slot.Key} position closed outside the strategy", nowUtc, nowEt);
                    return;
                }
            }

            // Stop loss and take profit: evaluated every second (each timer tick).
            bool capActive = nowUtc >= _enterStartUtc.AddMinutes(CapActiveAfterMinutes);
            if (MaxLossPerBasket > 0 && capActive && !double.IsNaN(pnl) && pnl <= -MaxLossPerBasket)
            {
                BeginExit("CAP_EXIT", $"basket P&L {pnl:F2} <= -{MaxLossPerBasket:F2}", nowUtc, nowEt);
                return;
            }
            if (TakeProfitPerBasket > 0 && !double.IsNaN(pnl) && pnl >= TakeProfitPerBasket)
            {
                BeginExit("TP_EXIT", $"basket P&L {pnl:F2} >= +{TakeProfitPerBasket:F2}", nowUtc, nowEt);
                return;
            }

            // P&L status line, once per minute.
            DateTime minute = TruncateMinute(nowEt);
            if (minute == _lastMinuteEvaluatedEt) return;
            _lastMinuteEvaluatedEt = minute;
            Log($"{minute:HH:mm}: basket P&L {Fmt(pnl)} (MAE {Fmt(log.Mae)}, MFE {Fmt(log.Mfe)}).",
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

            Log($"{reason} - {detail}. Exiting all legs at market.", StrategyLoggingLevel.Trading);
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
                    Log($"Still not flat 60s after {_exitReason}. Accepted closes are re-sent only after " +
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

            _state = BasketState.Done;
            _current = null;

            log.Outcome = _exitReason;
            WriteBasketRow(log);
            if (double.IsNaN(log.Net))
                Log("Net P&L unknown (missing exit price). Check the account.", StrategyLoggingLevel.Error);
            Log($"Basket closed {_exitReason}: gross {Fmt(log.Gross)}, fees {Fmt(log.Fees)}, net {Fmt(log.Net)}. " +
                "Stop and start the strategy to open another basket.", StrategyLoggingLevel.Trading);
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
        // Log
        // ------------------------------------------------------------------

        private static string BasketsHeader()
        {
            var cols = new List<string> { "date", "start_time", "exit_reason", "detail" };
            cols.AddRange(SymbolSpecs.Select(s => "direction_" + s.Key));
            cols.AddRange(SymbolSpecs.Select(s => "entry_fill_" + s.Key));
            cols.AddRange(SymbolSpecs.Select(s => "touch_at_send_" + s.Key));
            cols.AddRange(SymbolSpecs.Select(s => "touch_slippage_ticks_" + s.Key));
            cols.AddRange(new[] { "quantity", "stop_loss", "take_profit", "basket_filled_time", "exit_time" });
            cols.AddRange(SymbolSpecs.Select(s => "exit_price_" + s.Key));
            cols.AddRange(new[] { "exit_price_estimated", "gross_pnl", "fees", "net_pnl", "fee_source", "fees_broker", "fees_estimated" });
            cols.AddRange(SymbolSpecs.Select(s => "leg_pnl_" + s.Key));
            cols.AddRange(new[] { "mae", "mfe" });
            return string.Join(",", cols);
        }

        private void WriteBasketRow(BasketLog log)
        {
            Leg LegOf(string key) => log.Legs.FirstOrDefault(l => l.Slot.Key == key);
            double LegPnl(Leg l) => l == null || l.EntryQty <= 0 || double.IsNaN(l.ExitFill)
                ? double.NaN : l.Dir * (l.ExitFill - l.EntryFill) * l.Slot.DollarsPerPoint * l.EntryQty;

            var v = new List<string>
            {
                log.StartEt.ToString("yyyy-MM-dd", CultureInfo.InvariantCulture),
                log.StartEt.ToString("HH:mm:ss", CultureInfo.InvariantCulture),
                log.Outcome,
                CsvText(log.Detail)
            };
            foreach (var s in SymbolSpecs) v.Add(LegOf(s.Key)?.Side.ToString() ?? "");
            foreach (var s in SymbolSpecs) v.Add(Csv(LegOf(s.Key)?.EntryFill, "G10"));
            foreach (var s in SymbolSpecs) v.Add(Csv(LegOf(s.Key)?.TouchAtSend, "G10"));
            foreach (var s in SymbolSpecs) v.Add(Csv(LegOf(s.Key)?.TouchSlippageTicks, "F1"));
            v.Add(QtyPerLeg.ToString(CultureInfo.InvariantCulture));
            v.Add(MaxLossPerBasket > 0 ? Csv(-MaxLossPerBasket) : "");
            v.Add(TakeProfitPerBasket > 0 ? Csv(TakeProfitPerBasket) : "");
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
            AppendCsv(_basketsCsv, v);
        }

        private void AppendCsv(string path, List<string> values)
        {
            if (string.IsNullOrEmpty(path)) return;
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
                WarnIfBasketOpen();
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
                WarnIfBasketOpen();
            }
            else if (connected && !_lastKnownConnected)
            {
                _lastKnownConnected = true;
                Log("Connection watchdog: connection restored.", StrategyLoggingLevel.Info);
                RebindAfterReconnect();
            }
        }

        private void WarnIfBasketOpen()
        {
            lock (_sync)
            {
                if (_state != BasketState.Done)
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
                        s.Symbol.NewLast -= OnNewLast;
                        s.Symbol.NewQuote -= OnNewQuote;
                        Symbol fresh = Core.GetSymbol(s.Symbol.CreateInfo());
                        if (fresh != null) s.Symbol = fresh;
                        else Log($"Reconnect: {s.Key} symbol not reacquired.", StrategyLoggingLevel.Error);
                        s.Symbol.NewLast += OnNewLast;
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
