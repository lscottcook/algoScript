using System;
using System.Collections;
using System.Collections.Generic;
//using System.Data;
using System.Diagnostics.Metrics;
using System.Drawing;
using System.IO;
using System.Linq;
using System.Security.Principal;
using System.Threading;
using System.Threading.Tasks;
using System.Xml.Linq;
using TradingPlatform.BusinessLayer;

namespace algoTrading
{
    public class algoTrading : Strategy, ICurrentAccount, ICurrentSymbol
    {
        // ======================================================
        // FRAMEWORK INPUTS (required)
        // ======================================================

        [InputParameter("Symbol", 0)]
        public Symbol CurrentSymbol { get; set; }

        [InputParameter("Account", 1)]
        public Account CurrentAccount { get; set; }

        [InputParameter("Quantity", 2)]
        public int Quantity = 1;

        [InputParameter("Use Trading Hours", 8)]
        public bool UseTradingHours = true;

        [InputParameter("Use Account Limit", 9)]
        public bool UseAccountLimit = true;

        [InputParameter("Account Take Profit ($)", 10)]
        public double AccountTakeProfit = 100.0;

        [InputParameter("Account Stop Loss ($)", 11)]
        public double AccountStopLoss = -100.0;

        [InputParameter("Starting Balance", 12)]
        public double StartingBalance { get; set; }

        // ======================================================
        // STRATEGY-SPECIFIC INPUTS
        // ======================================================

        // Entry trigger: 9/20 EMA crossover on 30-second bars, traded WITH the
        // trend (fast crosses above slow -> buy; fast crosses below slow -> sell).
        // See EMAHelper for how the averages are calculated.

        private Period EmaBarPeriod;
        private int EmaFastPeriod = 9;
        private int EmaSlowPeriod = 20;

        // How long an unfilled crossover signal stays live before requiring a
        // fresh crossover -- prevents chasing a stale trend indefinitely on
        // repeated timeout/retry cycles. 0 = never expires.
        private int EmaSignalExpirySeconds = 300;

        // The take-profit / stop-loss offsets (in ticks) attached to every entry
        // order and held by the broker. These are the strategy's ONLY exit, and the
        // only numbers that reach the server -- the TargetTicks/StopTicks inputs
        // above are not used. Declared here so PlaceEntry, the log lines, and the
        // CSV's targetPrice/stopPrice columns can never disagree about the levels.
        private const int ServerTakeProfitTicks = 5;
        private const int ServerStopLossTicks = 4;

        // Resolved from the CURRENT user's profile rather than hardcoded, so the same
        // source file works unchanged on both machines:
        //     local -> C:\Users\Lisa\Downloads\algoTrading.csv
        //     VPS   -> C:\Users\Administrator\Downloads\algoTrading.csv
        // Hand-editing this line on the VPS after every pull was what left the working
        // tree dirty and made the next pull conflict. Nothing to change per machine now.
        private string CsvPath = Path.Combine(
            Environment.GetFolderPath(Environment.SpecialFolder.UserProfile),
            "Downloads", "algoTrading.csv");

        // ======================================================
        // FRAMEWORK FIELDS — quotes / market state
        // ======================================================

        private double _tickSize = 0;
        private double _bid = double.NaN, _ask = double.NaN;
        private double _lastMid = double.NaN;

        // Throttled diagnostic so a blocking gate is visible in the log
        private long _lastGateLogTs = 0;

        // Cached L1 quote (updated on each OnNewQuote)
        private volatile Quote _latestQuote = null;

        // Cached Level 2 / MBO data (updated on each OnNewLevel2)
        private volatile DOMQuote _latestDom = null;
        private volatile Level2Quote _latestMbo = null;

        private volatile List<Level2Item> _sortedBids = null;
        private volatile List<Level2Item> _sortedAsks = null;

        // How many depth levels to request from the aggregated DOM pull
        private const int DomLevelsToPull = 10;

        // One-shot latch so the "L2 feed connected" confirmation logs once per strategy instance
        private bool _loggedLevel2Connected = false;

        // ======================================================
        // FRAMEWORK FIELDS — entry signal
        // ======================================================

        // Set when entry signal fires; consumed when entry order is placed
        protected Side? _pendingSignalSide = null;
        protected DateTime _pendingSignalTime = DateTime.MinValue;

        // Direction of the most recent crossover, latched. Unlike _pendingSignalSide
        // -- which PlaceEntry consumes (sets to null) the instant an order goes out --
        // this is NOT cleared by order placement, expiry, or a position closing. It
        // tracks the crossover EVENT, so one crossover can arm exactly one entry.
        // Only the opposite crossover changes it. See UpdateEntrySignal.
        private Side? _lastCrossoverSide = null;

        // ======================================================
        // STRATEGY-SPECIFIC FIELDS — EMA crossover signal
        // ======================================================

        // How far back the bar history is requested from. Four hours of 30-second
        // bars is ~480 bars -- far more than the 20-bar slow EMA needs to warm up,
        // and still a light initial load.
        private readonly DateTime _emaStartPoint = Core.TimeUtils.DateTimeUtcNow.AddHours(-4);
        private HistoricalData _hdmEma;
        private EMAHelper _ema;


        // ======================================================
        // FIELDS — entry / signal latency
        // ======================================================

        private long _lastCloseTimestamp = 0;         // Stopwatch ticks — re-entry cooldown gate
        private long _lastUnmatchedLogTs = 0;          // Stopwatch ticks — throttles the unmatched-position warning

        // Bracket leg order ids for the CURRENTLY open position, captured while it
        // still exposes them. Used to identify its closing execution exactly.
        private string _tpOrderId, _slOrderId;
        // The entry order id of the currently open position, for the same reason.
        private string _entryOrderIdForPosition;

        // ======================================================
        // FIELDS — trades awaiting their closing execution
        // ======================================================
        // A closed trade is NOT written the instant the position disappears,
        // because at that moment the strategy does not yet know what the exit
        // filled at -- and the P&L is worthless without it.
        //
        // PositionRemoved captures everything only the strategy knows (MFE/MAE,
        // fill latency, the quotes at entry and exit) into a TradeRecord. The
        // closing execution supplies the exit price, and the row is written once
        // the two meet. See the REALIZED TRADE RESULT section for the P&L itself
        // and for the two approaches that failed before this one.
        private class TradeRecord
        {
            public string PositionId;
            public Side Side;
            public double EntryPrice;      // Position.OpenPrice -- fallback only
            public double Quantity;

            // Order ids are the only truly discriminating link between this trade
            // and its executions. PositionId is NOT: on this connection it is the
            // composite "HGZ6@COMEX@Paper200062", identical for every position on
            // the instrument, which is what let one execution be claimed by nine
            // different trades.
            public string EntryOrderId;
            public string TpOrderId;
            public string SlOrderId;
            public DateTime OpenTime;
            public DateTime CloseTime;
            public double Mfe, Mae;
            public double EntryBid, EntryAsk;
            public double ExitBid, ExitAsk;
            public double FillLatencySec;
            public System.Timers.Timer Fallback;
            public int Written;            // Interlocked flag — exactly one writer

            // Executions accumulate here; a leg can fill in pieces, so each side is
            // the quantity-weighted average of what actually traded.
            public double EntryQty, EntryNotional;
            public double ExitQty, ExitNotional;

            public double EntryFill => EntryQty > 0 ? EntryNotional / EntryQty : double.NaN;
            public double ExitPrice => ExitQty > 0 ? ExitNotional / ExitQty : double.NaN;
            public bool ExitComplete => ExitQty > 0 && ExitQty >= Quantity - 1e-9;

            // Which bracket leg filled, when the order id identified it outright.
            public string ExitLeg;
        }

        private readonly Dictionary<string, TradeRecord> _pendingTrades =
            new Dictionary<string, TradeRecord>();
        private readonly object _pendingTradesLock = new object();

        // How long to wait for the closing execution before writing the row with
        // an unknown P&L instead. A trade must never be lost just because an
        // execution failed to arrive -- an empty grossPnL column is a visible
        // gap, where a dropped row is not.
        private const int RealizedPnLTimeoutSeconds = 20;
        private long _signalTimestamp = 0;             // Stopwatch ticks at entry placement
        private DateTime _signalWallTime = DateTime.MinValue;
        private double _fillLatencySec = 0;

        private int EntryTimeoutSeconds = 200;
        private int ReentryCooldownSeconds = 1;

        // ======================================================
        // FIELDS — position / order management
        // ======================================================

        private Position _openPosition = null;
        private double _entryPrice = double.NaN;
        private bool _entrySent = false;
        private bool _hasOpenPosition = false;

        // Serializes every read/write of the position-tracking fields in this region
        // across the quote thread (OnNewQuote/ManageOpenPositions) and Quantower's own
        // event-dispatch thread (OnPositionAdded/OnPositionRemoved) -- without this,
        // two fills landing close together can both pass the "is a position already
        // open?" check before either sets it, and both get adopted into these SAME
        // shared fields, corrupting entry price/exit reason across trades. Mirrors
        // MeanReversion.cs's _positionLock, added there after exactly this failure
        // mode was confirmed live (an extreme burst produced two overlapping
        // positions and corrupted a trade's logged GrossPnL).
        private readonly object _positionLock = new object();

        private readonly HashSet<string> _myPositionIds = new HashSet<string>();

        private string _entryLimitOrderId = null;
        private System.Timers.Timer _entryLimitTimer;

        private bool _isStopping = false;

        // Per-position tracking (adverse-selection measurement)
        private DateTime _positionOpenTime = DateTime.MinValue;
        private double _positionHighWater = 0;         // MFE (ticks)
        private double _positionLowWater = 0;          // MAE (ticks)
        private double _entryBidAtFill = double.NaN, _entryAskAtFill = double.NaN;

        // ======================================================
        // FIELDS — connection / reconnect
        // ======================================================

        private readonly Dictionary<Connection, EventHandler<ConnectionStateChangedEventArgs>>
            _connectionHandlers = new Dictionary<Connection, EventHandler<ConnectionStateChangedEventArgs>>();
        private System.Timers.Timer _connectionWatchdog;
        private bool _lastKnownConnected = true;

        // ======================================================
        // EMA HELPER
        // ======================================================
        // Standard exponential moving average over bar closes, with the usual
        // smoothing constant k = 2 / (period + 1).
        //
        // An EMA has no natural starting point -- every value depends on the one
        // before it -- so it is seeded with a simple average of the oldest
        // `period` bars in the window and then run forward. WarmupMultiplier
        // extra periods of bars are fed in ahead of the bar actually being read,
        // so by the time the value at `shift` is produced the seed's weight has
        // decayed to a negligible fraction and the number matches what a
        // continuously running EMA would report.
        //
        // shift follows the HistoricalData convention: 0 is the bar currently
        // forming, 1 is the last CLOSED bar, 2 the one before it.
        private class EMAHelper
        {
            private readonly HistoricalData hdmInd;
            private readonly int fastPeriod;
            private readonly int slowPeriod;

            // Periods of extra history fed in before the value is read. At 5,
            // the seed retains (1-k)^(5*period) of its weight -- under 0.01% for
            // any period -- so the result is stable regardless of where the
            // loaded history happens to begin.
            private const int WarmupMultiplier = 5;

            public EMAHelper(HistoricalData hdmInd, int fastPeriod = 9, int slowPeriod = 20)
            {
                this.hdmInd = hdmInd;
                this.fastPeriod = fastPeriod;
                this.slowPeriod = slowPeriod;
            }

            public double Fast(int shift = 0) => CalculateEMA(fastPeriod, shift);

            public double Slow(int shift = 0) => CalculateEMA(slowPeriod, shift);

            private double CalculateEMA(int period, int shift = 0)
            {
                if (hdmInd == null || period < 1 || shift < 0)
                    return double.NaN;

                // Oldest bar to start from: the seed window plus the warmup tail,
                // clamped to whatever history is actually loaded.
                int oldest = shift + period * (WarmupMultiplier + 1) - 1;
                if (oldest >= hdmInd.Count)
                    oldest = hdmInd.Count - 1;

                // Not even enough bars for the seed itself.
                if (oldest < shift + period - 1)
                    return double.NaN;

                double seed = 0;
                for (int i = 0; i < period; i++)
                    seed += hdmInd.Close(oldest - i);
                double ema = seed / period;

                double k = 2.0 / (period + 1);

                // Walk forward in time -- indices count DOWN toward the present.
                for (int barIndex = oldest - period; barIndex >= shift; barIndex--)
                    ema = hdmInd.Close(barIndex) * k + ema * (1 - k);

                return ema;
            }
        }

        // ======================================================
        // FIELDS — CSV
        // ======================================================

        private string _tradeCsv = "";
        private readonly List<string> _tradeBuf = new List<string>();
        private readonly object _csvLock = new object();
        private System.Timers.Timer _flushTimer;



        // ======================================================
        // CONSTRUCTOR
        // ======================================================

        public algoTrading()
        {
            Name = "algoTrading";
            Description = "Generic strategy algoTrading with framework for rapid development.";
            EmaBarPeriod = Period.SECOND30;
        }

        // ======================================================
        // LIFECYCLE
        // ======================================================

        protected override void OnRun()
        {
            if (CurrentSymbol == null || CurrentAccount == null)
            {
                Log("❌ Symbol and Account must be set before running", StrategyLoggingLevel.Error);
                return;
            }

            this.CurrentSymbol = Core.GetSymbol(CurrentSymbol.CreateInfo());
            _tickSize = CurrentSymbol.TickSize;

            if (StartingBalance <= 0)
            {
                StartingBalance = CurrentAccount.Balance;
                Log($"│  StartingBalance captured from account: {StartingBalance:F2}", StrategyLoggingLevel.Info);
            }

            // Subscribe to data feeds
            CurrentSymbol.NewLast += OnNewTick;      // Real-time trade ticks; also drives the DOM pull
            CurrentSymbol.NewQuote += OnNewQuote;
            CurrentSymbol.NewLevel2 += OnNewLevel2;  // MBO order-level detail
            Log($"🔔 Subscribed to NewLast + NewLevel2 events for {CurrentSymbol.Name}", StrategyLoggingLevel.Info);
            Core.Instance.PositionAdded += OnPositionAdded;
            Core.Instance.PositionRemoved += OnPositionRemoved;
            Core.Instance.TradeAdded += OnTradeAdded;

            _hdmEma = CurrentSymbol.GetHistory(new HistoryRequestParameters
            {
                Symbol = CurrentSymbol,
                FromTime = _emaStartPoint,
                Aggregation = new HistoryAggregationTime(EmaBarPeriod, CurrentSymbol.HistoryType)
            });
            _ema = new EMAHelper(_hdmEma, EmaFastPeriod, EmaSlowPeriod);

            _tradeCsv = CsvPath;
            EnsureHeaders();

            // Start CSV flush timer
            _flushTimer = new System.Timers.Timer(5000) { AutoReset = true };
            _flushTimer.Elapsed += (s, e) => Flush();
            _flushTimer.Start();

            // Set up connection monitoring
            Core.Instance.Connections.ConnectionAdded += OnConnectionAdded;
            Core.Instance.Connections.ConnectionRemoved += OnConnectionRemoved;
            foreach (var conn in Core.Instance.Connections.All)
                SubscribeToConnection(conn);

            _connectionWatchdog = new System.Timers.Timer(15_000) { AutoReset = true };
            _connectionWatchdog.Elapsed += (s, e) => CheckConnectionHealth();
            _connectionWatchdog.Start();

            Log($"╭─ Strategy started on {CurrentSymbol.Name}  (tickSize={_tickSize})", StrategyLoggingLevel.Info);
            Log($"│  Quantity={Quantity}  Server bracket TP={ServerTakeProfitTicks}t  SL={ServerStopLossTicks}t  (attached to the entry order)", StrategyLoggingLevel.Info);
            Log($"│  Trading hours {(UseTradingHours ? "ENABLED" : "DISABLED")}   Account limits {(UseAccountLimit ? $"ENABLED TP=${AccountTakeProfit} SL=${AccountStopLoss}" : "DISABLED")}", StrategyLoggingLevel.Info);
            Log($"│  L1 quotes ENABLED   L2 depth ENABLED (OnNewLevel2 + aggregated DOM pull in OnNewTick)", StrategyLoggingLevel.Info);
            Log($"│  Entry trigger: EMA crossover ({EmaBarPeriod} bars, fast={EmaFastPeriod} slow={EmaSlowPeriod}), traded WITH the trend  signal expiry={EmaSignalExpirySeconds}s  bars loaded={_hdmEma?.Count ?? 0}", StrategyLoggingLevel.Info);
            Log($"│  Trades → {_tradeCsv}", StrategyLoggingLevel.Info);

            // Instrument identity, printed because position matching depends on it.
            // The strategy is attached to the continuous contract ("HG") while fills
            // come back on the concrete one ("HGZ6"); IsOurSymbol bridges the two via
            // Root. If Root is blank here, that bridge cannot work and every fill
            // will go untracked and unlogged -- exactly the 2026-09-14 failure.
            Log($"│  Instrument: Name={CurrentSymbol.Name}  Root={(string.IsNullOrEmpty(CurrentSymbol.Root) ? "(none)" : CurrentSymbol.Root)}  " +
                $"Id={CurrentSymbol.Id}  Exchange={CurrentSymbol.ExchangeId}  Account={CurrentAccount.Name}", StrategyLoggingLevel.Info);

            // Anything already open on this instrument before the strategy started
            // is reported now; it also proves the matcher works against real broker
            // objects rather than only against CurrentSymbol.
            var preExisting = Core.Instance.Positions
                .Where(pp => IsOurAccount(pp.Account) && IsOurSymbol(pp.Symbol)).ToList();
            if (preExisting.Count > 0)
            {
                foreach (var pp in preExisting)
                    Log($"│  Pre-existing position matched: {pp.Id} on {pp.Symbol?.Name} " +
                        $"({pp.Side} {pp.Quantity} @ {pp.OpenPrice:F5}) — not adopted; close it or restart flat",
                        StrategyLoggingLevel.Error);
            }
            Log($"╰─ Waiting for quotes…", StrategyLoggingLevel.Info);
        }

        protected override void OnStop()
        {
            _isStopping = true;

            if (CurrentSymbol != null)
            {
                CurrentSymbol.NewLast -= OnNewTick;
                CurrentSymbol.NewQuote -= OnNewQuote;
                CurrentSymbol.NewLevel2 -= OnNewLevel2;
            }
            Core.Instance.PositionAdded -= OnPositionAdded;
            Core.Instance.PositionRemoved -= OnPositionRemoved;
            Core.Instance.TradeAdded -= OnTradeAdded;

            foreach (var kv in _connectionHandlers) kv.Key.StateChanged -= kv.Value;
            _connectionHandlers.Clear();
            Core.Instance.Connections.ConnectionAdded -= OnConnectionAdded;
            Core.Instance.Connections.ConnectionRemoved -= OnConnectionRemoved;

            _entryLimitTimer?.Stop(); _entryLimitTimer?.Dispose();
            _connectionWatchdog?.Stop(); _connectionWatchdog?.Dispose(); _connectionWatchdog = null;
            _flushTimer?.Stop(); _flushTimer?.Dispose(); _flushTimer = null;

            _hdmEma?.Dispose(); _hdmEma = null; _ema = null;

            // Anything still waiting on a realized result is settled now, with the
            // broker's figure if it has landed, so stopping never discards a trade.
            List<TradeRecord> stillPending;
            lock (_pendingTradesLock)
            {
                stillPending = _pendingTrades.Values.ToList();
                _pendingTrades.Clear();
            }
            foreach (var record in stillPending)
                CompleteTrade(record);

            Flush();
            Log($"🛑 Strategy stopped.", StrategyLoggingLevel.Info);
        }

        protected override void OnRemove() { CurrentSymbol = null; CurrentAccount = null; }

        protected override void OnInitializeMetrics(Meter meter)
        {
            base.OnInitializeMetrics(meter);
            meter.CreateObservableCounter("balance",
                () => CurrentAccount.Balance - StartingBalance,
                description: "Balance");
        }

        // ======================================================
        // MARKET DATA HANDLERS
        // ======================================================

        // Every executed trade print. Two jobs:
        //   1. Refresh the aggregated depth ladder (_sortedBids/_sortedAsks). The pushed DOMQuote
        //      handed to OnNewLevel2 is not an aggregated, price-sorted book -- this pull is the
        //      only thing that gives one, and OnNewTick is the right context to do it in.
        //   2. Hand the trade to strategy-specific flow logic.
        private void OnNewTick(Symbol symbol, Last last)
        {
            // Pull a fresh aggregated DOM snapshot into our own sorted fields
            try
            {
                var dom = CurrentSymbol?.DepthOfMarket?.GetDepthOfMarketAggregatedCollections(
                    new GetLevel2ItemsParameters
                    {
                        AggregateMethod = AggregateMethod.ByPriceLVL,
                        LevelsCount = DomLevelsToPull,
                        CalculateCumulative = true
                    });

                if (dom != null && dom.Bids?.Length > 0 && dom.Asks?.Length > 0)
                {
                    // GetDepthOfMarketAggregatedCollections returns arrays, already sorted by price
                    _sortedBids = dom.Bids.ToList();  // Bids descending
                    _sortedAsks = dom.Asks.ToList();  // Asks ascending
                }
            }
            catch { }

            if (last == null || last.Size <= 0) return;

            // TODO: Feed the trade print into strategy-specific flow logic here.
            // Example: AddTradeEvent(last.Price, (int)last.Size, isBuyAggressor);
        }

        private void OnNewQuote(Symbol symbol, Quote quote)
        {
            if (quote == null) return;
            _latestQuote = quote;

            _bid = quote.Bid; _ask = quote.Ask;
            if (double.IsNaN(_bid) || double.IsNaN(_ask) || _bid <= 0 || _ask <= 0) return;
            _lastMid = (_bid + _ask) / 2.0;

            // 1. Track excursion stats on the open position (no exit decisions —
            //    the broker's attached TP/SL is the only thing that closes a trade)
            ManageOpenPositions();

            // 2. Re-evaluate the EMA crossover (cheap; only changes when a bar closes)
            UpdateEntrySignal();

            // Everything below decides whether to place a new entry
            lock (_positionLock)
            {
                if (_hasOpenPosition || _entrySent) return;

                // Gate 1: Trading hours restriction
                if (UseTradingHours)
                {
                    var t = TimeSpan.FromSeconds(Math.Round(NowEst().TimeOfDay.TotalSeconds));
                    if (!IsTradingTimeValid(t)) { GateLog("outside trading hours"); return; }
                }

                // Gate 2: Account P&L limits
                if (UseAccountLimit)
                {
                    double net = CurrentAccount.Balance - StartingBalance;
                    if (net >= AccountTakeProfit * Quantity || net <= AccountStopLoss * Quantity)
                    {
                        GateLog($"account limit hit: net={net:F2}");
                        return;
                    }
                }

                // Gate 3: Re-entry cooldown
                if (ReentryCooldownSeconds > 0 && _lastCloseTimestamp != 0)
                {
                    double since = (System.Diagnostics.Stopwatch.GetTimestamp() - _lastCloseTimestamp)
                        / (double)System.Diagnostics.Stopwatch.Frequency;
                    if (since < ReentryCooldownSeconds) return;
                }

                // Gate 4: Entry signal ready
                if (_pendingSignalSide == null) { GateLog("no EMA crossover signal"); return; }

                // Place entry order
                PlaceEntry(_pendingSignalSide.Value);
            }
        }

        // ======================================================
        // MBO DATA HANDLER (Level 2 / Order-Level Events)
        // ======================================================

        private void OnNewLevel2(Symbol symbol, Level2Quote level2, DOMQuote dom)
        {
            // Cache push-based MBO (order-level data)
            if (level2 != null)
                _latestMbo = level2;

            // Cache the push-based DOM as a liveness marker only. The depth the strategy reads
            // (_sortedBids/_sortedAsks) is pulled in OnNewTick, not taken from here.
            if (dom != null)
                _latestDom = dom;

            // Log once when both Level2 and DOM events have fired, so a dead MBO feed is visible
            if (level2 != null && dom != null && !_loggedLevel2Connected)
            {
                _loggedLevel2Connected = true;
                Log($"✅ Level2 + DOM events connected", StrategyLoggingLevel.Info);
            }

            // TODO: Add MBO-based entry logic if needed
            // Example: if (IsBestBidFilledOrder(level2)) { ... }
        }

        // ======================================================
        // ENTRY SIGNAL GENERATION — 9/20 EMA CROSSOVER, TRADED WITH THE TREND
        // ======================================================
        // Evaluated every tick, but cheap: Fast/Slow only read the last two CLOSED
        // bars (shift 1 and 2), so the result is static within a bar and only
        // actually changes the moment a new bar closes.
        //
        // fast crosses above slow -> buy (go with the up-trend)
        // fast crosses below slow -> sell (go with the down-trend)
        //
        // An opposite crossover overwrites a still-pending, unfilled signal
        // outright rather than requiring it to be cancelled first. The signal
        // survives timed-out entry retries (same trend, keep trying) until it
        // fills, is reversed, or expires via EmaSignalExpirySeconds.
        protected void UpdateEntrySignal()
        {
            if (_ema == null || _hdmEma == null || _hdmEma.Count < EmaSlowPeriod + 3) return;

            double fast1 = _ema.Fast(1), slow1 = _ema.Slow(1);
            double fast2 = _ema.Fast(2), slow2 = _ema.Slow(2);
            if (double.IsNaN(fast1) || double.IsNaN(slow1) || double.IsNaN(fast2) || double.IsNaN(slow2)) return;

            if (_pendingSignalSide != null && EmaSignalExpirySeconds > 0
                && (DateTime.Now - _pendingSignalTime).TotalSeconds > EmaSignalExpirySeconds)
            {
                Log($"⌛ EMA signal expired — {_pendingSignalSide} unfilled for {EmaSignalExpirySeconds}s; " +
                    "this crossover is spent, waiting for the next one", StrategyLoggingLevel.Info);
                _pendingSignalSide = null;
            }

            bool crossedUp = fast2 < slow2 && fast1 > slow1;
            bool crossedDown = fast2 > slow2 && fast1 < slow1;

            // ONE POSITION PER CROSSOVER.
            //
            // crossedUp/crossedDown are derived from bars at shift 1 and 2 -- the last
            // two CLOSED bars -- so they do not change while the current bar is still
            // forming. A crossover condition therefore reads TRUE on every quote for
            // the whole of the following bar (30 seconds at SECOND30, which can be
            // hundreds of quotes).
            //
            // Latching on _pendingSignalSide did not hold, because PlaceEntry sets it
            // back to null the moment the order goes out: the very next quote saw
            // "crossedUp && _pendingSignalSide != Side.Buy" as true again and re-armed
            // the SAME crossover. With a 3s entry timeout and a 4-tick stop, one
            // crossover could open several positions in a row.
            //
            // _lastCrossoverSide is never touched by order placement, so it survives
            // that consumption and the same crossover cannot arm twice. Only the
            // opposite crossover flips it.
            if (crossedUp && _lastCrossoverSide != Side.Buy)
            {
                _lastCrossoverSide = Side.Buy;
                _pendingSignalSide = Side.Buy;
                _pendingSignalTime = DateTime.Now;
                Log($"📈 EMA crossover UP  fast={fast1:F5} slow={slow1:F5} — going long with the trend", StrategyLoggingLevel.Info);
            }
            else if (crossedDown && _lastCrossoverSide != Side.Sell)
            {
                _lastCrossoverSide = Side.Sell;
                _pendingSignalSide = Side.Sell;
                _pendingSignalTime = DateTime.Now;
                Log($"📉 EMA crossover DOWN  fast={fast1:F5} slow={slow1:F5} — going short with the trend", StrategyLoggingLevel.Info);
            }
        }

        // ======================================================
        // INSTRUMENT / ACCOUNT MATCHING
        // ======================================================
        // Does this symbol refer to the instrument the strategy is trading?
        //
        // Deliberately NOT a plain Symbol.Equals. The strategy is attached to the
        // continuous contract ("HG"), but every position and order the broker
        // sends back is stamped with the CONCRETE contract it actually routed to
        // ("HGZ6"). Symbol.Equals compares identity, so HGZ6.Equals(HG) is false.
        //
        // That one mismatch silently disabled all position tracking: on
        // 2026-09-14 the strategy placed 34 entries, logged 0 fills and 0 closes,
        // and wrote 0 CSV rows, while the account was down $200 and the broker's
        // own order log showed HGZ6 entry fills with market bracket exits.
        // OnPositionAdded returned at the symbol guard, so _myPositionIds stayed
        // empty, so OnPositionRemoved returned before it could ever call
        // WriteTrade. The same mismatch also made the duplicate-entry pre-flight
        // in PlaceEntry unable to see a live position.
        private bool IsOurSymbol(Symbol symbol)
        {
            if (symbol == null || CurrentSymbol == null) return false;

            if (symbol.Equals(CurrentSymbol)) return true;
            if (!string.IsNullOrEmpty(symbol.Id)
                && string.Equals(symbol.Id, CurrentSymbol.Id, StringComparison.OrdinalIgnoreCase))
                return true;

            // Bridge continuous <-> concrete contract. Root is the contract root
            // ("HG" for HGZ6); it is empty on non-derivative symbols, where Name
            // is the right thing to compare instead.
            string theirRoot = string.IsNullOrEmpty(symbol.Root) ? symbol.Name : symbol.Root;
            string ourRoot = string.IsNullOrEmpty(CurrentSymbol.Root) ? CurrentSymbol.Name : CurrentSymbol.Root;
            if (string.IsNullOrEmpty(theirRoot) || string.IsNullOrEmpty(ourRoot)) return false;
            if (!string.Equals(theirRoot, ourRoot, StringComparison.OrdinalIgnoreCase)) return false;

            // Only bridge when one side IS the root symbol (the continuous one).
            // Two concrete contracts sharing a root -- HGZ6 and HGH7 -- are
            // different instruments and must never match each other.
            bool oneSideIsContinuous =
                string.Equals(symbol.Name, theirRoot, StringComparison.OrdinalIgnoreCase)
                || string.Equals(CurrentSymbol.Name, ourRoot, StringComparison.OrdinalIgnoreCase);
            if (!oneSideIsContinuous) return false;

            // Same root on a different exchange is a different instrument.
            return string.IsNullOrEmpty(symbol.ExchangeId)
                || string.IsNullOrEmpty(CurrentSymbol.ExchangeId)
                || string.Equals(symbol.ExchangeId, CurrentSymbol.ExchangeId, StringComparison.OrdinalIgnoreCase);
        }

        private bool IsOurAccount(Account account)
        {
            if (account == null || CurrentAccount == null) return false;
            return account.Equals(CurrentAccount)
                || (!string.IsNullOrEmpty(account.Id)
                    && string.Equals(account.Id, CurrentAccount.Id, StringComparison.OrdinalIgnoreCase));
        }

        private void GateLog(string why)
        {
            long now = System.Diagnostics.Stopwatch.GetTimestamp();
            double since = (now - _lastGateLogTs) / (double)System.Diagnostics.Stopwatch.Frequency;
            if (_lastGateLogTs == 0 || since >= 360.0)   // at most once per 10s
            {
                _lastGateLogTs = now;
                Log($"⏸ No entry — {why}", StrategyLoggingLevel.Info);
            }
        }

        // ======================================================
        // POSITION MONITORING — called on every quote
        // ======================================================
        // Observation only. Exits are handled entirely by the take-profit and
        // stop-loss the broker holds against the position (attached to the entry
        // order in PlaceEntry), so this method never places or cancels anything --
        // it just records how far the trade ran in each direction for the CSV.
        private void ManageOpenPositions()
        {
            lock (_positionLock)
            {
                if (!_hasOpenPosition || _openPosition == null) return;
                if (double.IsNaN(_entryPrice)) return;

                double pnlTicks = _openPosition.Side == Side.Buy
                    ? (_lastMid - _entryPrice) / _tickSize
                    : (_entryPrice - _lastMid) / _tickSize;

                // Track MFE (max favorable excursion) and MAE (max adverse excursion)
                if (pnlTicks > _positionHighWater) _positionHighWater = pnlTicks;
                if (pnlTicks < _positionLowWater) _positionLowWater = pnlTicks;
            }
        }

        // ======================================================
        // ENTRY: Place entry order
        // ======================================================
        // TODO: Implement your entry logic here
        // This method should:
        //   1. Determine entry price (market, bid/ask, limit, etc.)
        //   2. Place the order via Core.Instance.PlaceOrder()
        //   3. Store _entryLimitOrderId for tracking
        //   4. Start _entryLimitTimer to timeout unfilled orders
        //   5. Log the entry attempt
        //
        private void PlaceEntry(Side side)
        {
            if (_entrySent) return;

            // AUTHORITATIVE PRE-FLIGHT -- do not place an order on top of live state.
            //
            // _hasOpenPosition and _entrySent are strategy-local flags, written by our
            // own event handlers, and the platform's real state runs AHEAD of them.
            // The gap that matters: an entry can fill on the exchange before
            // OnPositionAdded is dispatched to us, and OnEntryTimeout can fire in that
            // same window, fail to find the not-yet-published position, and release
            // _entrySent. A quote arriving in between then passes the gate with both
            // flags false and sends a SECOND entry on top of a fill that is already
            // landing -- which times out ~3s later and cancels. That is the
            // "working orders placed and cancelled while a position is open" churn.
            //
            // Local flags cannot close that window because they are the thing lagging.
            // Ask Core directly instead: it is the same source the platform's own
            // order panel reads from.
            var livePosition = Core.Instance.Positions
                .FirstOrDefault(pos => IsOurAccount(pos.Account) && IsOurSymbol(pos.Symbol));
            if (livePosition != null)
            {
                GateLog($"position {livePosition.Id} already live — not placing another entry");
                return;
            }

            // Once an entry fills, the broker's own take-profit and stop-loss legs are
            // working orders on this symbol/account, so this check also keeps a new
            // entry out while a bracket is being held.
            var workingOrder = Core.Instance.Orders
                .FirstOrDefault(o => IsOurAccount(o.Account) && IsOurSymbol(o.Symbol)
                                  && (o.Status == OrderStatus.Opened || o.Status == OrderStatus.PartiallyFilled));
            if (workingOrder != null)
            {
                GateLog($"order {workingOrder.Id} ({workingOrder.Side}, {workingOrder.Status}) still working — not placing another entry");
                return;
            }

            _entrySent = true;

            // TODO: Replace with your entry price logic
            // Example: double limitPrice = side == Side.Buy ? _bid : _ask;
            double limitPrice = side == Side.Buy ? _bid : _ask;

            var result = Core.Instance.PlaceOrder(new PlaceOrderRequestParameters
            {
                Symbol = CurrentSymbol,
                Account = CurrentAccount,
                Side = side,
                OrderTypeId = OrderType.Limit,
                Price = limitPrice,
                Quantity = Quantity,
                TimeInForce = TimeInForce.GTC,
                TakeProfit = SlTpHolder.CreateTP(ServerTakeProfitTicks, PriceMeasurement.Offset),
                StopLoss = SlTpHolder.CreateSL(ServerStopLossTicks, PriceMeasurement.Offset)
            });

            if (result.Status != TradingOperationResultStatus.Success)
            {
                Log($"❌ Entry order failed: {result.Message}", StrategyLoggingLevel.Error);
                _entrySent = false;
                return;
            }

            _entryLimitOrderId = result.OrderId;
            _signalTimestamp = System.Diagnostics.Stopwatch.GetTimestamp();
            _signalWallTime = DateTime.Now;
            _pendingSignalSide = null;

            Log($"📤 Entry {side} {Quantity} @ {limitPrice:F5}  bracket TP={ServerTakeProfitTicks}t SL={ServerStopLossTicks}t (server-side)  cancels in {EntryTimeoutSeconds}s", StrategyLoggingLevel.Info);

            _entryLimitTimer = new System.Timers.Timer(EntryTimeoutSeconds * 1000) { AutoReset = false };
            _entryLimitTimer.Elapsed += (s, e) => OnEntryTimeout();
            _entryLimitTimer.Start();
        }

        private void OnEntryTimeout()
        {
            lock (_positionLock)
            {
                _entryLimitTimer?.Stop(); _entryLimitTimer?.Dispose(); _entryLimitTimer = null;
                if (_hasOpenPosition) return;

                if (!string.IsNullOrEmpty(_entryLimitOrderId))
                {
                    var order = Core.Instance.Orders.FirstOrDefault(o => o.Id == _entryLimitOrderId);

                    if (order == null)
                    {
                        // The entry order left Core.Instance.Orders without OnPositionAdded
                        // having fired: either it filled and the position event hasn't
                        // reached us yet, or it was cancelled/rejected externally and there
                        // is no position. Ask the platform's own collection directly rather
                        // than waiting on our event. Whichever way it went, the entry claim
                        // MUST be released on this path -- _entrySent gates every future
                        // entry in OnNewQuote, and nothing else would ever clear it.
                        var untracked = Core.Instance.Positions
                            .FirstOrDefault(p => IsOurAccount(p.Account)
                                              && IsOurSymbol(p.Symbol)
                                              && !_myPositionIds.Contains(p.Id));

                        _entryLimitOrderId = null;

                        if (untracked != null)
                        {
                            // It filled. Track it so a new entry can't stack on top and so
                            // the trade still reaches the CSV; the broker is already holding
                            // this order's take-profit and stop-loss against it.
                            _openPosition = untracked;
                            _entryPrice = untracked.OpenPrice;
                            _hasOpenPosition = true;
                            _myPositionIds.Add(untracked.Id);

                            _fillLatencySec = _signalTimestamp != 0
                                ? (System.Diagnostics.Stopwatch.GetTimestamp() - _signalTimestamp) / (double)System.Diagnostics.Stopwatch.Frequency
                                : 0;
                            _signalTimestamp = 0;

                            _positionOpenTime = DateTime.Now;
                            _positionHighWater = 0; _positionLowWater = 0;
                            _entryBidAtFill = _bid; _entryAskAtFill = _ask;
                            _tpOrderId = untracked.TakeProfit?.Id;
                            _slOrderId = untracked.StopLoss?.Id;

                            Log($"🔧 Entry timeout — order gone but position {untracked.Id} is live; " +
                                $"tracking {untracked.Side} @ {_entryPrice:F5}  " +
                                $"server bracket TP={ServerTakeProfitTicks}t SL={ServerStopLossTicks}t", StrategyLoggingLevel.Trading);
                            return;
                        }

                        Log("⏱️ Entry timeout — order gone and no untracked position; releasing entry gate", StrategyLoggingLevel.Info);
                        _entrySent = false;
                        return;
                    }

                    if (order.Status == OrderStatus.PartiallyFilled || order.FilledQuantity > 0)
                    {
                        Log($"⚠️ Entry timeout — partially filled, leaving for OnPositionAdded", StrategyLoggingLevel.Info);
                        return;
                    }

                    if (order.Status == OrderStatus.Opened)
                    {
                        var cancelResult = order.Cancel();
                        if (cancelResult.Status != TradingOperationResultStatus.Success)
                        {
                            Log($"⚠️ Entry timeout — cancel failed ({cancelResult.Message}), likely just filled", StrategyLoggingLevel.Info);
                            return;
                        }
                        Log($"⏱️ Entry order cancelled after {EntryTimeoutSeconds}s", StrategyLoggingLevel.Info);
                    }

                    _entryLimitOrderId = null;
                }

                if (_hasOpenPosition) return;
                _entrySent = false;
            }
        }

        // ======================================================
        // POSITION TRACKING
        // ======================================================

        private void OnPositionAdded(Position pos)
        {
            lock (_positionLock)
            {
                // A position we cannot match is the failure mode that hid every
                // fill on 2026-09-14, so it is logged rather than dropped in
                // silence. Throttled, because an unrelated account on the same
                // platform would otherwise flood the log.
                if (!IsOurAccount(pos.Account) || !IsOurSymbol(pos.Symbol))
                {
                    long nowTs = System.Diagnostics.Stopwatch.GetTimestamp();
                    double sinceLog = (nowTs - _lastUnmatchedLogTs) / (double)System.Diagnostics.Stopwatch.Frequency;
                    if (_lastUnmatchedLogTs == 0 || sinceLog >= 60.0)
                    {
                        _lastUnmatchedLogTs = nowTs;
                        Log($"👁 Ignoring position {pos.Id} on {pos.Symbol?.Name}/{pos.Account?.Name} — " +
                            $"does not match this strategy ({CurrentSymbol?.Name}/{CurrentAccount?.Name}). " +
                            "If this IS our fill, the instrument match is wrong and no trade will be logged.",
                            StrategyLoggingLevel.Error);
                    }
                    return;
                }
                if (_myPositionIds.Contains(pos.Id)) return;
                if (_hasOpenPosition) return;

                // A position arriving with no pending entry (_entrySent is only ever
                // true from the moment PlaceEntry sends an order until it's resolved).
                // Two ways to get here:
                //   1. A manual fill on the same account/symbol -- not ours, and it may
                //      carry no bracket at all.
                //   2. Our own entry filled, but OnEntryTimeout had already given up on
                //      the order and released the gate before this event arrived. That
                //      one IS bracketed; the timeout's own position scan catches it
                //      whenever the platform's collection is populated in time.
                // The strategy never closes a position itself, so either way it just
                // tracks this one (which blocks a new entry from stacking on top) and
                // logs, since case 1 needs a human to look at it.
                if (!_entrySent)
                {
                    _myPositionIds.Add(pos.Id);
                    Log($"⚠️ Unexpected position {pos.Id} ({pos.Side} {pos.Quantity} @ {pos.OpenPrice:F5}) " +
                        "appeared with no pending entry -- either a late fill from our own timed-out entry, or a " +
                        "manual fill. Tracking it so no new entry stacks on top, but if it wasn't ours it may have " +
                        "NO take-profit/stop-loss attached -- check it on the platform.",
                        StrategyLoggingLevel.Error);
                }

                _entryLimitTimer?.Stop(); _entryLimitTimer?.Dispose(); _entryLimitTimer = null;
                _entryOrderIdForPosition = _entryLimitOrderId;
                _entryLimitOrderId = null;

                _openPosition = pos;
                _entryPrice = pos.OpenPrice;
                _hasOpenPosition = true;
                _myPositionIds.Add(pos.Id);

                _fillLatencySec = _signalTimestamp != 0
                    ? (System.Diagnostics.Stopwatch.GetTimestamp() - _signalTimestamp) / (double)System.Diagnostics.Stopwatch.Frequency
                    : 0;
                _signalTimestamp = 0;

                _positionOpenTime = DateTime.Now;
                _positionHighWater = 0; _positionLowWater = 0;
                _entryBidAtFill = _bid; _entryAskAtFill = _ask;

                // The bracket legs identify the exit execution outright, so their
                // ids are captured while the position still exposes them.
                _tpOrderId = pos.TakeProfit?.Id;
                _slOrderId = pos.StopLoss?.Id;

                Log($"✅ Filled {pos.Side} {pos.Quantity} @ {_entryPrice:F5}  latency={_fillLatencySec * 1000:F0}ms  " +
                    $"server bracket TP={ServerTakeProfitTicks}t SL={ServerStopLossTicks}t", StrategyLoggingLevel.Trading);

                // No exit orders are placed here: the take-profit and stop-loss were
                // attached to the entry order and are held by the broker.

                // TODO: Add any additional position-opened logic here
            }
        }

        private void OnPositionRemoved(Position pos)
        {
            lock (_positionLock)
            {
                if (!_myPositionIds.Contains(pos.Id)) return;

                // Nothing to sweep: both bracket legs belong to the broker, which
                // OCO-cancels the one that didn't fill when the position goes flat.
                _myPositionIds.Remove(pos.Id);

                // Capture what only the strategy knows. The P&L is deliberately
                // NOT read from pos here -- see the TradeRecord comment above.
                var record = new TradeRecord
                {
                    PositionId = pos.Id,
                    Side = pos.Side,
                    EntryPrice = _entryPrice,
                    Quantity = pos.Quantity > 0 ? pos.Quantity : Quantity,
                    EntryOrderId = _entryOrderIdForPosition,
                    TpOrderId = _tpOrderId,
                    SlOrderId = _slOrderId,
                    OpenTime = _positionOpenTime,
                    CloseTime = DateTime.Now,
                    Mfe = _positionHighWater,
                    Mae = _positionLowWater,
                    EntryBid = _entryBidAtFill,
                    EntryAsk = _entryAskAtFill,
                    ExitBid = _bid,
                    ExitAsk = _ask,
                    FillLatencySec = _fillLatencySec
                };

                // Releasing the trading gate must never depend on the bookkeeping
                // below succeeding: these flags are the only thing that lets the
                // strategy trade again, so they are set in a finally.
                try
                {
                    RegisterPendingTrade(record);
                }
                catch (Exception ex)
                {
                    Log($"❌ Failed to queue closed trade {pos.Id}: {ex.Message}", StrategyLoggingLevel.Error);
                }
                finally
                {
                    _hasOpenPosition = false;
                    _openPosition = null;
                    _entrySent = false;
                    _entryPrice = double.NaN;
                    _lastCloseTimestamp = System.Diagnostics.Stopwatch.GetTimestamp();
                }
            }
        }

        // ======================================================
        // CONNECTION / RECONNECT HANDLING
        // ======================================================

        private void SubscribeToConnection(Connection connection)
        {
            if (_connectionHandlers.ContainsKey(connection)) return;
            EventHandler<ConnectionStateChangedEventArgs> handler = (s, e) => OnConnectionStateChanged(connection, e);
            connection.StateChanged += handler;
            _connectionHandlers[connection] = handler;
        }

        private void OnConnectionAdded(Connection connection)
        {
            Log($"🔌 New connection: {connection.Name}", StrategyLoggingLevel.Info);
            SubscribeToConnection(connection);
        }

        private void OnConnectionRemoved(Connection connection)
        {
            if (_connectionHandlers.TryGetValue(connection, out var handler))
            {
                connection.StateChanged -= handler;
                _connectionHandlers.Remove(connection);
            }
        }

        private void OnConnectionStateChanged(Connection connection, ConnectionStateChangedEventArgs e)
        {
            if (_isStopping) return;
            if (e.NewState == ConnectionState.Connected)
            {
                Log($"✅ Reconnected: {connection.Name}", StrategyLoggingLevel.Info);
                RebindAfterReconnect();
                Task.Run(async () => { await Task.Delay(5000); if (!_isStopping) RebindAfterReconnect(); });
            }
            else if (e.NewState == ConnectionState.Disconnected)
            {
                Log($"⚠️ Disconnected: {connection.Name}", StrategyLoggingLevel.Error);
            }
        }

        private void RebindAfterReconnect()
        {
            if (_isStopping) return;

            if (CurrentAccount != null)
            {
                var liveAccount = Core.Instance.Accounts.FirstOrDefault(a => a.Id == CurrentAccount.Id);
                if (liveAccount != null) { CurrentAccount = liveAccount; Log("✅ Reattached account after reconnect", StrategyLoggingLevel.Info); }
                else Log("❌ Failed to reacquire account", StrategyLoggingLevel.Error);
            }

            if (CurrentSymbol != null)
            {
                // Core.GetSymbol returns a NEW Symbol instance, so EVERY market-data event must be
                // rebound onto it. Missing one here kills that feed silently for the rest of the
                // session -- the strategy keeps running on frozen cached values.
                CurrentSymbol.NewLast -= OnNewTick;
                CurrentSymbol.NewQuote -= OnNewQuote;
                CurrentSymbol.NewLevel2 -= OnNewLevel2;
                CurrentSymbol = Core.GetSymbol(CurrentSymbol.CreateInfo());
                CurrentSymbol.NewLast += OnNewTick;
                CurrentSymbol.NewQuote += OnNewQuote;
                CurrentSymbol.NewLevel2 += OnNewLevel2;
                _loggedLevel2Connected = false;   // re-confirm the L2 feed came back
                Log($"✅ Reattached symbol + L1/L2 feeds: {CurrentSymbol.Name}", StrategyLoggingLevel.Info);

                _hdmEma?.Dispose();
                _hdmEma = CurrentSymbol.GetHistory(new HistoryRequestParameters
                {
                    Symbol = CurrentSymbol,
                    FromTime = _emaStartPoint,
                    Aggregation = new HistoryAggregationTime(EmaBarPeriod, CurrentSymbol.HistoryType)
                });
                _ema = new EMAHelper(_hdmEma, EmaFastPeriod, EmaSlowPeriod);
                Log("✅ EMA history reinitialized after reconnect", StrategyLoggingLevel.Info);
            }

            lock (_positionLock)
            {
                foreach (var p in Core.Instance.Positions)
                {
                    if (_myPositionIds.Contains(p.Id) && IsOurAccount(p.Account))
                    {
                        _openPosition = p; _entryPrice = p.OpenPrice; _hasOpenPosition = true;
                        Log($"🔄 Reconnect: re-attached live position {p.Id}", StrategyLoggingLevel.Info);
                    }
                }
            }

            Core.Instance.PositionAdded -= OnPositionAdded; Core.Instance.PositionAdded += OnPositionAdded;
            Core.Instance.PositionRemoved -= OnPositionRemoved; Core.Instance.PositionRemoved += OnPositionRemoved;
            Core.Instance.TradeAdded -= OnTradeAdded; Core.Instance.TradeAdded += OnTradeAdded;
            Log("✅ Reattached events after reconnect", StrategyLoggingLevel.Info);
        }

        private void CheckConnectionHealth()
        {
            if (_isStopping) return;
            bool anyConnected = Core.Instance.Connections.All.Any(c => c.State == ConnectionState.Connected);

            if (!anyConnected && _lastKnownConnected)
            {
                _lastKnownConnected = false;
                Log($"🚨 WATCHDOG: No connections — open positions={_myPositionIds.Count}", StrategyLoggingLevel.Error);
            }
            else if (anyConnected && !_lastKnownConnected)
            {
                _lastKnownConnected = true;
                Log("✅ WATCHDOG: Connection restored", StrategyLoggingLevel.Info);
                RebindAfterReconnect();
            }
        }

        // ======================================================
        // REALIZED TRADE RESULT
        // ======================================================
        // Gross P&L is reconstructed from the executions the trade actually
        // printed: entry fill, exit fill, quantity, tick value. Nothing here
        // trusts a vendor-supplied P&L field, because none of them survived
        // contact with this connection:
        //
        //   1. Position.GrossPnL at PositionRemoved time is the UNREALIZED mark
        //      against the last quote the strategy processed -- $37.50 for a
        //      take-profit that had filled 5 ticks out for $62.50.
        //   2. Core.Instance.ClosedPositionAdded never fires here, and
        //      ClosedPositions never holds a matching record, so every trade fell
        //      through to the timeout and logged an empty P&L.
        //   3. Matching executions on Trade.PositionId looked right and was worse
        //      than either: that id is the composite "HGZ6@COMEX@Paper200062",
        //      the SAME string for every position on the instrument. Combined
        //      with a buffer that never consumed what it matched, a single
        //      execution at 6.39050 was claimed by all nine trades of the
        //      session, so every row implied that one exit price.
        //
        // What actually discriminates is the ORDER ID, plus consuming each
        // execution exactly once. The strategy holds at most one position at a
        // time, so an unclaimed opposite-side execution after the entry is the
        // exit even when the ids are unavailable.

        // Dollar value of one tick. GetTickCost is the platform's own figure;
        // the fallback is the standard futures identity, tick size x contract
        // size, which for HG is 0.0005 x 25,000 = $12.50.
        private double TickValue(double atPrice)
        {
            if (CurrentSymbol == null || _tickSize <= 0) return double.NaN;

            try
            {
                double cost = CurrentSymbol.GetTickCost(atPrice);
                if (!double.IsNaN(cost) && !double.IsInfinity(cost) && cost > 0) return cost;
            }
            catch { /* fall through to the identity below */ }

            double lot = CurrentSymbol.LotSize;
            return lot > 0 ? _tickSize * lot : double.NaN;
        }

        // One execution on our instrument, in arrival order. Claimed is what stops
        // a fill being counted toward more than one trade.
        private class Execution
        {
            public string OrderId;
            public Side Side;
            public double Price;
            public double Quantity;
            public DateTime Seen;
            public bool Claimed;
        }

        private readonly List<Execution> _executions = new List<Execution>();

        private void OnTradeAdded(Trade trade)
        {
            if (trade == null) return;
            if (!IsOurAccount(trade.Account) || !IsOurSymbol(trade.Symbol)) return;
            if (trade.Price <= 0 || trade.Quantity <= 0) return;

            // PositionImpactType is deliberately NOT used as a filter. It is
            // vendor-populated and an Undefined value would silently discard every
            // execution -- the failure mode that produced a session of empty P&L.
            var execution = new Execution
            {
                OrderId = trade.OrderId,
                Side = trade.Side,
                Price = trade.Price,
                Quantity = trade.Quantity,
                Seen = DateTime.Now
            };

            TradeRecord completed = null;

            lock (_pendingTradesLock)
            {
                _executions.Add(execution);

                // Keep the tail bounded; claimed executions are of no further use.
                _executions.RemoveAll(x => x.Claimed && (DateTime.Now - x.Seen).TotalMinutes > 5);
                if (_executions.Count > 200) _executions.RemoveRange(0, _executions.Count - 200);

                foreach (var record in _pendingTrades.Values.ToList())
                {
                    if (!ApplyExecutions(record)) continue;
                    if (!record.ExitComplete) continue;
                    _pendingTrades.Remove(record.PositionId);
                    completed = record;
                    break;
                }
            }

            Log($"🧾 Execution {execution.Side} {execution.Quantity:F0} @ {execution.Price:F5} " +
                $"order={execution.OrderId} impact={trade.PositionImpactType}", StrategyLoggingLevel.Trading);

            if (completed != null) CompleteTrade(completed);
        }

        // Fold every execution this trade can claim into it. Caller holds
        // _pendingTradesLock. Returns true if anything was claimed.
        private bool ApplyExecutions(TradeRecord record)
        {
            if (record == null) return false;
            bool claimedAny = false;

            foreach (var execution in _executions)
            {
                if (execution.Claimed) continue;

                // --- entry side -------------------------------------------------
                bool isEntry = !string.IsNullOrEmpty(record.EntryOrderId)
                            && execution.OrderId == record.EntryOrderId;
                if (isEntry)
                {
                    record.EntryQty += execution.Quantity;
                    record.EntryNotional += execution.Price * execution.Quantity;
                    execution.Claimed = true;
                    claimedAny = true;
                    continue;
                }

                if (record.ExitComplete) continue;

                // --- exit side, by bracket leg id (authoritative) ----------------
                string leg = null;
                if (!string.IsNullOrEmpty(record.TpOrderId) && execution.OrderId == record.TpOrderId)
                    leg = "TakeProfit";
                else if (!string.IsNullOrEmpty(record.SlOrderId) && execution.OrderId == record.SlOrderId)
                    leg = "StopLoss";

                // --- exit side, by shape (only when no leg id was available) -----
                // Safe because the strategy holds one position at a time and each
                // execution is consumed: an unclaimed opposite-side fill that is
                // not our own entry order can only be this position's exit.
                bool shapeExit = leg == null
                              && string.IsNullOrEmpty(record.TpOrderId)
                              && string.IsNullOrEmpty(record.SlOrderId)
                              && execution.Side != record.Side
                              && execution.OrderId != record.EntryOrderId;

                if (leg == null && !shapeExit) continue;

                record.ExitQty += execution.Quantity;
                record.ExitNotional += execution.Price * execution.Quantity;
                if (leg != null) record.ExitLeg = leg;
                execution.Claimed = true;
                claimedAny = true;
            }

            return claimedAny;
        }

        private void RegisterPendingTrade(TradeRecord record)
        {
            bool complete;
            lock (_pendingTradesLock)
            {
                // The executions that closed this position almost always arrive
                // BEFORE PositionRemoved -- the fill is what ends the position --
                // so they are already buffered and waiting to be claimed.
                ApplyExecutions(record);
                complete = record.ExitComplete;
                if (!complete) _pendingTrades[record.PositionId] = record;
            }

            if (complete) { CompleteTrade(record); return; }

            // Never let a trade go unrecorded because an execution never arrived.
            var fallback = new System.Timers.Timer(RealizedPnLTimeoutSeconds * 1000) { AutoReset = false };
            fallback.Elapsed += (s2, e2) =>
            {
                TradeRecord pending;
                lock (_pendingTradesLock)
                {
                    if (!_pendingTrades.TryGetValue(record.PositionId, out pending)) return;
                    _pendingTrades.Remove(record.PositionId);
                }

                Log($"⚠️ No closing execution for position {pending.PositionId} after " +
                    $"{RealizedPnLTimeoutSeconds}s — recording it with an unknown P&L rather than dropping it",
                    StrategyLoggingLevel.Error);
                CompleteTrade(pending);
            };
            record.Fallback = fallback;
            fallback.Start();
        }

        // Writes the row. Interlocked so the fallback timer and the execution
        // stream can race without ever producing two rows for one trade.
        private void CompleteTrade(TradeRecord record)
        {
            if (record == null) return;
            if (System.Threading.Interlocked.Exchange(ref record.Written, 1) != 0) return;

            record.Fallback?.Stop();
            record.Fallback?.Dispose();
            record.Fallback = null;

            // The execution fill is the truth. Position.OpenPrice disagreed with it
            // by a tick on at least one trade (recorded 6.38900 against an actual
            // fill of 6.38950), so it is only a fallback.
            double entryPrice = !double.IsNaN(record.EntryFill) ? record.EntryFill : record.EntryPrice;
            double exitPrice = record.ExitPrice;

            double grossPnL = double.NaN, ticks = double.NaN, tickValue = double.NaN;

            if (!double.IsNaN(exitPrice) && !double.IsNaN(entryPrice) && _tickSize > 0)
            {
                // A long makes money when the exit is higher; a short when it is lower.
                double direction = record.Side == Side.Buy ? 1.0 : -1.0;
                ticks = (exitPrice - entryPrice) * direction / _tickSize;
                tickValue = TickValue(entryPrice);
                if (!double.IsNaN(tickValue))
                    grossPnL = ticks * tickValue * record.ExitQty;
            }

            // Prefer the leg that actually filled; fall back to the sign.
            string exitReason = !string.IsNullOrEmpty(record.ExitLeg) ? record.ExitLeg
                : double.IsNaN(grossPnL) ? "Unknown"
                : grossPnL > 0 ? "TakeProfit"
                : grossPnL < 0 ? "StopLoss" : "Flat";

            try
            {
                WriteTrade(record, entryPrice, grossPnL, exitReason);

                // The inputs are logged with the result so any row in the CSV can
                // be checked by hand without re-deriving it from the platform log.
                Log($"🏁 Closed {record.Side}  reason={exitReason}  " +
                    $"Gross={(double.IsNaN(grossPnL) ? "n/a" : grossPnL.ToString("F2"))}  " +
                    $"entry={entryPrice:F5} exit={(double.IsNaN(exitPrice) ? "n/a" : exitPrice.ToString("F5"))} " +
                    $"({(double.IsNaN(ticks) ? "?" : ticks.ToString("F1"))}t x " +
                    $"{(double.IsNaN(tickValue) ? "?" : tickValue.ToString("F2"))}/t x {record.ExitQty:F0})  " +
                    $"MFE={record.Mfe:F1}t MAE={record.Mae:F1}t", StrategyLoggingLevel.Info);
            }
            catch (Exception ex)
            {
                Log($"❌ Failed to record closed trade {record.PositionId}: {ex.Message}", StrategyLoggingLevel.Error);
            }
        }

        // ======================================================
        // CSV LOGGING
        // ======================================================
        // TODO: Add strategy-specific columns to EnsureHeaders and WriteTrade
        // For example:
        //   EnsureHeaders: add "indicatorValue,entrySignal,exitSignal" etc.
        //   WriteTrade: add string.Format values for those fields

        private const string CsvHeader =
            "openTime,closeTime,side,entryPrice,exitReason,mfeTicks,maeTicks," +
            "grossPnL,fillLatencyMs,entryBid,entryAsk,spreadAtFillTicks," +
            "exitBid,exitAsk";

        private void EnsureHeaders()
        {
            try
            {
                // The path is derived from the running user's profile, so the folder
                // is not guaranteed to exist -- create it rather than let every
                // append fail against a missing directory for the whole session.
                string dir = Path.GetDirectoryName(_tradeCsv);
                if (!string.IsNullOrEmpty(dir) && !Directory.Exists(dir))
                    Directory.CreateDirectory(dir);

                if (!File.Exists(_tradeCsv) || new FileInfo(_tradeCsv).Length == 0)
                {
                    File.AppendAllText(_tradeCsv, CsvHeader + Environment.NewLine);
                    return;
                }

                // A file written against a different column set would take new rows
                // silently misaligned. Archive it and start a clean one.
                string firstLine = File.ReadLines(_tradeCsv).FirstOrDefault();
                if (!string.Equals(firstLine, CsvHeader, StringComparison.Ordinal))
                {
                    string archived = Path.Combine(
                        Path.GetDirectoryName(_tradeCsv) ?? "",
                        Path.GetFileNameWithoutExtension(_tradeCsv)
                            + DateTime.Now.ToString("-yyyyMMdd-HHmmss") + ".csv");
                    File.Move(_tradeCsv, archived);
                    File.AppendAllText(_tradeCsv, CsvHeader + Environment.NewLine);
                    Log($"📁 CSV columns changed — previous file archived to {archived}", StrategyLoggingLevel.Info);
                }
            }
            catch (Exception ex) { Log($"❌ CSV header error: {ex.Message}", StrategyLoggingLevel.Error); }
        }

        private void WriteTrade(TradeRecord record, double entryPrice, double grossPnL, string exitReason)
        {
            string row = string.Join(",",
                record.OpenTime.ToString("yyyy-MM-dd HH:mm:ss.fff"),
                record.CloseTime.ToString("yyyy-MM-dd HH:mm:ss.fff"),
                record.Side,
                entryPrice.ToString("F5"),
                string.IsNullOrEmpty(exitReason) ? "unknown" : exitReason,
                record.Mfe.ToString("F1"),
                record.Mae.ToString("F1"),
                (double.IsNaN(grossPnL) ? "" : grossPnL.ToString("F2")),
                (record.FillLatencySec * 1000).ToString("F0"),
                (double.IsNaN(record.EntryBid) ? "" : record.EntryBid.ToString("F5")),
                (double.IsNaN(record.EntryAsk) ? "" : record.EntryAsk.ToString("F5")),
                (double.IsNaN(record.EntryBid) || _tickSize <= 0
                    ? "" : ((record.EntryAsk - record.EntryBid) / _tickSize).ToString("F2")),
                (double.IsNaN(record.ExitBid) ? "" : record.ExitBid.ToString("F5")),
                (double.IsNaN(record.ExitAsk) ? "" : record.ExitAsk.ToString("F5")));

            lock (_csvLock) { _tradeBuf.Add(row); }

            // Write through now rather than waiting up to 5s for the timer -- a
            // closed trade should be on disk before the next one opens.
            Flush();
        }

        private void Flush()
        {
            List<string> trades;
            lock (_csvLock)
            {
                if (_tradeBuf.Count == 0) return;
                trades = new List<string>(_tradeBuf);
            }

            try
            {
                File.AppendAllLines(_tradeCsv, trades);
            }
            catch (Exception ex)
            {
                // The buffer is deliberately NOT cleared on failure. It used to be
                // cleared before the write was attempted, so a locked or missing
                // file destroyed the rows outright and the only trace was a log
                // line. Leaving them queued means the next flush -- or OnStop --
                // still gets them to disk once the file is writable again.
                Log($"❌ CSV flush error (rows kept for retry): {ex.Message}", StrategyLoggingLevel.Error);
                return;
            }

            // Only drop what was actually written; anything WriteTrade appended
            // while the file I/O was in flight stays queued for the next flush.
            lock (_csvLock) { _tradeBuf.RemoveRange(0, Math.Min(trades.Count, _tradeBuf.Count)); }
        }


        // ======================================================
        // TIME HELPERS
        // ======================================================

        private static readonly TimeZoneInfo EstZone =
            TimeZoneInfo.FindSystemTimeZoneById("Eastern Standard Time");

        private DateTime NowEst() =>
            TimeZoneInfo.ConvertTimeFromUtc(DateTime.UtcNow, EstZone);

        private bool IsTradingTimeValid(TimeSpan t)
        {
            // NY open/close bursts where spreads/fills are most active.
            var windows = new (int sh, int sm, int eh, int em)[]
            {
                ( 18, 00, 8, 30),  
                (8, 30, 16,  0),   // 3:30–4:00 ET (optional second window)
            };
            foreach (var (sh, sm, eh, em) in windows)
            {
                var start = TimeSpan.FromMinutes(sh * 60 + sm);
                var end = TimeSpan.FromMinutes(eh * 60 + em);
                bool inWindow = start < end ? (t >= start && t < end) : (t >= start || t < end);
                if (inWindow) return true;
            }
            return false;
        }


    }
}