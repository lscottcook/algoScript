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

        // Entry trigger: HMA crossover, traded WITH the trend (fast crosses above
        // slow -> buy; fast crosses below slow -> sell). Ported from
        // vocprep\algo\TestingB and Archive\HMACrossover -- see HMAHelper.
        [InputParameter("HMA Bar Period", 18)]
        public Period HmaBarPeriod { get; set; }

        [InputParameter("HMA Fast Period", 19)]
        public int HmaFastPeriod = 5;

        [InputParameter("HMA Slow Period", 20)]
        public int HmaSlowPeriod = 15;

        // How long an unfilled crossover signal stays live before requiring a
        // fresh crossover -- prevents chasing a stale trend indefinitely on
        // repeated timeout/retry cycles. 0 = never expires.
        [InputParameter("HMA Signal Expiry (seconds, 0=never)", 21)]
        public int HmaSignalExpirySeconds = 300;

        // The take-profit / stop-loss offsets (in ticks) attached to every entry
        // order and held by the broker. These are the strategy's ONLY exit, and the
        // only numbers that reach the server -- the TargetTicks/StopTicks inputs
        // above are not used. Declared here so PlaceEntry, the log lines, and the
        // CSV's targetPrice/stopPrice columns can never disagree about the levels.
        private const int ServerTakeProfitTicks = 5;
        private const int ServerStopLossTicks = 4;

        // private string CsvPath = @"C:\Users\Administrator\Downloads\algoTrading.csv";
        private string CsvPath = @"C:\Users\Lisa\Downloads\algoTrading.csv";

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

        // ======================================================
        // STRATEGY-SPECIFIC FIELDS — HMA crossover signal
        // ======================================================

        // How far back the bar history is requested from. Four hours of the
        // configured bar period is ample for a 15-bar slow HMA and keeps the
        // initial load light.
        private readonly DateTime _hmaStartPoint = Core.TimeUtils.DateTimeUtcNow.AddHours(-4);
        private HistoricalData _hdmHma;
        private HMAHelper _hma;


        // ======================================================
        // FIELDS — entry / signal latency
        // ======================================================

        private long _lastCloseTimestamp = 0;         // Stopwatch ticks — re-entry cooldown gate
        private long _signalTimestamp = 0;             // Stopwatch ticks at entry placement
        private DateTime _signalWallTime = DateTime.MinValue;
        private double _fillLatencySec = 0;

        private int EntryTimeoutSeconds = 3;
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
        // HMA HELPER
        // ======================================================
        // Ported verbatim from vocprep\algo\TestingB\TestingB.cs, which in turn
        // took it from Archive\HMACrossover\HMACrossover.cs, so this strategy's
        // crossovers are directly comparable with those runs.
        //
        // KNOWN QUIRK, kept deliberately for parity: the final Hull smoothing step
        // is a no-op. CalculateHMA ends with GetWMA(sqrtPeriod, shift, rawHMA),
        // and passing overrideValue makes GetWMA use that same constant for every
        // bar in its loop -- a weighted average of one repeated value is just that
        // value, so it returns rawHMA unchanged. The result is therefore
        // 2*WMA(n/2) - WMA(n), the raw intermediate, NOT a true Hull MA. It is
        // noisier and crosses more often than a real HMA would. Every other
        // strategy in the archive runs it this way; see the note at the end of
        // this session if you want the corrected version instead.
        private class HMAHelper
        {
            private readonly HistoricalData hdmInd;
            private readonly int fastPeriod;
            private readonly int slowPeriod;

            public HMAHelper(HistoricalData hdmInd, int fastPeriod = 5, int slowPeriod = 15)
            {
                this.hdmInd = hdmInd;
                this.fastPeriod = fastPeriod;
                this.slowPeriod = slowPeriod;
            }

            public double Fast(int shift = 0) => CalculateHMA(fastPeriod, shift);

            public double Slow(int shift = 0) => CalculateHMA(slowPeriod, shift);

            private double CalculateHMA(int period, int shift = 0)
            {
                if (hdmInd == null || hdmInd.Count < period + shift)
                    return double.NaN;

                int halfPeriod = Math.Max(1, period / 2);
                int sqrtPeriod = Math.Max(1, (int)Math.Sqrt(period));

                double wmaFull = GetWMA(period, shift);
                double wmaHalf = GetWMA(halfPeriod, shift);

                double rawHMA = 2 * wmaHalf - wmaFull;

                return GetWMA(sqrtPeriod, shift, rawHMA);
            }

            private double GetWMA(int length, int shift = 0, double? overrideValue = null)
            {
                if (hdmInd == null || hdmInd.Count <= shift + length - 1)
                    return double.NaN;

                double sumWeights = 0;
                double weightedPrice = 0;
                int weight = length;

                for (int i = 0; i < length; i++)
                {
                    int barIndex = shift + (length - 1 - i);
                    if (barIndex < 0 || barIndex >= hdmInd.Count)
                        return double.NaN;

                    double price = overrideValue ?? hdmInd.Close(barIndex);

                    weightedPrice += price * weight;
                    sumWeights += weight;
                    weight--;
                }

                return (sumWeights == 0) ? double.NaN : weightedPrice / sumWeights;
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
            HmaBarPeriod = Period.SECOND30;
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

            _hdmHma = CurrentSymbol.GetHistory(new HistoryRequestParameters
            {
                Symbol = CurrentSymbol,
                FromTime = _hmaStartPoint,
                Aggregation = new HistoryAggregationTime(HmaBarPeriod, CurrentSymbol.HistoryType)
            });
            _hma = new HMAHelper(_hdmHma, HmaFastPeriod, HmaSlowPeriod);

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
            Log($"│  Entry trigger: HMA crossover ({HmaBarPeriod} bars, fast={HmaFastPeriod} slow={HmaSlowPeriod}), traded WITH the trend  signal expiry={HmaSignalExpirySeconds}s  bars loaded={_hdmHma?.Count ?? 0}", StrategyLoggingLevel.Info);
            Log($"│  Trades → {_tradeCsv}", StrategyLoggingLevel.Info);
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

            foreach (var kv in _connectionHandlers) kv.Key.StateChanged -= kv.Value;
            _connectionHandlers.Clear();
            Core.Instance.Connections.ConnectionAdded -= OnConnectionAdded;
            Core.Instance.Connections.ConnectionRemoved -= OnConnectionRemoved;

            _entryLimitTimer?.Stop(); _entryLimitTimer?.Dispose();
            _connectionWatchdog?.Stop(); _connectionWatchdog?.Dispose(); _connectionWatchdog = null;
            _flushTimer?.Stop(); _flushTimer?.Dispose(); _flushTimer = null;

            _hdmHma?.Dispose(); _hdmHma = null; _hma = null;

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

            // 2. Re-evaluate the HMA crossover (cheap; only changes when a bar closes)
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
                if (_pendingSignalSide == null) { GateLog("no HMA crossover signal"); return; }

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
        // ENTRY SIGNAL GENERATION — HMA CROSSOVER, TRADED WITH THE TREND
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
        // fills, is reversed, or expires via HmaSignalExpirySeconds.
        protected void UpdateEntrySignal()
        {
            if (_hma == null || _hdmHma == null || _hdmHma.Count < HmaSlowPeriod + 3) return;

            double fast1 = _hma.Fast(1), slow1 = _hma.Slow(1);
            double fast2 = _hma.Fast(2), slow2 = _hma.Slow(2);
            if (double.IsNaN(fast1) || double.IsNaN(slow1) || double.IsNaN(fast2) || double.IsNaN(slow2)) return;

            if (_pendingSignalSide != null && HmaSignalExpirySeconds > 0
                && (DateTime.Now - _pendingSignalTime).TotalSeconds > HmaSignalExpirySeconds)
            {
                Log($"⌛ HMA signal expired — {_pendingSignalSide} unfilled for {HmaSignalExpirySeconds}s", StrategyLoggingLevel.Info);
                _pendingSignalSide = null;
            }

            bool crossedUp = fast2 < slow2 && fast1 > slow1;
            bool crossedDown = fast2 > slow2 && fast1 < slow1;

            if (crossedUp && _pendingSignalSide != Side.Buy)
            {
                _pendingSignalSide = Side.Buy;
                _pendingSignalTime = DateTime.Now;
                Log($"📈 HMA crossover UP  fast={fast1:F5} slow={slow1:F5} — going long with the trend", StrategyLoggingLevel.Info);
            }
            else if (crossedDown && _pendingSignalSide != Side.Sell)
            {
                _pendingSignalSide = Side.Sell;
                _pendingSignalTime = DateTime.Now;
                Log($"📉 HMA crossover DOWN  fast={fast1:F5} slow={slow1:F5} — going short with the trend", StrategyLoggingLevel.Info);
            }
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
                            .FirstOrDefault(p => p.Account.Equals(CurrentAccount)
                                              && p.Symbol.Equals(CurrentSymbol)
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
                if (!pos.Account.Equals(CurrentAccount)) return;
                if (!pos.Symbol.Equals(CurrentSymbol)) return;
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

                // Only the broker's two bracket legs can close a position now, so the
                // realized gross result identifies which one filled. A flat/zero gross
                // is reported as-is rather than guessed at.
                double gross = pos.GrossPnL?.Value ?? 0;
                string exitReason = gross > 0 ? "TakeProfit" : gross < 0 ? "StopLoss" : "Flat";

                double netPnL = CurrentAccount.Balance - StartingBalance;
                WriteTrade(pos, netPnL, exitReason);

                Log($"🏁 Closed {pos.Side}  reason={exitReason}  " +
                    $"Gross={gross:F2}  Net={netPnL:F2}  MFE={_positionHighWater:F1}t MAE={_positionLowWater:F1}t", StrategyLoggingLevel.Info);

                _hasOpenPosition = false;
                _openPosition = null;
                _entrySent = false;
                _entryPrice = double.NaN;
                _lastCloseTimestamp = System.Diagnostics.Stopwatch.GetTimestamp();
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

                _hdmHma?.Dispose();
                _hdmHma = CurrentSymbol.GetHistory(new HistoryRequestParameters
                {
                    Symbol = CurrentSymbol,
                    FromTime = _hmaStartPoint,
                    Aggregation = new HistoryAggregationTime(HmaBarPeriod, CurrentSymbol.HistoryType)
                });
                _hma = new HMAHelper(_hdmHma, HmaFastPeriod, HmaSlowPeriod);
                Log("✅ HMA history reinitialized after reconnect", StrategyLoggingLevel.Info);
            }

            lock (_positionLock)
            {
                foreach (var p in Core.Instance.Positions)
                {
                    if (_myPositionIds.Contains(p.Id) && p.Account.Equals(CurrentAccount))
                    {
                        _openPosition = p; _entryPrice = p.OpenPrice; _hasOpenPosition = true;
                        Log($"🔄 Reconnect: re-attached live position {p.Id}", StrategyLoggingLevel.Info);
                    }
                }
            }

            Core.Instance.PositionAdded -= OnPositionAdded; Core.Instance.PositionAdded += OnPositionAdded;
            Core.Instance.PositionRemoved -= OnPositionRemoved; Core.Instance.PositionRemoved += OnPositionRemoved;
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
        // CSV LOGGING
        // ======================================================
        // TODO: Add strategy-specific columns to EnsureHeaders and WriteTrade
        // For example:
        //   EnsureHeaders: add "indicatorValue,entrySignal,exitSignal" etc.
        //   WriteTrade: add string.Format values for those fields

        private void EnsureHeaders()
        {
            try
            {
                if (!File.Exists(_tradeCsv) || new FileInfo(_tradeCsv).Length == 0)
                    File.AppendAllText(_tradeCsv,
                        "openTime,closeTime,side,entryPrice,exitReason,mfeTicks,maeTicks," +
                        "grossPnL,netPnL,fillLatencyMs,entryBid,entryAsk,spreadAtFillTicks," +
                        "exitBid,exitAsk" + Environment.NewLine);
            }
            catch (Exception ex) { Log($"CSV header error: {ex.Message}", StrategyLoggingLevel.Error); }
        }

        private void WriteTrade(Position pos, double netPnL, string exitReason)
        {
            string row = string.Join(",",
                _positionOpenTime.ToString("yyyy-MM-dd HH:mm:ss.fff"),
                DateTime.Now.ToString("yyyy-MM-dd HH:mm:ss.fff"),
                pos.Side,
                _entryPrice.ToString("F5"),
                string.IsNullOrEmpty(exitReason) ? "unknown" : exitReason,
                _positionHighWater.ToString("F1"),
                _positionLowWater.ToString("F1"),
                (pos.GrossPnL?.Value ?? 0).ToString("F2"),
                netPnL.ToString("F2"),
                (_fillLatencySec * 1000).ToString("F0"),
                (double.IsNaN(_entryBidAtFill) ? "" : _entryBidAtFill.ToString("F5")),
                (double.IsNaN(_entryAskAtFill) ? "" : _entryAskAtFill.ToString("F5")),
                (double.IsNaN(_entryBidAtFill) ? "" : ((_entryAskAtFill - _entryBidAtFill) / _tickSize).ToString("F2")),
                (double.IsNaN(_bid) ? "" : _bid.ToString("F5")),
                (double.IsNaN(_ask) ? "" : _ask.ToString("F5")));
            lock (_csvLock) { _tradeBuf.Add(row); }
        }

        private void Flush()
        {
            try
            {
                List<string> trades = null;
                lock (_csvLock)
                {
                    if (_tradeBuf.Count > 0) { trades = new List<string>(_tradeBuf); _tradeBuf.Clear(); }
                }
                if (trades != null) File.AppendAllLines(_tradeCsv, trades);
            }
            catch (Exception ex) { Log($"CSV flush error: {ex.Message}", StrategyLoggingLevel.Error); }
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
                ( 9, 45, 12, 30),   // 9:30–10:30 ET
                //(15, 30, 16,  0),   // 3:30–4:00 ET (optional second window)
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