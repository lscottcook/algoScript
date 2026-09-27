using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Metrics;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text.Json;
using System.Text.Json.Serialization;
using System.Threading.Tasks;
using TradingPlatform.BusinessLayer;

namespace strategyTesting
{
    /// <summary>
    /// Quantower implementation of the frozen HG movement candidate.
    ///
    /// Frozen definition:
    ///   1. Detect a five-tick movement from a locally tracked price extreme.
    ///   2. Preserve the movement direction.
    ///   3. Wait ten seconds after activation.
    ///   4. Record the executable quote and observable Quantower state.
    ///   5. Follow TP 15 versus SL 10 for up to 600 seconds.
    ///   6. Enforce a five-minute activation cooldown.
    ///
    /// Shadow logging is the default. Paper orders require two explicit inputs:
    /// EnablePaperOrders=true and PaperConfirmation="PAPER ONLY".
    /// </summary>
    public class strategyTesting : Strategy, ICurrentAccount, ICurrentSymbol
    {
        [InputParameter("Symbol", 0)]
        public Symbol CurrentSymbol { get; set; }

        [InputParameter("Account (identity only; no orders are sent)", 1)]
        public Account CurrentAccount { get; set; }

        [InputParameter("Activation ticks", 2, 1, 50, 1, 0)]
        public int ActivationTicks = 5;

        [InputParameter("Checkpoint delay (seconds)", 3, 1, 120, 1, 0)]
        public int CheckpointSeconds = 10;

        [InputParameter("Take profit ticks", 4, 1, 100, 1, 0)]
        public int TakeProfitTicks = 15;

        [InputParameter("Stop loss ticks", 5, 1, 100, 1, 0)]
        public int StopLossTicks = 10;

        [InputParameter("Maximum hold (seconds)", 6, 30, 1800, 30, 0)]
        public int EvaluationSeconds = 600;

        [InputParameter("Activation cooldown (seconds)", 7, 1, 1800, 1, 0)]
        public int ActivationCooldownSeconds = 300;

        [InputParameter("Checkpoint timer interval (ms)", 8, 10, 250, 5, 0)]
        public int CheckpointTimerMs = 25;

        [InputParameter("DOM levels", 9, 1, 20, 1, 0)]
        public int DomLevels = 10;

        [InputParameter("Exclude 4:00-6:00 PM ET", 10)]
        public bool ExcludeClosedPeriod = true;

        [InputParameter("Frozen model JSON path", 11)]
        public string FrozenModelPath = @"C:\Users\Administrator\Documents\algoScript\hg_frozen_directional_model.json";

        [InputParameter("Enable PAPER orders", 12)]
        public bool EnablePaperOrders = true;

        [InputParameter("Paper confirmation text", 13)]
        public string PaperConfirmation = "PAPER ONLY";

        [InputParameter("Paper quantity", 14, 1, 10, 1, 0)]
        public int PaperQuantity = 1;

        [InputParameter("Starting Balance", 14)] 
        public double StartingBalance { get; set; }



        private readonly int[] _featureWindows = { 5, 10, 30, 60 };
        private readonly object _sync = new object();
        private readonly object _csvSync = new object();
        private readonly object _flushIoLock = new object();
        private readonly List<string> _checkpointBuffer = new List<string>();
        private readonly List<string> _episodeBuffer = new List<string>();
        private readonly List<PendingActivation> _pending = new List<PendingActivation>();
        private readonly List<VirtualEpisode> _episodes = new List<VirtualEpisode>();
        private readonly Queue<TimedTrade> _trades = new Queue<TimedTrade>();
        private readonly Queue<FlowEvent> _flowEvents = new Queue<FlowEvent>();
        private readonly Dictionary<string, OrderState> _orders = new Dictionary<string, OrderState>();

        private string _runId;
        private long _activationSequence;
        private double _tickSize;
        private bool _stopping;
        private bool _closedState;
        private bool _rebindInProgress;
        private bool _lastKnownConnected = true;
        private DateTime _dataReadyAfterUtc = DateTime.MinValue;
        private readonly Dictionary<Connection, EventHandler<ConnectionStateChangedEventArgs>>
            _connectionHandlers = new Dictionary<Connection, EventHandler<ConnectionStateChangedEventArgs>>();
        private System.Timers.Timer _connectionWatchdog;

        private DateTime _lastTradeReceiveUtc = DateTime.MinValue;
        private DateTime _lastTradeEventUtc = DateTime.MinValue;
        private DateTime _lastQuoteReceiveUtc = DateTime.MinValue;
        private DateTime _lastQuoteEventUtc = DateTime.MinValue;
        private double _lastTradePrice = double.NaN;
        private double _bid = double.NaN;
        private double _ask = double.NaN;
        private List<Level2Item> _bids;
        private List<Level2Item> _asks;

        // State for the next independent five-tick activation search.
        private bool _searchInitialized;
        private double _searchLow = double.NaN;
        private double _searchHigh = double.NaN;
        private DateTime _searchLowUtc = DateTime.MinValue;
        private DateTime _searchHighUtc = DateTime.MinValue;
        private DateTime _nextActivationAllowedUtc = DateTime.MinValue;

        private string _checkpointCsv;
        private string _episodeCsv;
        private System.Timers.Timer _checkpointTimer;
        private System.Timers.Timer _flushTimer;
        private FrozenModelSpec _modelSpec;
        private Position _paperPosition;
        private DateTime _paperPositionOpenedUtc = DateTime.MinValue;
        private bool _paperEntryPending;
        private bool _paperTradingBlockedAfterReconnect;
        private Side _paperPendingSide;
        private string _paperSignalId = "";
        private DateTime _nextReconcileUtc = DateTime.MinValue;

        private sealed class TimedTrade
        {
            public DateTime ReceiveUtc;
            public double Price;
            public double Size;
        }

        private sealed class FlowEvent
        {
            public DateTime ReceiveUtc;
            public string Action;
            public string Side;
            public double Size;
        }

        private sealed class OrderState
        {
            public string Side;
            public double Size;
        }

        private sealed class PipelineSpec
        {
            [JsonPropertyName("input_features")] public List<string> InputFeatures { get; set; }
            [JsonPropertyName("imputer_statistics")] public List<double?> ImputerStatistics { get; set; }
            [JsonPropertyName("scaler_mean")] public List<double> ScalerMean { get; set; }
            [JsonPropertyName("scaler_scale")] public List<double> ScalerScale { get; set; }
            [JsonPropertyName("coefficient")] public List<double> Coefficient { get; set; }
            [JsonPropertyName("intercept")] public double Intercept { get; set; }
        }

        private sealed class ThresholdSpec
        {
            [JsonPropertyName("resolution_probability")] public double ResolutionProbability { get; set; }
            [JsonPropertyName("direction_probability")] public double DirectionProbability { get; set; }
        }

        private sealed class ActivationSpec
        {
            [JsonPropertyName("ticks")] public int Ticks { get; set; }
            [JsonPropertyName("cooldown_seconds")] public int CooldownSeconds { get; set; }
        }

        private sealed class ExitSpec
        {
            [JsonPropertyName("take_profit_ticks")] public int TakeProfitTicks { get; set; }
            [JsonPropertyName("stop_loss_ticks")] public int StopLossTicks { get; set; }
            [JsonPropertyName("maximum_hold_seconds")] public int MaximumHoldSeconds { get; set; }
        }

        private sealed class FrozenModelSpec
        {
            [JsonPropertyName("model_version")] public string ModelVersion { get; set; }
            [JsonPropertyName("instrument")] public string Instrument { get; set; }
            [JsonPropertyName("tick_size")] public double TickSize { get; set; }
            [JsonPropertyName("activation")] public ActivationSpec Activation { get; set; }
            [JsonPropertyName("checkpoint_seconds")] public int CheckpointSeconds { get; set; }
            [JsonPropertyName("feature_windows_seconds")] public List<int> FeatureWindowsSeconds { get; set; }
            [JsonPropertyName("exit")] public ExitSpec Exit { get; set; }
            [JsonPropertyName("resolution_model")] public PipelineSpec ResolutionModel { get; set; }
            [JsonPropertyName("direction_model")] public PipelineSpec DirectionModel { get; set; }
            [JsonPropertyName("thresholds")] public ThresholdSpec Thresholds { get; set; }
        }

        private sealed class PendingActivation
        {
            public string ActivationId;
            public Side Side;
            public DateTime AnchorUtc;
            public DateTime ActivationUtc;
            public DateTime CheckpointDueUtc;
            public double AnchorPrice;
            public double ActivationPrice;
        }

        private sealed class WindowFeatures
        {
            public int TradeCount;
            public double TradeVolume;
            public double NetTicks;
        }

        private sealed class VirtualEpisode
        {
            public string EpisodeId;
            public string ActivationId;
            public Side Side;
            public DateTime AnchorUtc;
            public DateTime ActivationUtc;
            public DateTime CheckpointDueUtc;
            public DateTime CheckpointUtc;
            public DateTime FirstMarketUpdateUtc;
            public string FirstMarketUpdateType = "";
            public double AnchorPrice;
            public double ActivationPrice;
            public double CheckpointReferencePrice;
            public double EntryPrice;
            public double Bid;
            public double Ask;
            public double CheckpointTimerLagMs;
            public double QuoteAgeMs;
            public double EntrySpreadTicks;
            public double NextMarketUpdateDelayMs = double.NaN;
            public double MfeTicks;
            public double MaeTicks;
            public double SecondsToTp = double.NaN;
            public double SecondsToSl = double.NaN;
            public double FinalSignedTicks = double.NaN;
            public string ModelVersion = "";
            public double ResolutionProbability = double.NaN;
            public double DirectionProbability = double.NaN;
            public bool Qualified;
        }

        public strategyTesting()
        {
            Name = "strategyTesting";
            Description = "Frozen two-stage MBO candidate. Shadow by default; explicitly gated paper orders.";
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

            ActivationTicks = Math.Max(1, ActivationTicks);
            CheckpointSeconds = Math.Max(1, CheckpointSeconds);
            TakeProfitTicks = Math.Max(1, TakeProfitTicks);
            StopLossTicks = Math.Max(1, StopLossTicks);
            EvaluationSeconds = Math.Max(30, EvaluationSeconds);
            ActivationCooldownSeconds = Math.Max(1, ActivationCooldownSeconds);
            CheckpointTimerMs = Math.Max(10, CheckpointTimerMs);
            PaperQuantity = Math.Max(1, PaperQuantity);

            if (!LoadAndValidateModel()) return;

            _runId = Guid.NewGuid().ToString("N");
            string downloads = Path.Combine(
                Environment.GetFolderPath(Environment.SpecialFolder.UserProfile), "Downloads");
            _checkpointCsv = Path.Combine(downloads, "strategyTesting_frozen_checkpoints.csv");
            _episodeCsv = Path.Combine(downloads, "strategyTesting_frozen_episodes.csv");
            EnsureHeaders();

            SubscribeMarketData();
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

            // Wait for a complete longest feature window before allowing the
            // first activation. This prevents startup/reconnect partial windows
            // from being silently replaced by training medians.
            _dataReadyAfterUtc = DateTime.UtcNow.AddSeconds(_featureWindows.Max());

            _checkpointTimer = new System.Timers.Timer(CheckpointTimerMs) { AutoReset = true };
            _checkpointTimer.Elapsed += (s, e) => OnCheckpointTimer();
            _checkpointTimer.Start();

            _flushTimer = new System.Timers.Timer(5000) { AutoReset = true };
            _flushTimer.Elapsed += (s, e) => Flush();
            _flushTimer.Start();

            Log($"Frozen candidate started for {CurrentSymbol.Name}. Mode={(EnablePaperOrders ? "PAPER REQUESTED" : "SHADOW")}.", StrategyLoggingLevel.Info);
            Log($"Activation={ActivationTicks}, checkpoint={CheckpointSeconds}s, TP/SL={TakeProfitTicks}/{StopLossTicks}, hold={EvaluationSeconds}s, cooldown={ActivationCooldownSeconds}s.", StrategyLoggingLevel.Info);
            Log($"Model={_modelSpec.ModelVersion}; resolution cutoff={_modelSpec.Thresholds.ResolutionProbability:F6}; direction cutoff={_modelSpec.Thresholds.DirectionProbability:F6}.", StrategyLoggingLevel.Info);
            Log($"Paper orders={(EnablePaperOrders ? "REQUESTED" : "DISABLED")}. They require confirmation text PAPER ONLY.", StrategyLoggingLevel.Info);
            Log($"Checkpoints: {_checkpointCsv}", StrategyLoggingLevel.Info);
            Log($"Episodes: {_episodeCsv}", StrategyLoggingLevel.Info);
        }

        protected override void OnStop()
        {
            _stopping = true;
            UnsubscribeMarketData();
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

            _checkpointTimer?.Stop();
            _checkpointTimer?.Dispose();
            _flushTimer?.Stop();
            _flushTimer?.Dispose();

            lock (_sync)
            {
                DateTime now = DateTime.UtcNow;
                foreach (VirtualEpisode episode in _episodes.ToList())
                    FinalizeEpisode(episode, now, "STRATEGY_STOP", true);
                _episodes.Clear();
                _pending.Clear();
            }
            Flush();
            Log("Frozen candidate stopped. Existing paper positions are not automatically closed by stopping the strategy.", StrategyLoggingLevel.Info);
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

        private void SubscribeMarketData()
        {
            if (CurrentSymbol == null) return;
            // Remove first so repeated reconnect callbacks cannot create duplicate handlers.
            CurrentSymbol.NewLast -= OnNewLast;
            CurrentSymbol.NewQuote -= OnNewQuote;
            CurrentSymbol.NewLevel2 -= OnNewLevel2;
            CurrentSymbol.NewLast += OnNewLast;
            CurrentSymbol.NewQuote += OnNewQuote;
            CurrentSymbol.NewLevel2 += OnNewLevel2;
        }

        private void UnsubscribeMarketData()
        {
            if (CurrentSymbol == null) return;
            CurrentSymbol.NewLast -= OnNewLast;
            CurrentSymbol.NewQuote -= OnNewQuote;
            CurrentSymbol.NewLevel2 -= OnNewLevel2;
        }

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
                ResetAfterDataGap("DATA_DISCONNECT");
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
            bool connected = Core.Instance.Connections.All.Any(
                c => c.State == ConnectionState.Connected);
            if (!connected && _lastKnownConnected)
            {
                _lastKnownConnected = false;
                Log("Connection watchdog: no connected data connection.", StrategyLoggingLevel.Error);
                ResetAfterDataGap("WATCHDOG_DISCONNECT");
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
                    UnsubscribeMarketData();
                    CurrentSymbol = Core.GetSymbol(symbolInfo);
                    if (CurrentSymbol == null)
                        throw new InvalidOperationException("Could not reacquire the selected symbol.");
                    _tickSize = CurrentSymbol.TickSize;
                    SubscribeMarketData();

                    if (!string.IsNullOrEmpty(accountId))
                    {
                        Account account = Core.Instance.Accounts.FirstOrDefault(a => a.Id == accountId);
                        if (account != null) CurrentAccount = account;
                        else Log("Reconnect warning: selected account was not reacquired.",
                            StrategyLoggingLevel.Error);
                    }

                    Core.Instance.PositionAdded -= OnPositionAdded;
                    Core.Instance.PositionRemoved -= OnPositionRemoved;
                    Core.Instance.PositionAdded += OnPositionAdded;
                    Core.Instance.PositionRemoved += OnPositionRemoved;
                    ResetTransientMarketState();
                    _dataReadyAfterUtc = DateTime.UtcNow.AddSeconds(_featureWindows.Max());
                    Log($"Reattached {CurrentSymbol.Name}; signal warmup ends at {_dataReadyAfterUtc:O}.",
                        StrategyLoggingLevel.Info);
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

        private void ResetAfterDataGap(string reason)
        {
            lock (_sync)
            {
                if (EnablePaperOrders && (_paperEntryPending || _paperPosition != null))
                {
                    _paperTradingBlockedAfterReconnect = true;
                    Log("Paper entries blocked after connection loss. Restart the strategy after reconciling the account and orders.",
                        StrategyLoggingLevel.Error);
                }
                DateTime now = DateTime.UtcNow;
                foreach (VirtualEpisode episode in _episodes.ToList())
                    FinalizeEpisode(episode, now, reason, true);
                _episodes.Clear();
                ResetTransientMarketState();
                _dataReadyAfterUtc = DateTime.MaxValue;
            }
        }

        private void ResetTransientMarketState()
        {
            _pending.Clear();
            _trades.Clear();
            _flowEvents.Clear();
            _orders.Clear();
            _bids = null;
            _asks = null;
            _bid = _ask = _lastTradePrice = double.NaN;
            _lastTradeReceiveUtc = _lastTradeEventUtc = DateTime.MinValue;
            _lastQuoteReceiveUtc = _lastQuoteEventUtc = DateTime.MinValue;
            _searchInitialized = false;
            _nextActivationAllowedUtc = DateTime.MinValue;
        }

        private void OnNewQuote(Symbol symbol, Quote quote)
        {
            if (_stopping || quote == null) return;
            DateTime receiveUtc = DateTime.UtcNow;
            DateTime eventUtc = TryReadUtcTimestamp(quote);
            lock (_sync)
            {
                _bid = quote.Bid;
                _ask = quote.Ask;
                _lastQuoteReceiveUtc = receiveUtc;
                _lastQuoteEventUtc = eventUtc;
                MarkFirstMarketUpdate(receiveUtc, "QUOTE");
            }
        }

        private void OnNewLevel2(Symbol symbol, Level2Quote level2, DOMQuote dom)
        {
            if (_stopping || level2 == null) return;
            DateTime receiveUtc = DateTime.UtcNow;
            lock (_sync)
            {
                HandleClosedPeriod(receiveUtc);
                if (IsClosedEt(receiveUtc)) return;

                string id = Convert.ToString(level2.Id, CultureInfo.InvariantCulture) ?? "";
                string side = level2.PriceType.ToString().IndexOf("Bid", StringComparison.OrdinalIgnoreCase) >= 0
                    ? "B" : "A";
                OrderState old = null;
                bool existed = !string.IsNullOrEmpty(id) && _orders.TryGetValue(id, out old);
                string typeText = level2.Type.ToString();
                bool closed = level2.Closed
                    || typeText.IndexOf("Delete", StringComparison.OrdinalIgnoreCase) >= 0
                    || typeText.IndexOf("Remove", StringComparison.OrdinalIgnoreCase) >= 0
                    || typeText.IndexOf("Cancel", StringComparison.OrdinalIgnoreCase) >= 0;
                string action = closed ? "cancel" : existed ? "modify" : "add";
                double eventSize = level2.Size > 0 ? level2.Size : (existed ? old.Size : 0);
                _flowEvents.Enqueue(new FlowEvent
                {
                    ReceiveUtc = receiveUtc,
                    Action = action,
                    Side = side,
                    Size = Math.Max(0, eventSize)
                });

                if (!string.IsNullOrEmpty(id))
                {
                    if (closed) _orders.Remove(id);
                    else _orders[id] = new OrderState { Side = side, Size = Math.Max(0, level2.Size) };
                }
                TrimFlowEvents(receiveUtc);
            }
        }

        private void OnNewLast(Symbol symbol, Last last)
        {
            if (_stopping || last == null || last.Price <= 0) return;
            DateTime receiveUtc = DateTime.UtcNow;
            DateTime eventUtc = TryReadUtcTimestamp(last);
            RefreshDom();

            lock (_sync)
            {
                HandleClosedPeriod(receiveUtc);
                _lastTradeReceiveUtc = receiveUtc;
                _lastTradeEventUtc = eventUtc;
                _lastTradePrice = last.Price;

                if (IsClosedEt(receiveUtc)) return;

                _trades.Enqueue(new TimedTrade
                {
                    ReceiveUtc = receiveUtc,
                    Price = last.Price,
                    Size = last.Size > 0 ? last.Size : 0
                });
                if (last.AggressorFlag != AggressorFlag.None)
                {
                    _flowEvents.Enqueue(new FlowEvent
                    {
                        ReceiveUtc = receiveUtc,
                        Action = "trade",
                        // An aggressive buy executes ask-side liquidity; an aggressive sell executes bid-side liquidity.
                        Side = last.AggressorFlag == AggressorFlag.Buy ? "A" : "B",
                        Size = Math.Max(0, last.Size)
                    });
                }
                TrimTrades(receiveUtc);
                TrimFlowEvents(receiveUtc);
                MarkFirstMarketUpdate(receiveUtc, "TRADE");
                UpdateEpisodes(receiveUtc, last.Price);
                DetectActivation(receiveUtc, last.Price);
            }
        }

        private void OnCheckpointTimer()
        {
            if (_stopping) return;
            DateTime nowUtc = DateTime.UtcNow;
            lock (_sync)
            {
                if (_stopping) return;
                HandleClosedPeriod(nowUtc);
                if (IsClosedEt(nowUtc)) return;
                ActivateDueCheckpoints(nowUtc);
                FinalizeExpiredEpisodes(nowUtc);
                HandlePaperTimeExit(nowUtc);
                ReconcileOrphanedPositions(nowUtc);
            }
        }

        private void DetectActivation(DateTime nowUtc, double price)
        {
            if (nowUtc < _dataReadyAfterUtc)
            {
                // Keep the activation anchor fresh during warmup, but never
                // evaluate a model with an incomplete 60-second feature window.
                ResetSearch(price, nowUtc);
                return;
            }
            if (nowUtc < _nextActivationAllowedUtc) return;
            if (!_searchInitialized)
            {
                ResetSearch(price, nowUtc);
                return;
            }

            if (price < _searchLow)
            {
                _searchLow = price;
                _searchLowUtc = nowUtc;
            }
            if (price > _searchHigh)
            {
                _searchHigh = price;
                _searchHighUtc = nowUtc;
            }

            double upTicks = Ticks(price - _searchLow);
            double downTicks = Ticks(_searchHigh - price);
            if (upTicks >= ActivationTicks)
                RegisterActivation(Side.Buy, _searchLowUtc, nowUtc, _searchLow, price);
            else if (downTicks >= ActivationTicks)
                RegisterActivation(Side.Sell, _searchHighUtc, nowUtc, _searchHigh, price);
        }

        private void RegisterActivation(
            Side side, DateTime anchorUtc, DateTime activationUtc,
            double anchorPrice, double activationPrice)
        {
            string activationId = _runId + "-A" + (++_activationSequence).ToString("D8");
            _pending.Add(new PendingActivation
            {
                ActivationId = activationId,
                Side = side,
                AnchorUtc = anchorUtc,
                ActivationUtc = activationUtc,
                CheckpointDueUtc = activationUtc.AddSeconds(CheckpointSeconds),
                AnchorPrice = anchorPrice,
                ActivationPrice = activationPrice
            });
            _nextActivationAllowedUtc = activationUtc.AddSeconds(ActivationCooldownSeconds);
            _searchInitialized = false;
        }

        private void ActivateDueCheckpoints(DateTime nowUtc)
        {
            foreach (PendingActivation activation in _pending.ToList())
            {
                if (nowUtc < activation.CheckpointDueUtc) continue;
                if (double.IsNaN(_lastTradePrice) || _lastTradePrice <= 0) continue;

                double entryPrice = activation.Side == Side.Buy ? _ask : _bid;
                if (double.IsNaN(entryPrice) || entryPrice <= 0) continue;

                var episode = new VirtualEpisode
                {
                    EpisodeId = activation.ActivationId + "-E",
                    ActivationId = activation.ActivationId,
                    Side = activation.Side,
                    AnchorUtc = activation.AnchorUtc,
                    ActivationUtc = activation.ActivationUtc,
                    CheckpointDueUtc = activation.CheckpointDueUtc,
                    CheckpointUtc = nowUtc,
                    AnchorPrice = activation.AnchorPrice,
                    ActivationPrice = activation.ActivationPrice,
                    CheckpointReferencePrice = _lastTradePrice,
                    EntryPrice = entryPrice,
                    Bid = _bid,
                    Ask = _ask,
                    CheckpointTimerLagMs = Math.Max(0, (nowUtc - activation.CheckpointDueUtc).TotalMilliseconds),
                    QuoteAgeMs = _lastQuoteReceiveUtc == DateTime.MinValue
                        ? double.NaN : Math.Max(0, (nowUtc - _lastQuoteReceiveUtc).TotalMilliseconds),
                    EntrySpreadTicks = Ticks(_ask - _bid),
                    MfeTicks = 0,
                    MaeTicks = 0
                };
                Dictionary<string, double> features = BuildDirectionalFeatures(
                    activation.ActivationUtc, nowUtc,
                    activation.Side == Side.Buy ? 1 : -1,
                    _modelSpec.DirectionModel.InputFeatures);
                episode.ModelVersion = _modelSpec.ModelVersion;
                episode.ResolutionProbability = Score(_modelSpec.ResolutionModel, features);
                episode.DirectionProbability = Score(_modelSpec.DirectionModel, features);
                episode.Qualified = episode.ResolutionProbability >= _modelSpec.Thresholds.ResolutionProbability
                    && episode.DirectionProbability >= _modelSpec.Thresholds.DirectionProbability;

                QueueCheckpointRow(activation, episode, nowUtc, features);
                if (episode.Qualified)
                {
                    _episodes.Add(episode);
                    TryPlacePaperOrder(episode);
                }
                _pending.Remove(activation);
            }
        }

        private void UpdateEpisodes(DateTime nowUtc, double tradePrice)
        {
            foreach (VirtualEpisode episode in _episodes.ToList())
            {
                double elapsed = (nowUtc - episode.CheckpointUtc).TotalSeconds;
                if (elapsed < 0) continue;
                double signedTicks = Ticks(tradePrice - episode.EntryPrice)
                    * (episode.Side == Side.Buy ? 1.0 : -1.0);
                episode.MfeTicks = Math.Max(episode.MfeTicks, signedTicks);
                episode.MaeTicks = Math.Min(episode.MaeTicks, signedTicks);
                episode.FinalSignedTicks = signedTicks;

                if (double.IsNaN(episode.SecondsToTp) && signedTicks >= TakeProfitTicks)
                    episode.SecondsToTp = elapsed;
                if (double.IsNaN(episode.SecondsToSl) && signedTicks <= -StopLossTicks)
                    episode.SecondsToSl = elapsed;
            }
        }

        private Dictionary<string, double> BuildDirectionalFeatures(
            DateTime activationUtc, DateTime checkpointUtc, int direction,
            IEnumerable<string> featureNames)
        {
            var result = new Dictionary<string, double>();
            foreach (string feature in featureNames)
            {
                string action;
                DateTime cutoff;
                if (feature.StartsWith("directional_since_activation_", StringComparison.Ordinal))
                {
                    action = feature.Substring("directional_since_activation_".Length)
                        .Replace("_aligned_share", "");
                    cutoff = activationUtc;
                }
                else
                {
                    string remainder = feature.Substring("directional_".Length);
                    int marker = remainder.IndexOf("s_", StringComparison.Ordinal);
                    int seconds = int.Parse(remainder.Substring(0, marker), CultureInfo.InvariantCulture);
                    action = remainder.Substring(marker + 2).Replace("_aligned_share", "");
                    cutoff = checkpointUtc.AddSeconds(-seconds + 1);
                }

                double bid = 0, ask = 0;
                foreach (FlowEvent e in _flowEvents)
                {
                    if (e.ReceiveUtc < cutoff || e.ReceiveUtc > checkpointUtc || e.Action != action) continue;
                    if (e.Side == "B") bid += e.Size;
                    else if (e.Side == "A") ask += e.Size;
                }
                double total = bid + ask;
                double value = total > 0 ? (bid - ask) / total : double.NaN;
                int actionSign = action == "trade" || action == "cancel" ? -direction : direction;
                result[feature] = double.IsNaN(value) ? double.NaN : actionSign * value;
            }
            return result;
        }

        private static double Score(PipelineSpec model, Dictionary<string, double> features)
        {
            int n = model.InputFeatures.Count;
            if (model.ImputerStatistics.Count != n || model.ScalerMean.Count != n
                || model.ScalerScale.Count != n || model.Coefficient.Count != n)
                throw new InvalidOperationException("Frozen model array lengths do not match its feature count.");

            double z = model.Intercept;
            for (int i = 0; i < n; i++)
            {
                double value = features.TryGetValue(model.InputFeatures[i], out double x) ? x : double.NaN;
                if (double.IsNaN(value) || double.IsInfinity(value))
                {
                    double? replacement = model.ImputerStatistics[i];
                    if (!replacement.HasValue) throw new InvalidOperationException(
                        "No imputation value for " + model.InputFeatures[i]);
                    value = replacement.Value;
                }
                double scale = model.ScalerScale[i];
                double standardized = scale > 0 ? (value - model.ScalerMean[i]) / scale : 0;
                z += standardized * model.Coefficient[i];
            }
            if (z >= 0) return 1.0 / (1.0 + Math.Exp(-z));
            double ez = Math.Exp(z);
            return ez / (1.0 + ez);
        }

        private void FinalizeExpiredEpisodes(DateTime nowUtc)
        {
            foreach (VirtualEpisode episode in _episodes.ToList())
            {
                if ((nowUtc - episode.CheckpointUtc).TotalSeconds < EvaluationSeconds) continue;
                FinalizeEpisode(episode, episode.CheckpointUtc.AddSeconds(EvaluationSeconds), "TIME_LIMIT", false);
                _episodes.Remove(episode);
            }
        }

        private void FinalizeEpisode(VirtualEpisode e, DateTime endUtc, string endReason, bool incomplete)
        {
            string outcome;
            if (!double.IsNaN(e.SecondsToTp) &&
                (double.IsNaN(e.SecondsToSl) || e.SecondsToTp < e.SecondsToSl)) outcome = "TP_FIRST";
            else if (!double.IsNaN(e.SecondsToSl) &&
                (double.IsNaN(e.SecondsToTp) || e.SecondsToSl < e.SecondsToTp)) outcome = "SL_FIRST";
            else if (!double.IsNaN(e.SecondsToTp) && e.SecondsToTp == e.SecondsToSl) outcome = "AMBIGUOUS";
            else outcome = "UNRESOLVED";

            var values = new List<string>
            {
                _runId, e.EpisodeId, e.ActivationId, CsvTime(e.AnchorUtc), CsvTime(e.ActivationUtc),
                CsvTime(e.CheckpointDueUtc), CsvTime(e.CheckpointUtc), CsvTime(endUtc), e.Side.ToString(),
                ActivationTicks.ToString(CultureInfo.InvariantCulture),
                CheckpointSeconds.ToString(CultureInfo.InvariantCulture),
                TakeProfitTicks.ToString(CultureInfo.InvariantCulture),
                StopLossTicks.ToString(CultureInfo.InvariantCulture),
                EvaluationSeconds.ToString(CultureInfo.InvariantCulture),
                Csv(e.AnchorPrice), Csv(e.ActivationPrice), Csv(e.CheckpointReferencePrice), Csv(e.EntryPrice),
                Csv(e.Bid), Csv(e.Ask), Csv(e.EntrySpreadTicks, "F2"), Csv(e.CheckpointTimerLagMs, "F3"),
                Csv(e.QuoteAgeMs, "F3"), CsvTime(e.FirstMarketUpdateUtc),
                Csv(e.NextMarketUpdateDelayMs, "F3"), e.FirstMarketUpdateType,
                Csv(e.MfeTicks, "F2"), Csv(e.MaeTicks, "F2"), Csv(e.SecondsToTp, "F3"),
                Csv(e.SecondsToSl, "F3"), outcome, Csv(e.FinalSignedTicks, "F2"), endReason,
                incomplete ? "1" : "0", e.ModelVersion, Csv(e.ResolutionProbability, "F8"),
                Csv(e.DirectionProbability, "F8"), e.Qualified ? "1" : "0"
            };
            lock (_csvSync) _episodeBuffer.Add(string.Join(",", values));
        }

        private void QueueCheckpointRow(PendingActivation a, VirtualEpisode e, DateTime nowUtc,
            Dictionary<string, double> features)
        {
            double bidSize, askSize, imbalance;
            GetTopBook(out bidSize, out askSize, out imbalance);
            var values = new List<string>
            {
                _runId, a.ActivationId, e.EpisodeId, CurrentSymbol?.Name ?? "", a.Side.ToString(),
                CsvTime(a.AnchorUtc), CsvTime(a.ActivationUtc), CsvTime(a.CheckpointDueUtc), CsvTime(nowUtc),
                Csv(a.AnchorPrice), Csv(a.ActivationPrice), Csv(e.CheckpointReferencePrice), Csv(e.EntryPrice),
                Csv(e.Bid), Csv(e.Ask), Csv(e.EntrySpreadTicks, "F2"), Csv(bidSize, "F0"),
                Csv(askSize, "F0"), Csv(imbalance, "F5"), Csv(e.CheckpointTimerLagMs, "F3"),
                Csv(e.QuoteAgeMs, "F3"), CsvTime(_lastTradeEventUtc), CsvTime(_lastTradeReceiveUtc),
                Csv(ValidLatencyMs(_lastTradeEventUtc, _lastTradeReceiveUtc), "F3"),
                CsvTime(_lastQuoteEventUtc), CsvTime(_lastQuoteReceiveUtc),
                Csv(ValidLatencyMs(_lastQuoteEventUtc, _lastQuoteReceiveUtc), "F3"),
                e.ModelVersion, Csv(e.ResolutionProbability, "F8"),
                Csv(e.DirectionProbability, "F8"), e.Qualified ? "1" : "0"
            };
            foreach (int seconds in _featureWindows)
            {
                WindowFeatures w = CalculateWindow(nowUtc, seconds);
                values.Add(w.TradeCount.ToString(CultureInfo.InvariantCulture));
                values.Add(Csv(w.TradeVolume, "F0"));
                values.Add(Csv(w.NetTicks, "F2"));
            }
            foreach (string feature in _modelSpec.DirectionModel.InputFeatures)
                values.Add(Csv(features.TryGetValue(feature, out double value) ? value : double.NaN, "F8"));
            lock (_csvSync) _checkpointBuffer.Add(string.Join(",", values));
        }

        private WindowFeatures CalculateWindow(DateTime nowUtc, int seconds)
        {
            DateTime cutoff = nowUtc.AddSeconds(-seconds);
            TimedTrade[] trades = _trades.Where(x => x.ReceiveUtc >= cutoff).ToArray();
            double first = trades.Length > 0 ? trades[0].Price : double.NaN;
            double last = trades.Length > 0 ? trades[trades.Length - 1].Price : double.NaN;
            return new WindowFeatures
            {
                TradeCount = trades.Length,
                TradeVolume = trades.Sum(x => x.Size),
                NetTicks = trades.Length > 0 ? Ticks(last - first) : double.NaN
            };
        }

        private void MarkFirstMarketUpdate(DateTime receiveUtc, string updateType)
        {
            foreach (VirtualEpisode e in _episodes)
            {
                if (e.FirstMarketUpdateUtc != DateTime.MinValue || receiveUtc <= e.CheckpointUtc) continue;
                e.FirstMarketUpdateUtc = receiveUtc;
                e.NextMarketUpdateDelayMs = Math.Max(0, (receiveUtc - e.CheckpointUtc).TotalMilliseconds);
                e.FirstMarketUpdateType = updateType;
            }
        }

        private void HandleClosedPeriod(DateTime nowUtc)
        {
            bool closed = IsClosedEt(nowUtc);
            if (closed && !_closedState)
            {
                foreach (VirtualEpisode e in _episodes.ToList())
                    FinalizeEpisode(e, nowUtc, "SESSION_CLOSE", true);
                _episodes.Clear();
                _pending.Clear();
                _trades.Clear();
                _flowEvents.Clear();
                _orders.Clear();
                _searchInitialized = false;
                _closedState = true;

                // The research definition excludes 16:00-18:00 ET. Do not let
                // an enabled paper position leak across that boundary.
                if (_paperPosition != null)
                {
                    TradingOperationResult closeResult = Core.Instance.ClosePosition(_paperPosition);
                    if (closeResult.Status == TradingOperationResultStatus.Success)
                    {
                        Log("PAPER session-close exit requested for signal " + _paperSignalId,
                            StrategyLoggingLevel.Trading);
                        CancelWorkingOrders("session close");
                    }
                    else
                        Log("PAPER session-close exit failed: " + closeResult.Message,
                            StrategyLoggingLevel.Error);
                }
            }
            else if (!closed && _closedState)
            {
                _searchInitialized = false;
                _nextActivationAllowedUtc = DateTime.MinValue;
                _closedState = false;
            }
        }

        private bool IsClosedEt(DateTime utc)
        {
            if (!ExcludeClosedPeriod) return false;
            DateTime et = ToEastern(utc);
            return et.Hour >= 16 && et.Hour < 18;
        }

        private void ResetSearch(double price, DateTime utc)
        {
            _searchInitialized = true;
            _searchLow = _searchHigh = price;
            _searchLowUtc = _searchHighUtc = utc;
        }

        private void TrimTrades(DateTime nowUtc)
        {
            DateTime cutoff = nowUtc.AddSeconds(-_featureWindows.Max() - 5);
            while (_trades.Count > 0 && _trades.Peek().ReceiveUtc < cutoff) _trades.Dequeue();
        }

        private void TrimFlowEvents(DateTime nowUtc)
        {
            DateTime cutoff = nowUtc.AddSeconds(-Math.Max(_featureWindows.Max(), CheckpointSeconds) - 5);
            while (_flowEvents.Count > 0 && _flowEvents.Peek().ReceiveUtc < cutoff)
                _flowEvents.Dequeue();
        }

        private bool LoadAndValidateModel()
        {
            try
            {
                if (!File.Exists(FrozenModelPath))
                    throw new FileNotFoundException("Frozen model JSON was not found", FrozenModelPath);
                _modelSpec = JsonSerializer.Deserialize<FrozenModelSpec>(
                    File.ReadAllText(FrozenModelPath),
                    new JsonSerializerOptions { PropertyNameCaseInsensitive = true });
                if (_modelSpec?.ResolutionModel?.InputFeatures == null
                    || _modelSpec.DirectionModel?.InputFeatures == null
                    || _modelSpec.Thresholds == null
                    || _modelSpec.Activation == null
                    || _modelSpec.Exit == null
                    || _modelSpec.FeatureWindowsSeconds == null)
                    throw new InvalidDataException("Frozen model JSON is incomplete.");
                if (!_modelSpec.ResolutionModel.InputFeatures.SequenceEqual(
                    _modelSpec.DirectionModel.InputFeatures))
                    throw new InvalidDataException("Resolution and direction feature orders differ.");
                if (_modelSpec.TickSize > 0 && Math.Abs(_modelSpec.TickSize - _tickSize) > _tickSize * 0.01)
                    throw new InvalidDataException($"Model tick size {_modelSpec.TickSize} does not match symbol tick size {_tickSize}.");

                if (!string.IsNullOrWhiteSpace(_modelSpec.Instrument)
                    && !string.IsNullOrWhiteSpace(CurrentSymbol.Root)
                    && !string.Equals(_modelSpec.Instrument, CurrentSymbol.Root,
                        StringComparison.OrdinalIgnoreCase))
                    throw new InvalidDataException(
                        $"Model instrument {_modelSpec.Instrument} does not match symbol root {CurrentSymbol.Root}.");

                RequireEqual("Activation ticks", ActivationTicks, _modelSpec.Activation.Ticks);
                RequireEqual("Checkpoint seconds", CheckpointSeconds, _modelSpec.CheckpointSeconds);
                RequireEqual("Cooldown seconds", ActivationCooldownSeconds,
                    _modelSpec.Activation.CooldownSeconds);
                RequireEqual("Take-profit ticks", TakeProfitTicks, _modelSpec.Exit.TakeProfitTicks);
                RequireEqual("Stop-loss ticks", StopLossTicks, _modelSpec.Exit.StopLossTicks);
                RequireEqual("Maximum hold seconds", EvaluationSeconds,
                    _modelSpec.Exit.MaximumHoldSeconds);

                if (!_featureWindows.SequenceEqual(_modelSpec.FeatureWindowsSeconds))
                    throw new InvalidDataException(
                        "Model feature windows do not match the strategy feature windows.");
                ValidatePipeline("resolution", _modelSpec.ResolutionModel);
                ValidatePipeline("direction", _modelSpec.DirectionModel);
                foreach (string feature in _modelSpec.DirectionModel.InputFeatures)
                    if (!IsSupportedDirectionalFeature(feature))
                        throw new InvalidDataException("Unsupported model feature: " + feature);
                if (_modelSpec.Thresholds.ResolutionProbability <= 0
                    || _modelSpec.Thresholds.ResolutionProbability >= 1
                    || _modelSpec.Thresholds.DirectionProbability <= 0
                    || _modelSpec.Thresholds.DirectionProbability >= 1)
                    throw new InvalidDataException("Model probability thresholds must be between zero and one.");
                return true;
            }
            catch (Exception ex)
            {
                Log("Frozen model load failed: " + ex.Message, StrategyLoggingLevel.Error);
                return false;
            }
        }

        private static void RequireEqual(string label, int strategyValue, int modelValue)
        {
            if (strategyValue != modelValue)
                throw new InvalidDataException(
                    $"{label} mismatch: strategy={strategyValue}, model={modelValue}.");
        }

        private static void ValidatePipeline(string label, PipelineSpec model)
        {
            int count = model?.InputFeatures?.Count ?? 0;
            if (count == 0 || model.ImputerStatistics == null || model.ScalerMean == null
                || model.ScalerScale == null || model.Coefficient == null
                || model.ImputerStatistics.Count != count || model.ScalerMean.Count != count
                || model.ScalerScale.Count != count || model.Coefficient.Count != count)
                throw new InvalidDataException(
                    $"The {label} model arrays do not match its feature count.");
            if (model.InputFeatures.Any(string.IsNullOrWhiteSpace)
                || model.InputFeatures.Distinct().Count() != count)
                throw new InvalidDataException(
                    $"The {label} model contains blank or duplicate feature names.");
        }

        private static bool IsSupportedDirectionalFeature(string feature)
        {
            if (string.IsNullOrWhiteSpace(feature)) return false;
            string action;
            if (feature.StartsWith("directional_since_activation_", StringComparison.Ordinal)
                && feature.EndsWith("_aligned_share", StringComparison.Ordinal))
            {
                action = feature.Substring("directional_since_activation_".Length)
                    .Replace("_aligned_share", "");
            }
            else if (feature.StartsWith("directional_", StringComparison.Ordinal)
                && feature.EndsWith("_aligned_share", StringComparison.Ordinal))
            {
                string remainder = feature.Substring("directional_".Length);
                int marker = remainder.IndexOf("s_", StringComparison.Ordinal);
                if (marker <= 0 || !int.TryParse(remainder.Substring(0, marker), out int seconds)
                    || seconds <= 0) return false;
                action = remainder.Substring(marker + 2).Replace("_aligned_share", "");
            }
            else return false;
            return action == "trade" || action == "add"
                || action == "modify" || action == "cancel";
        }

        private void TryPlacePaperOrder(VirtualEpisode episode)
        {
            if (!EnablePaperOrders) return;
            if (_paperTradingBlockedAfterReconnect)
            {
                Log("Qualified signal not traded: paper execution is blocked after reconnect until strategy restart.",
                    StrategyLoggingLevel.Error);
                return;
            }
            if (!string.Equals(PaperConfirmation?.Trim(), "PAPER ONLY", StringComparison.Ordinal))
            {
                Log("Qualified signal not traded: Paper confirmation must equal PAPER ONLY.", StrategyLoggingLevel.Error);
                return;
            }
            if (CurrentAccount == null)
            {
                Log("Qualified signal not traded: no account selected.", StrategyLoggingLevel.Error);
                return;
            }
            if (_paperEntryPending || _paperPosition != null) return;
            if (Core.Instance.Positions.Any(p => IsOurAccount(p.Account) && IsOurSymbol(p.Symbol))) return;
            if (Core.Instance.Orders.Any(o => IsOurAccount(o.Account) && IsOurSymbol(o.Symbol)
                && (o.Status == OrderStatus.Opened || o.Status == OrderStatus.PartiallyFilled))) return;

            // Set pending state before submission so a very fast PositionAdded
            // callback cannot arrive before the strategy is ready to claim it.
            _paperEntryPending = true;
            _paperPendingSide = episode.Side;
            _paperSignalId = episode.EpisodeId;

            var result = Core.Instance.PlaceOrder(new PlaceOrderRequestParameters
            {
                Symbol = CurrentSymbol,
                Account = CurrentAccount,
                Side = episode.Side,
                OrderTypeId = OrderType.Market,
                Quantity = PaperQuantity,
                TimeInForce = TimeInForce.GTC,
                TakeProfit = SlTpHolder.CreateTP(TakeProfitTicks, PriceMeasurement.Offset),
                StopLoss = SlTpHolder.CreateSL(StopLossTicks, PriceMeasurement.Offset),
                Comment = "HG_MBO_" + episode.ModelVersion
            });
            if (result.Status != TradingOperationResultStatus.Success)
            {
                _paperEntryPending = false;
                _paperSignalId = "";
                Log("Paper entry failed: " + result.Message, StrategyLoggingLevel.Error);
                return;
            }
            Log($"PAPER entry submitted: {episode.Side} {PaperQuantity}, signal={episode.EpisodeId}",
                StrategyLoggingLevel.Trading);
        }

        private void OnPositionAdded(Position position)
        {
            lock (_sync)
            {
                if (!IsOurAccount(position.Account) || !IsOurSymbol(position.Symbol)) return;

                if (_paperEntryPending && position.Side == _paperPendingSide)
                {
                    _paperPosition = position;
                    _paperPositionOpenedUtc = DateTime.UtcNow;
                    _paperEntryPending = false;
                    Log($"PAPER position filled: {position.Side} {position.Quantity} @ {position.OpenPrice:F5}; signal={_paperSignalId}",
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
                _paperPosition = null;
                _paperPositionOpenedUtc = DateTime.MinValue;
                _paperSignalId = "";
            }
        }

        // A position that reaches this path did not come from the strategy's
        // own tracked entry flow, so it carries no verified broker-side SL/TP
        // (the bracket is only known to exist on the fill the strategy itself
        // claimed). Rather than adopt it into timed management and let it ride
        // unprotected for up to EvaluationSeconds, close it immediately. Never
        // touches an already-tracked position, since IsOurSymbol matches by
        // root and could otherwise misidentify an unrelated position in a
        // different contract month as ours.
        private void CloseUnexpectedPosition(Position position, string reason)
        {
            if (_paperPosition != null)
            {
                if (_paperPosition.Id == position.Id) return;
                Log($"PAPER position anomaly: already tracking id={_paperPosition.Id} but an unrelated " +
                    $"position id={position.Id}, side={position.Side}, qty={position.Quantity} appeared for " +
                    $"our account/symbol ({reason}). Not touching it; check the platform for a duplicate or " +
                    "unexpected position.", StrategyLoggingLevel.Error);
                return;
            }
            Log($"PAPER position found outside the normal entry flow: id={position.Id}, side={position.Side}, " +
                $"qty={position.Quantity} @ {position.OpenPrice:F5} ({reason}). This usually means the platform " +
                "reissued the position object (partial-fill merge, reconnect reconciliation) or a position was " +
                "left open from a prior run. It has no verified stop-loss, so it is being closed immediately " +
                "rather than adopted.", StrategyLoggingLevel.Error);
            TradingOperationResult result = Core.Instance.ClosePosition(position);
            if (result.Status == TradingOperationResultStatus.Success)
            {
                Log($"Unexpected PAPER position close requested: id={position.Id}.", StrategyLoggingLevel.Trading);
                // Only sweep stray orders when there is no real entry still in
                // flight (a side-mismatch call can reach here while _paperEntryPending
                // is still true and its order may still be working).
                if (!_paperEntryPending) CancelWorkingOrders("unexpected position closed");
            }
            else
                Log($"Unexpected PAPER position close FAILED: id={position.Id}: {result.Message}. " +
                    "Manual intervention required.", StrategyLoggingLevel.Error);
        }

        // Any SL/TP or other working order left for our account/symbol after a
        // position close is either stale (its position is gone) or, at minimum,
        // no longer wanted once we've deliberately exited. Left alone it would
        // silently block TryPlacePaperOrder's new-entry guard from ever firing
        // again until someone notices and cancels it by hand.
        private void CancelWorkingOrders(string reason)
        {
            List<Order> working = Core.Instance.Orders.Where(o => IsOurAccount(o.Account) && IsOurSymbol(o.Symbol)
                && (o.Status == OrderStatus.Opened || o.Status == OrderStatus.PartiallyFilled)).ToList();
            foreach (Order order in working)
            {
                TradingOperationResult result = Core.Instance.CancelOrder((IOrder)order);
                if (result.Status == TradingOperationResultStatus.Success)
                    Log($"Working order cancelled after close ({reason}): id={order.Id}.", StrategyLoggingLevel.Trading);
                else
                    Log($"Failed to cancel working order after close ({reason}): id={order.Id}: {result.Message}.",
                        StrategyLoggingLevel.Error);
            }
        }

        // Periodic safety net: catches a position that exists on the platform
        // for our account/symbol but that the strategy lost track of (or never
        // saw a PositionAdded for, e.g. one left open from a prior run started
        // before this instance subscribed to position events).
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

        private void HandlePaperTimeExit(DateTime nowUtc)
        {
            if (_paperPosition == null || _paperPositionOpenedUtc == DateTime.MinValue) return;
            if ((nowUtc - _paperPositionOpenedUtc).TotalSeconds < EvaluationSeconds) return;
            TradingOperationResult result = Core.Instance.ClosePosition(_paperPosition);
            if (result.Status == TradingOperationResultStatus.Success)
            {
                Log("PAPER 600-second time exit requested for signal " + _paperSignalId,
                    StrategyLoggingLevel.Trading);
                CancelWorkingOrders("600-second time exit");
            }
            else
                Log("PAPER time exit failed: " + result.Message, StrategyLoggingLevel.Error);
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

        private void RefreshDom()
        {
            try
            {
                var dom = CurrentSymbol?.DepthOfMarket?.GetDepthOfMarketAggregatedCollections(
                    new GetLevel2ItemsParameters
                    {
                        AggregateMethod = AggregateMethod.ByPriceLVL,
                        LevelsCount = Math.Max(1, DomLevels),
                        CalculateCumulative = true
                    });
                if (dom?.Bids?.Length > 0 && dom.Asks?.Length > 0)
                {
                    _bids = dom.Bids.ToList();
                    _asks = dom.Asks.ToList();
                }
            }
            catch { }
        }

        private void GetTopBook(out double bidSize, out double askSize, out double imbalance)
        {
            bidSize = askSize = imbalance = double.NaN;
            if (_bids == null || _asks == null || _bids.Count == 0 || _asks.Count == 0) return;
            bidSize = ReadNumericProperty(_bids[0], "Size", "Volume", "Quantity");
            askSize = ReadNumericProperty(_asks[0], "Size", "Volume", "Quantity");
            double total = bidSize + askSize;
            if (!double.IsNaN(total) && total > 0) imbalance = (bidSize - askSize) / total;
        }

        private void EnsureHeaders()
        {
            Directory.CreateDirectory(Path.GetDirectoryName(_checkpointCsv));
            string checkpointHeader =
                "runId,activationId,episodeId,symbol,direction,anchorUtc,activationUtc,checkpointDueUtc,checkpointUtc," +
                "anchorPrice,activationPrice,checkpointLastTradePrice,executableEntryPrice,bid,ask,spreadTicks," +
                "bidSize,askSize,depthImbalance,checkpointTimerLagMs,quoteAgeMs,lastTradeEventUtc,lastTradeReceiveUtc," +
                "tradeFeedLatencyMs,lastQuoteEventUtc,lastQuoteReceiveUtc,quoteFeedLatencyMs,modelVersion," +
                "resolutionProbability,directionProbability,qualified," +
                string.Join(",", _featureWindows.SelectMany(w => new[]
                {
                    $"tradeCount_{w}s", $"tradeVolume_{w}s", $"netTicks_{w}s"
                })) + "," + string.Join(",", _modelSpec.DirectionModel.InputFeatures);
            string episodeHeader =
                "runId,episodeId,activationId,anchorUtc,activationUtc,checkpointDueUtc,checkpointUtc,endUtc,direction," +
                "activationTicks,checkpointSeconds,takeProfitTicks,stopLossTicks,evaluationSeconds,anchorPrice," +
                "activationPrice,checkpointLastTradePrice,entryPrice,bid,ask,spreadTicks,checkpointTimerLagMs," +
                "quoteAgeMs,firstMarketUpdateUtc,nextMarketUpdateDelayMs,firstMarketUpdateType,mfeTicks,maeTicks," +
                "secondsToTp,secondsToSl,firstTouchOutcome,finalSignedTicks,endReason,incomplete,modelVersion," +
                "resolutionProbability,directionProbability,qualified";
            EnsureHeader(_checkpointCsv, checkpointHeader);
            EnsureHeader(_episodeCsv, episodeHeader);
        }

        private static void EnsureHeader(string path, string header)
        {
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
                List<string> checkpoints;
                List<string> episodes;
                lock (_csvSync)
                {
                    checkpoints = new List<string>(_checkpointBuffer);
                    episodes = new List<string>(_episodeBuffer);
                }
                try
                {
                    if (checkpoints.Count > 0) File.AppendAllLines(_checkpointCsv, checkpoints);
                    if (episodes.Count > 0) File.AppendAllLines(_episodeCsv, episodes);
                }
                catch (Exception ex)
                {
                    Log("CSV flush failed; rows retained: " + ex.Message, StrategyLoggingLevel.Error);
                    return;
                }
                lock (_csvSync)
                {
                    _checkpointBuffer.RemoveRange(0, Math.Min(checkpoints.Count, _checkpointBuffer.Count));
                    _episodeBuffer.RemoveRange(0, Math.Min(episodes.Count, _episodeBuffer.Count));
                }
            }
        }

        private double Ticks(double priceDifference)
        {
            return _tickSize > 0 && !double.IsNaN(priceDifference)
                ? priceDifference / _tickSize : double.NaN;
        }

        private static double ValidLatencyMs(DateTime eventUtc, DateTime receiveUtc)
        {
            if (eventUtc == DateTime.MinValue || receiveUtc == DateTime.MinValue) return double.NaN;
            double value = (receiveUtc - eventUtc).TotalMilliseconds;
            return value >= -1000 && value <= 86400000 ? value : double.NaN;
        }

        private static DateTime TryReadUtcTimestamp(object obj)
        {
            if (obj == null) return DateTime.MinValue;
            string[] names = { "Time", "DateTime", "Timestamp", "ServerTime", "ExchangeTime" };
            foreach (string name in names)
            {
                try
                {
                    PropertyInfo p = obj.GetType().GetProperty(name);
                    if (p == null) continue;
                    object value = p.GetValue(obj);
                    if (value is DateTimeOffset dto) return dto.UtcDateTime;
                    if (value is DateTime dt)
                    {
                        if (dt.Kind == DateTimeKind.Utc) return dt;
                        if (dt.Kind == DateTimeKind.Local) return dt.ToUniversalTime();
                        return DateTime.SpecifyKind(dt, DateTimeKind.Utc);
                    }
                }
                catch { }
            }
            return DateTime.MinValue;
        }

        private static double ReadNumericProperty(object obj, params string[] names)
        {
            if (obj == null) return double.NaN;
            foreach (string name in names)
            {
                try
                {
                    PropertyInfo p = obj.GetType().GetProperty(name);
                    if (p == null) continue;
                    object value = p.GetValue(obj);
                    if (value != null) return Convert.ToDouble(value, CultureInfo.InvariantCulture);
                }
                catch { }
            }
            return double.NaN;
        }

        private static string Csv(double value, string format = "F5")
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
