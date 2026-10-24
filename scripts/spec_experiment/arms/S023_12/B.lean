-- imports: VCVio.ProgramLogic.Library
theorem prEvent_stablePhaseRunFrom_exact_le
    [DecidableEq Query] [DecidableEq Address] [DecidableEq Y]
    [Finite Y]
    [UniformAnswerMeasure (Query →ₒ Y)]
    (view : MerkleTreeExtractor.QueryView Query Address Y)
    {config : Configuration Cfg Address}
    (state : ExtractorState Cfg Query Address Y config)
    (suffix : X → (Query →ₒ Y).QueryLog → OracleComp (Query →ₒ Y) R)
    (continuation : X → OracleComp (Query →ₒ Y) C)
    (win : R → Prop) (overhead : ℕ)
    (prefixComp : OracleComp (Query →ₒ Y) X)
    (remaining cached : ℕ)
    (hbound : IsTotalQueryBound (prefixComp >>= continuation) remaining)
    (cache : (Query →ₒ Y).QueryCache)
    (log : (Query →ₒ Y).QueryLog)
    (hno : ¬ CacheHasCollision cache)
    (hcacheBound : ∃ keys : Finset Query, keys.card ≤ cached ∧
      ∀ input, cache input ≠ none → input ∈ keys)
    (hlogCache : ∀ entry ∈ log, cache entry.1 = some entry.2)
    (hcacheLog : ∀ input value, cache input = some value →
      ∃ entry ∈ log, entry.1 = input ∧ entry.2 = value)
    (hstable : state.StableAt view log)
    (hterminal : ∀ (x : X) (terminalRemaining terminalCached : ℕ)
        (terminalCache : (Query →ₒ Y).QueryCache)
        (terminalLog : (Query →ₒ Y).QueryLog),
      IsTotalQueryBound (continuation x) terminalRemaining →
      ¬ CacheHasCollision terminalCache →
      (∃ keys : Finset Query, keys.card ≤ terminalCached ∧
        ∀ input, terminalCache input ≠ none → input ∈ keys) →
      (∀ entry ∈ terminalLog, terminalCache entry.1 = some entry.2) →
      (∀ input value, terminalCache input = some value →
        ∃ entry ∈ terminalLog, entry.1 = input ∧ entry.2 = value) →
      state.StableAt view terminalLog →
      Pr{let z ← (simulateQ (Query →ₒ Y).cachingOracle (suffix x terminalLog)).run
             terminalCache}[win z.1] ≤
        (multiCheckpointErrorNumerator state.totalNodeBudget state.checkpoints.length
          overhead terminalRemaining terminalCached : ENNReal) *
            (Nat.card Y : ENNReal)⁻¹) :
    Pr{let z ← adaptivePrefixRunFrom (ι := Query) (Y := Y) (X := X) (R := R) suffix prefixComp
           cache log}[win z.1] ≤
      (multiCheckpointErrorNumerator state.totalNodeBudget state.checkpoints.length
        overhead remaining cached : ENNReal) * (Nat.card Y : ENNReal)⁻¹ :=
  by apply prEvent_stablePhaseRunFrom_le view state <;> first | assumption | rfl
