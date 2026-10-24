-- imports: VCVio.ProgramLogic.Library
theorem contextFork_propertyTransfer [DecidableEq ι] [∀ t, DecidableEq (spec.Range t)]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1)))
    (P_out : α → QueryLog spec → Prop)
    (hP : ∀ {x log}, (x, log) ∈ support (replayFirstRun main) → P_out x log)
    {x₁ x₂ : α} (h : some (x₁, x₂) ∈ support (contextFork main qb i cf)) :
    ∃ (log₁ log₂ : QueryLog spec) (s : Fin (qb i + 1)),
      cf x₁ = some s ∧ cf x₂ = some s ∧
      P_out x₁ log₁ ∧ P_out x₂ log₂ ∧
      QueryLog.getQueryValue? log₁ i s ≠
        QueryLog.getQueryValue? log₂ i s := by
  obtain ⟨_, s, ⟨o, c, rfl⟩, d, -, h₁, -, hne, h₂, rfl, rfl⟩ := contextFork_success _ _ _ _ h
  have k p := hP (replayPathResult_mem_support_replayFirstRun _ p (mem_support_replayFirstPath _ p))
  exact ⟨_, _, s, h₁, h₂, k _, k _, by simpa [getQueryValue?_completion_path_eq_answer o] using hne⟩
