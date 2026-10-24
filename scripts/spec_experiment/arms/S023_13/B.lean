-- imports: VCVio.ProgramLogic.Library
theorem prEvent_contextForkPair_le_guarded_add_collision [DecidableEq ι]
    [∀ t, DecidableEq (spec.Range t)] [OracleSpec.AnswerMeasure spec]
    (main : OracleComp spec α) (qb : ι → ℕ) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) (s : Fin (qb i + 1)) :
    Pr{let r ← contextForkPair main qb i cf s}[r = some (some s, some s)] ≤
      Pr{let r ← guardedContextFork main qb i cf s}[r.isSome] +
        Pr{let r ← contextForkViewCollision main qb i cf s}[r = some s] := by
  rw [contextForkPair, observedForkPair, prEvent_map]
  refine (prEvent_mono _ _ _ fun v => ?_).trans ((prEvent_or_le _ _ _).trans_eq
    (congrArg₂ _ (prEvent_map _ _ _).symm (prEvent_map _ _ (· = some s)).symm))
  rcases v with _ | view <;> simp; grind [classifyForkView, collideForkView]
