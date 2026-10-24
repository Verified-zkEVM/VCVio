# S023_10 ITSRAdvantage_eq_evalDist_experiment — arm A

- Minutes: ~4
- Original: 6 lines / 258 HB (`simpa only [ITSRAdvantage, ITSRExperiment] using
  prEvent_eq_evalDist_decide (mx := adv.run) (p := fun z => prob.Wins z.2 z.1)`).
- A: 4 lines / 169 HB, 52 tokens (vs 73): term proof `prEvent_eq_evalDist_decide ..`.
- What shortened it: the definitions `ITSRAdvantage`/`ITSRExperiment` unfold definitionally to the
  lemma's two sides (the pair-pattern `let (c, t) ← _` matches `p z` up to structure eta), so no
  `simpa` unfolding is needed and `p` is inferred by unification.
- Missing: nothing; the generic bridge lemma `prEvent_eq_evalDist_decide` already exists.

## B
- Minutes: ~1. B.lean = A.lean + import. 4 lines / 170 HB (A: 4 / 169).
- Library lemmas used: none (no simulation or handler involved; the bridge
  `prEvent_eq_evalDist_decide` is core VCVio).
