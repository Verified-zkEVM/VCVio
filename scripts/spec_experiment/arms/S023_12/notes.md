# S023_12 prEvent_stablePhaseRunFrom_exact_le — arm A

- Minutes: ~5
- Original: 45 lines / 434 HB (42 statement lines + a 3-line explicit term application of
  `prEvent_stablePhaseRunFrom_le … le_rfl le_rfl hterminal`).
- A: 43 lines / ~490 HB: `by apply prEvent_stablePhaseRunFrom_le view state <;> first | assumption
  | rfl`.
- What shortened it: `apply` + `assumption` closes all hypothesis arguments; `rfl` (Mathlib
  `@[refl] le_refl`) closes the two budget side conditions. `view` must be given (it only occurs
  in a hypothesis, and `DecidableEq ?Address` is synthesized before unification otherwise).
- Tried: `_`-heavy term (2 lines, 427 HB), named-arg `..` term (fails: `hterminal` not inferred).
- Reason: NEAR-NO-ROOM (statement is 42/45 lines).
- Missing: nothing substantive; the theorem is a specialization of an existing one.

## B
- Minutes: ~1. B.lean = A.lean + import. 43 lines / 491 HB (A: 43 / 491).
- Library lemmas used: none (specialisation of an existing theorem; no room).
