# S023_05 evalDistEq_run_progGameRunImplCombinedTrap_eq — arm A

- Minutes: ~3
- Result: 10 lines / 218 HB (original 13 / 186). Accepted (HB ≤ 1.5×).
  (A two-line variant with the step lemma's explicit arguments was 11 lines / 179 HB.)
- What shortened it: the original is already a one-term application of the generic
  `evalDistEq_simulateQ_run`; the only saving is letting unification infer the two handlers,
  the step lemma's parameters (from `hreg` and the expected type) and the trailing `oa s` (`..`).
  All savings are in the header-dominated proof's argument lists; nothing structural.
- Missing: nothing substantive — the generic simulation-congruence lemma already exists and the
  per-step equidistribution is a separate lemma in the file. A `@[gcongr]`/tactic form
  ("`simulateQ_congr` with per-step `=ᵈ` side goal") would let it be `by simulateQ_congr; exact
  evalDistEq_progGameRunImplCombined_step_eq_trap .. hreg`, which is not shorter here.

## B
- Minutes: ~2. B = A + import: 10 lines / 218 HB (A 10 / 218).
- Looked at `evalDistEq_simulateQ_run_of_impl_evalDistEq_on_inv` (T1/Bisim) with
  `Inv := fun _ => True`: strictly longer than the existing invariant-free
  `evalDistEq_simulateQ_run` already used in A. No library gain; nothing missing.
