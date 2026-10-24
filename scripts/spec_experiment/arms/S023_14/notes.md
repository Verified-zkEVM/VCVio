# S023_14 progGameRunImplCombinedTrapCount_table_defer — arm A

- Minutes: ~25
- Original: 215 lines / 9762 HB.
- A: 91 lines / ~22.8k HB, no top-level helpers (both helpers are local `have`s, so all
  heartbeats are counted; an earlier version with two top-level helpers measured 97 lines /
  16.0k HB in the main declaration + 6.7k uncounted in helpers). Accepted via the lines gate
  (91 ≤ 129, HB ≤ 48.8k). Replacing the two `simp [hcs, …, htbls]` calls in the "IH at a
  post-state" branches by `simp only` lists cuts ~10k HB at +2 lines (not taken).
- Same proof strategy (induction on `oa`; split on whether `k₀` is cached at the start; split on
  the query kind), but:
  - `intro s htc` once + `induction … generalizing s`; pure case is `clear hsupp forged` +
    `rcases … <;> simp_all` (without the `clear`, `simp_all` loops on the local `have`s);
  - IH applications at a modified post-state are `(ih v _ ?_).trans ?_ <;> simp [hcs, …, htbls]`:
    the post-state is found by unification, so the 4-line explicit post-states of the original
    disappear everywhere;
  - unchanged-state branches use `(ih v s htc).trans (by rw [hcs])` (cheap) instead of
    `have hih …; simp only [hcs] at hih; exact hih`;
  - the forged-miss branch (originally ~85 lines with explicit `Q`, `hLHS`, `hRHS`) became a
    local `have forged` stated over an abstract family of post-states
    `σ : Domain → State` (only `cache(k₀) = some v`, `table(k₀) = some x`, and "σ x agrees with
    σ sStar off the table" are needed), applied with `σ` inferred by unification. Its proof uses
    the existing `…_table_frozen_eq` (as a conditional simp lemma whose side condition simp
    discharges), `…_table_indep`, `…_frozen`, and a support-congruence helper;
  - the signed-forged-message branch is one support-congruence step + `…_signedSet_grows`.
- Tried and rejected: `congr! 6` for the triple `tsum_congr` (goes too deep), full `simp` with
  `mul_comm` for the final arithmetic (wrong normal form), `simp` for the frozen-start case (72k HB).
- Missing (would have shortened further):
  - `tsum_prEvent_mul_congr_support : (∀ z ∈ support oa, f z = g z) → ∑' z, Pr[= z | oa] * f z =
    ∑' z, Pr[= z | oa] * g z` (generic; written here as a local `have hsupp`).
  - a lemma/tactic for nested `tsum_prEvent_bind_mul` congruence: "`∑' z, Pr[= z | oa >>= f] * h z
    = ∑' z, Pr[= z | oa >>= g] * h' z` from `∀ a ∈ support oa, ∑' … f a … = ∑' … g a …`"
    (a relational `bind_congr` for weighted sums) — replaces the repeated
    `simp only [tsum_prEvent_bind_mul]; refine tsum_congr fun r => congrArg _ <| …` chains.
  - handler-specific: a frozen-cache analogue of `…_table_frozen_eq` for an arbitrary function of
    `cache_z k₀` (here proved inline), and a family version of `…_table_indep` ("the expectation
    does not depend on the table value written at a cached key").
  - generally: an "expectation of a write-only state component is deferrable" lemma for stateful
    handlers whose component is never read — this theorem is an instance.

## B
- Minutes: ~6. B.lean = A.lean + import. 91 lines / 22836 HB (A: 91 / 22823).
- Library lemmas used: none in the final version.
- Tried: replacing the shared 2-line `simp only [simulateQ_bind, simulateQ_query,
  OracleQuery.input_query, OracleQuery.cont_query, id_map, StateT.run_bind]` by
  `simp only [simulateQ_nf]` (−1 line). It produced the same top-level goal but broke every
  `ih v …` application downstream: after the per-case run lemma and `simulateQ_nf`'s
  `bind_assoc`/`pure_bind`, the bound answer `v` gets the summand's range type (`Fin (n+1)`,
  `Range`) instead of `((unifSpec + _) + _).Range (Sum.inl (Sum.inl n))`, and `ih v` / `mx v`
  no longer elaborate. Reverted.
- Missing / did not fit: the library has no weighted-sum (`∑' z, Pr[= z | run] * f z`) rules —
  the whole proof is in that shape (`tsum_prEvent_bind_mul` congruence, support congruence,
  frozen/write-only state deferral). The whole-run support principles
  (`inv_of_mem_support_simulateQ_run`, `MonotoneState`) would re-prove the file's existing
  `…_signedSet_grows`/`…_frozen`, which this proof only uses.
