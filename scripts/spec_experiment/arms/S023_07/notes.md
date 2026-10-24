# S023_07 isQueryBoundP_liftComp_isEncQuery — arm A

- Minutes: ~4
- Result: 4 lines / 178 HB (original 10 / 482). Accepted. Extra import:
  `VCVio.OracleComp.QueryTracking.QueryBound.Simulation` (existing module).
- Tried: plain induction with `simpa [IsEncQuery] using ih` (fails: the lifted query
  `liftM (liftM (query t))` is not in the `liftM (spec.query (Sum.inl t)) >>= _` shape that
  `isQueryBoundP_query_bind_iff` matches, which is why the original needs a `change`);
  `simp [IsEncQuery, liftM_eq_liftM_liftM]` on the step goal (same problem).
- What shortened it: `liftComp` is definitionally `simulateQ (fun t => liftM (query t))`, so the
  existing `IsQueryBoundP.simulateQ_of_step` with source predicate `fun _ => False`
  (`isQueryBoundP_false`) reduces it to a one-query step, closed by
  `(isQueryBoundP_query_iff _ (Sum.inl t) 0).2 nofun` (defeq of the lifted query).
- Missing:
  - `isQueryBoundP_liftComp (h : ∀ t, ¬ q (lift t)) : IsQueryBoundP (liftComp oa superSpec) q 0`
    — more generally `IsQueryBoundP (liftComp oa superSpec) q n ↔ IsQueryBoundP oa (q ∘ ι) n`
    for a sub-spec index embedding; and the special case for `spec₁ ⊂ₒ spec₁ + spec₂` with
    `q = isRight`.
  - simp lemma normalizing `liftM (liftM (spec₁.query t) : OracleQuery (spec₁ + spec₂) _)` to
    `liftM ((spec₁ + spec₂).query (Sum.inl t))`, so the existing `isQueryBoundP_query_bind_iff`
    simp set fires on lifted computations.

## B
- Minutes: ~2. B = A + import: 4 lines / 179 HB (A 4 / 178).
- Looked for: an `IsQueryBoundP` rule for `liftComp` in T1/QueryBound. Only the total-bound
  `isTotalQueryBound_liftComp` exists. Missing:
  `isQueryBoundP_liftComp : (∀ t, ¬ q (lift t)) → IsQueryBoundP (liftComp oa sup) q 0`, or
  the general `IsQueryBoundP (liftComp oa sup) q n ↔ IsQueryBoundP oa (q ∘ lift) n`
  (with the `spec₁ ⊂ₒ spec₁ + spec₂` instance: `q ∘ Sum.inl`).
