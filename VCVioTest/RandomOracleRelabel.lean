/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Relabel
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Canonical relabelling on a one-node graph

A random oracle on `Bool` has one derivation `()` and one node `()`, whose only child is the
derivation and whose point is the derivation's value. The relabelled game answers a public query
at the derivation's value, once the derivation is drawn, by the node's label.

* When the derivation is drawn first and then queried, no conflict arises on any path, so the
  relabelling bound reduces to the relabelled game read on the merged state.
* When the public point `true` is queried first and the derivation drawn afterwards, a conflict
  arises exactly when the derivation is `true`, with probability `2⁻¹`, and the relabelling bound
  charges it.
* The conflict cannot be dropped from the bound: in the second program the ideal game caches the
  point `true` with probability `1`, while the relabelled game, read on the merged state, does so
  only with probability `2⁻¹`.
* Under the secret encoding that reads the derivation at the public point named by the secret, the
  split state merged under the encoding reads the derivation there, the node's label at the
  node's point, and the public cache elsewhere.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace RelabelToy

/-- Programs with uniform draws, a public random oracle on `Bool` and one derivation query. -/
abbrev spec : OracleSpec ((ℕ ⊕ Bool) ⊕ Unit) := (Bool →ₒ Bool).withDerivations Unit Bool

/-- One node, whose only child is the derivation and whose point is the derivation's value. -/
def G : CanonicalGraph (Bool →ₒ Bool) Unit Unit Bool where
  ch _ := [.inl ()]
  pt _ vs := vs.headD false
  range_eq _ _ := rfl
  pt_inj {_ _ vs vs'} h h' hpt := by
    match vs, vs', h, h' with
    | [v], [v'], _, _ => exact ⟨rfl, by simpa using hpt⟩

/-- The derivation is drawn, then its value is queried. -/
def honestFirst : OracleComp spec Bool := do
  let s ← liftM (spec.query (.inr ()))
  liftM (spec.query (.inl (.inr s)))

/-- The point `true` is queried, then the derivation is drawn. -/
def forgerFirst : OracleComp spec Bool := do
  let _ ← liftM (spec.query (.inl (.inr true)))
  liftM (spec.query (.inr ()))

/-- The children of the node are drawn exactly when the derivation is. -/
theorem childVals_eq (st : RelabelState (Bool →ₒ Bool) Unit Unit Bool) :
    G.childVals st () = (st.2 (.inl ())).map fun v ↦ [v] := by
  cases h : st.2 (.inl ()) with
  | some v => exact G.childVals_eq_some_iff.2 (.cons h .nil)
  | none =>
    cases hc : G.childVals st () with
    | none => rfl
    | some vs =>
      have hf : List.Forall₂ (fun c v ↦ st.2 c = some v) [.inl ()] vs :=
        G.childVals_eq_some_iff.1 hc
      rcases hf with _ | ⟨hv, -⟩
      rw [h] at hv
      exact absurd hv (Option.some_ne_none _).symm

/-- Drawing the derivation leaves the label of the node undrawn. -/
theorem cacheQuery_apply_inr (s : Bool) :
    ((∅ : ((Unit ⊕ Unit) →ₒ Bool).QueryCache).cacheQuery (.inl ()) s) (.inr ()) = none :=
  (QueryCache.cacheQuery_of_ne _ _ Sum.inr_ne_inl).trans (QueryCache.empty_apply _)

/-- A state whose public cache is empty has no conflict. -/
theorem not_conflict_of_cache_eq_empty {st : RelabelState (Bool →ₒ Bool) Unit Unit Bool}
    (h : st.1 = ∅) : ¬G.Conflict st := by
  rintro ⟨_, _, -, hc⟩
  rw [h, QueryCache.empty_apply] at hc
  exact Bool.false_ne_true hc

/-- Drawing the derivation and then querying its value never conflicts. -/
theorem not_conflict_of_mem_support_honestFirst {z}
    (hz : z ∈ support ((simulateQ G.relabelImpl honestFirst).run (∅, ∅))) : ¬G.Conflict z.2 := by
  simp only [honestFirst, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    mem_support_bind_iff] at hz
  obtain ⟨w, hw, hz⟩ := hz
  rw [CanonicalGraph.relabelImpl_apply_inr,
    RelabelState.drawCell_run_of_cell_eq_none (c := .inl ()) rfl, support_map] at hw
  obtain ⟨s, -, rfl⟩ := hw
  have hk : G.childVals (∅, (∅ : ((Unit ⊕ Unit) →ₒ Bool).QueryCache).cacheQuery (.inl ()) s) ()
      = some [s] := by
    rw [childVals_eq, QueryCache.cacheQuery_self]; rfl
  change z ∈ support ((G.relabelImpl (.inl (.inr (G.pt () [s])))).run _) at hz
  rw [G.relabelImpl_run_pt hk, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [RelabelState.drawCell_run_of_cell_eq_none (c := .inr ()) (cacheQuery_apply_inr s),
    support_map] at hw
  obtain ⟨u, -, rfl⟩ := hw
  exact not_conflict_of_cache_eq_empty rfl

/-- For the honest-first program, the ideal game is dominated by the relabelled game read on the
merged state. -/
example (P : Bool × SecretEncoding.SplitCache (Bool →ₒ Bool) Unit Bool → Prop) :
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl (Bool →ₒ Bool) Unit Bool)
        honestFirst).run (∅, ∅)}[P z] ≤
      Pr{let z ← (simulateQ G.relabelImpl honestFirst).run (∅, ∅)}[P (z.1, G.toSplitCache z.2)] :=
  (G.prEvent_idealImpl_le_relabelImpl honestFirst P).trans_eq <|
    prEvent_congr_of_support _ _ _ fun _ hz ↦
      or_iff_left (not_conflict_of_mem_support_honestFirst hz)

/-- In the forger-first program, an event that, once the public point `true` is cached alone,
holds exactly when the derivation is drawn at `b` has probability `2⁻¹`. -/
theorem prEvent_forgerFirst_eq_inv_two (E : RelabelState (Bool →ₒ Bool) Unit Unit Bool → Prop)
    (b : Bool) (hE : ∀ C : (Bool →ₒ Bool).QueryCache, (∀ t, (C t).isSome ↔ t = true) →
      ∀ s, E (C, (∅ : ((Unit ⊕ Unit) →ₒ Bool).QueryCache).cacheQuery (.inl ()) s) ↔ s = b) :
    Pr{let z ← (simulateQ G.relabelImpl forgerFirst).run (∅, ∅)}[E z.2] = 2⁻¹ := by
  have hnot : ¬∃ k vs, G.childVals ((∅, ∅) : RelabelState (Bool →ₒ Bool) Unit Unit Bool) k =
      some vs ∧ G.pt k vs = true := by
    rintro ⟨k, vs, hk, -⟩
    rw [childVals_eq] at hk
    exact absurd hk (Option.some_ne_none _).symm
  -- After the first query, the event is decided by the drawn derivation.
  have hstep : ∀ w ∈ support ((G.relabelImpl (.inl (.inr true))).run (∅, ∅)),
      Pr{let z ← (G.relabelImpl (.inr ())).run w.2}[E z.2] = 2⁻¹ := by
    intro w hw
    rw [G.relabelImpl_run_pub_of_not_exists hnot, support_map] at hw
    obtain ⟨⟨_, C⟩, hb, rfl⟩ := hw
    have hC (t : Bool) : (C t).isSome ↔ t = true := by
      rw [QueryImpl.withCaching_run_isSome_apply_iff _ hb t, QueryCache.empty_apply,
        Option.isSome_none, Bool.false_eq_true, false_or]
    rw [CanonicalGraph.relabelImpl_apply_inr,
      RelabelState.drawCell_run_of_cell_eq_none (c := .inl ()) rfl, prEvent_map]
    calc _ = Pr{let s ← $ᵗ Bool}[s = b] := prEvent_congr _ _ _ (hE C hC)
      _ = 2⁻¹ := by
        rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_bool,
          Nat.cast_ofNat]
  let _ : MeasurableSpace (Bool × RelabelState (Bool →ₒ Bool) Unit Unit Bool) := ⊤
  simp only [forgerFirst, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [prEvent_bind_eq_lintegral_of_discrete]
  refine (lintegral_congr_ae
    (evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete hstep)).trans ?_
  rw [lintegral_const, evalDist_apply_univ_eq_one, mul_one]

/-- Querying `true` and then drawing the derivation conflicts with probability `2⁻¹`. -/
theorem prEvent_conflict_forgerFirst :
    Pr{let z ← (simulateQ G.relabelImpl forgerFirst).run (∅, ∅)}[G.Conflict z.2] = 2⁻¹ := by
  refine prEvent_forgerFirst_eq_inv_two _ true fun C hC s ↦ ?_
  refine ⟨fun ⟨k, vs, hk, hc⟩ ↦ ?_, fun hs ↦ ⟨(), [s], ?_, ?_⟩⟩
  · rw [childVals_eq, QueryCache.cacheQuery_self] at hk
    obtain rfl : [s] = vs := Option.some_inj.1 hk
    exact (hC s).1 hc
  · rw [childVals_eq, QueryCache.cacheQuery_self]; rfl
  · exact (hC s).2 hs

/-- For the forger-first program, the ideal game exceeds the relabelled game, read on the merged
state, by at most the conflict probability `2⁻¹`. -/
example (P : Bool × SecretEncoding.SplitCache (Bool →ₒ Bool) Unit Bool → Prop) :
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl (Bool →ₒ Bool) Unit Bool)
        forgerFirst).run (∅, ∅)}[P z] ≤
      Pr{let z ← (simulateQ G.relabelImpl forgerFirst).run (∅, ∅)}[P (z.1, G.toSplitCache z.2)] +
        2⁻¹ := by
  refine (G.prEvent_idealImpl_le_relabelImpl forgerFirst P).trans ?_
  rw [← prEvent_conflict_forgerFirst]
  exact prEvent_or_le _ _ _

/-- In the ideal game, the forger-first program always caches the public point `true`. -/
theorem prEvent_idealImpl_isSome_forgerFirst :
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl (Bool →ₒ Bool) Unit Bool)
        forgerFirst).run (∅, ∅)}[(z.2.1 true).isSome] = 1 := by
  refine prEvent_eq_one_of_forall_mem_support _ _ fun z hz ↦ ?_
  simp only [forgerFirst, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    mem_support_bind_iff] at hz
  obtain ⟨w, hw, hz⟩ := hz
  exact (SecretEncoding.isSome_fst_apply_iff_of_mem_support_idealImpl hz true).2
    (.inl ((SecretEncoding.isSome_fst_apply_iff_of_mem_support_idealImpl hw true).2 (.inr rfl)))

/-- In the relabelled game, read on the merged state, the forger-first program caches the public
point `true` only with probability `2⁻¹`: when the derivation is drawn at `true`, the merged
state reads `true` from the undrawn label of the node. -/
theorem prEvent_relabelImpl_isSome_forgerFirst :
    Pr{let z ← (simulateQ G.relabelImpl forgerFirst).run (∅, ∅)}[
      ((G.toSplitCache z.2).1 true).isSome] = 2⁻¹ := by
  refine prEvent_forgerFirst_eq_inv_two (fun st ↦ ((G.toSplitCache st).1 true).isSome) false
    fun C hC s ↦ ?_
  have hk : G.childVals (C, (∅ : ((Unit ⊕ Unit) →ₒ Bool).QueryCache).cacheQuery (.inl ()) s) ()
      = some [s] := by
    rw [childVals_eq, QueryCache.cacheQuery_self]; rfl
  cases s with
  | true =>
    change (G.merge _ (G.pt () [true])).isSome ↔ _
    rw [G.merge_apply_pt hk]
    simp only [cacheQuery_apply_inr, Option.map_none, Option.isSome_none, Bool.false_eq_true,
      Bool.true_eq_false]
  | false =>
    rw [CanonicalGraph.toSplitCache, G.merge_apply_of_not_exists]
    · exact iff_of_true ((hC true).2 rfl) rfl
    · rintro ⟨_, vs, hk', hpt⟩
      rw [hk] at hk'
      cases hk'
      exact Bool.false_ne_true hpt

/-- The conflict disjunct of the relabelling bound cannot be dropped. -/
example : ¬∀ P : Bool × SecretEncoding.SplitCache (Bool →ₒ Bool) Unit Bool → Prop,
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl (Bool →ₒ Bool) Unit Bool)
        forgerFirst).run (∅, ∅)}[P z] ≤
      Pr{let z ← (simulateQ G.relabelImpl forgerFirst).run (∅, ∅)}[
        P (z.1, G.toSplitCache z.2)] := fun h ↦ by
  have h' := h fun z ↦ (z.2.1 true).isSome
  rw [prEvent_idealImpl_isSome_forgerFirst, prEvent_relabelImpl_isSome_forgerFirst] at h'
  exact absurd h' (not_le.2 (ENNReal.inv_lt_one.2 ENNReal.one_lt_two))

/-! ## Merging under a secret encoding -/

/-- The derivation under secret `s` is read at the public point `s`. -/
def E : SecretEncoding (Bool →ₒ Bool) Bool Unit Bool where
  enc s _ := s
  range_eq _ _ := rfl
  injective _ _ _ _ := rfl

/-- At the point named by the secret, the merged split state reads the derivation. -/
example (s : Bool) (st : RelabelState (Bool →ₒ Bool) Unit Unit Bool) :
    E.merge s (G.toSplitCache st) s = st.2 (.inl ()) :=
  (E.merge_toSplitCache_apply_enc G s st ()).trans (by cases st.2 (.inl ()) <;> rfl)

/-- With the derivation drawn at `v` and the secret `!v`, the node's point `v` reads the node's
label. -/
example (v : Bool) {st : RelabelState (Bool →ₒ Bool) Unit Unit Bool}
    (h : st.2 (.inl ()) = some v) :
    E.merge (!v) (G.toSplitCache st) v = st.2 (.inr ()) :=
  (E.merge_toSplitCache_apply_pt G (!v) (k := ()) (vs := [v]) (by cases v <;> decide)
    ((childVals_eq st).trans (by rw [h]; rfl))).trans (by cases st.2 (.inr ()) <;> rfl)

/-- With the derivation undrawn, the point other than the secret reads the public cache. -/
example (s : Bool) {st : RelabelState (Bool →ₒ Bool) Unit Unit Bool}
    (h : st.2 (.inl ()) = none) :
    E.merge s (G.toSplitCache st) (!s) = st.1 (!s) :=
  E.merge_toSplitCache_apply_of_not_exists G s (by cases s <;> decide)
    fun ⟨_, _, hk, _⟩ ↦ by rw [childVals_eq, h] at hk; cases hk

end RelabelToy
