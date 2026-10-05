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
    G.childVals st () = (st.table ()).map fun v ↦ [v] := by
  cases h : st.table () with
  | some v => exact G.childVals_eq_some_iff.2 (.cons h .nil)
  | none =>
    cases hc : G.childVals st () with
    | none => rfl
    | some vs =>
      have hf : List.Forall₂ (fun c v ↦ st.cell c = some v) [.inl ()] vs :=
        G.childVals_eq_some_iff.1 hc
      rcases hf with _ | ⟨hv, -⟩
      rw [RelabelState.cell_inl, h] at hv
      exact absurd hv (Option.some_ne_none _).symm

/-- A state whose public cache is empty has no conflict. -/
theorem not_conflict_of_cache_eq_empty {st : RelabelState (Bool →ₒ Bool) Unit Unit Bool}
    (h : st.cache = ∅) : ¬G.Conflict st := by
  rintro ⟨_, _, -, hc⟩
  rw [h, QueryCache.empty_apply] at hc
  exact Bool.false_ne_true hc

/-- Drawing the derivation and then querying its value never conflicts. -/
theorem not_conflict_of_mem_support_honestFirst {z}
    (hz : z ∈ support ((simulateQ G.relabelImpl honestFirst).run ∅)) : ¬G.Conflict z.2 := by
  simp only [honestFirst, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    mem_support_bind_iff] at hz
  obtain ⟨w, hw, hz⟩ := hz
  rw [CanonicalGraph.relabelImpl_derive,
    RelabelState.drawCell_run_of_cell_eq_none (c := .inl ()) rfl, support_map] at hw
  obtain ⟨s, -, rfl⟩ := hw
  have hk : G.childVals ((∅ : RelabelState (Bool →ₒ Bool) Unit Unit Bool).setCell (.inl ()) s) ()
      = some [s] := by
    rw [childVals_eq]; rfl
  change z ∈ support ((G.relabelImpl (.inl (.inr (G.pt () [s])))).run _) at hz
  rw [G.relabelImpl_run_pt hk, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rw [RelabelState.drawCell_run_of_cell_eq_none (c := .inr ()) rfl, support_map] at hw
  obtain ⟨u, -, rfl⟩ := hw
  exact not_conflict_of_cache_eq_empty rfl

/-- For the honest-first program, the ideal game is dominated by the relabelled game read on the
merged state. -/
example (P : Bool × SecretEncoding.SplitCache (Bool →ₒ Bool) Unit Bool → Prop) :
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl (Bool →ₒ Bool) Unit Bool)
        honestFirst).run (∅, ∅)}[P z] ≤
      Pr{let z ← (simulateQ G.relabelImpl honestFirst).run ∅}[P (z.1, G.toSplitCache z.2)] :=
  (G.prEvent_idealImpl_le_relabelImpl honestFirst P).trans_eq <|
    prEvent_congr_of_support _ _ _ fun _ hz ↦
      or_iff_left (not_conflict_of_mem_support_honestFirst hz)

/-- Querying `true` and then drawing the derivation conflicts with probability `2⁻¹`. -/
theorem prEvent_conflict_forgerFirst :
    Pr{let z ← (simulateQ G.relabelImpl forgerFirst).run ∅}[G.Conflict z.2] = 2⁻¹ := by
  have hnot : ¬∃ k vs, G.childVals (∅ : RelabelState (Bool →ₒ Bool) Unit Unit Bool) k = some vs ∧
      G.pt k vs = true := by
    rintro ⟨k, vs, hk, -⟩
    rw [childVals_eq] at hk
    exact absurd hk (Option.some_ne_none _).symm
  -- After the first query, a conflict arises exactly when the derivation is drawn at `true`.
  have hstep : ∀ w ∈ support ((G.relabelImpl (.inl (.inr true))).run ∅),
      Pr{let z ← (G.relabelImpl (.inr ())).run w.2}[G.Conflict z.2] = 2⁻¹ := by
    intro w hw
    rw [G.relabelImpl_run_pub_of_not_exists hnot, support_map] at hw
    obtain ⟨⟨b, C⟩, hb, rfl⟩ := hw
    have hC (t : Bool) : (C t).isSome ↔ t = true := by
      rw [QueryImpl.withCaching_run_isSome_apply_iff _ hb t, RelabelState.cache_empty,
        QueryCache.empty_apply, Option.isSome_none, Bool.false_eq_true, false_or]
    rw [CanonicalGraph.relabelImpl_derive,
      RelabelState.drawCell_run_of_cell_eq_none (c := .inl ()) rfl, prEvent_map]
    calc _ = Pr{let s ← $ᵗ Bool}[s = true] := prEvent_congr _ _ _ fun s ↦ by
          refine ⟨fun ⟨k, vs, hk, hc⟩ ↦ ?_, fun hs ↦ ⟨(), [s], ?_, ?_⟩⟩
          · rw [childVals_eq] at hk
            obtain rfl : [s] = vs := Option.some_inj.1 hk
            exact (hC s).1 hc
          · rw [childVals_eq]; rfl
          · exact (hC s).2 hs
      _ = 2⁻¹ := by
        rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_bool,
          Nat.cast_ofNat]
  let _ : MeasurableSpace (Bool × RelabelState (Bool →ₒ Bool) Unit Unit Bool) := ⊤
  simp only [forgerFirst, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [prEvent_bind_eq_lintegral_of_discrete]
  refine (lintegral_congr_ae
    (evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete hstep)).trans ?_
  rw [lintegral_const, evalDist_apply_univ_eq_one, mul_one]

/-- For the forger-first program, the ideal game exceeds the relabelled game, read on the merged
state, by at most the conflict probability `2⁻¹`. -/
example (P : Bool × SecretEncoding.SplitCache (Bool →ₒ Bool) Unit Bool → Prop) :
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl (Bool →ₒ Bool) Unit Bool)
        forgerFirst).run (∅, ∅)}[P z] ≤
      Pr{let z ← (simulateQ G.relabelImpl forgerFirst).run ∅}[P (z.1, G.toSplitCache z.2)] +
        2⁻¹ := by
  refine (G.prEvent_idealImpl_le_relabelImpl forgerFirst P).trans ?_
  rw [← prEvent_conflict_forgerFirst]
  exact prEvent_or_le _ _ _

end RelabelToy
