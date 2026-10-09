/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio.OracleComp.QueryTracking.RandomOracle.Defer
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

/-!
# Touch deferral on a one-node graph

A random oracle on `Bool` has one derivation `()` and one node `()`, whose only child is the
derivation and whose point is the derivation's value. The program touches the derivation and then
queries the public point `true`, a guess of the touched value.

* In the eager game the touch draws the derivation, and the guess reads the node's label exactly
  when the derivation is `true`, with probability `2⁻¹`.
* In the deferred game the guess finds the derivation undrawn and is answered by the public
  cache; the end fill then draws the derivation, so the label is never drawn and a conflict
  arises exactly when the derivation is `true`, with probability `2⁻¹`.
* The deferral bound is therefore tight here, and its conflict disjunct cannot be dropped.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace DeferToy

/-- Programs with uniform draws, a public random oracle on `Bool`, one derivation query and the
label operations of one node. -/
abbrev spec := (Bool →ₒ Bool).withLabels Unit Unit Bool

/-- One node, whose only child is the derivation and whose point is the derivation's value. -/
def G : CanonicalGraph (Bool →ₒ Bool) Unit Unit Bool where
  ch _ := [.inl ()]
  pt _ vs := vs.headD false
  range_eq _ _ := rfl
  pt_inj {_ _ vs vs'} h h' hpt := by
    match vs, vs', h, h' with
    | [v], [v'], _, _ => exact ⟨rfl, by simpa using hpt⟩

/-- Touch the derivation, then query the public point `true`. -/
def touchThenGuess : OracleComp spec Bool := do
  let _ ← liftM (spec.query (.inr (.inl (.inl ()))))
  liftM (spec.query (.inl (.inl (.inr true))))

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

/-- No node has its children drawn in a state with no drawn cell. -/
theorem not_exists_childVals_empty (t : Bool) (C : (Bool →ₒ Bool).QueryCache) :
    ¬∃ k vs, G.childVals ((C, ∅) : RelabelState (Bool →ₒ Bool) Unit Unit Bool) k = some vs ∧
      G.pt k vs = t := by
  rintro ⟨k, vs, hk, -⟩
  rw [childVals_eq] at hk
  exact absurd hk (Option.some_ne_none _).symm

/-- In the deferred game the touch is recorded and the guess is cached as a public answer. -/
theorem deferredImpl_run_touchThenGuess :
    (simulateQ G.deferredImpl touchThenGuess).run ((∅, ∅), []) =
      (fun u ↦ (u, ((((∅ : (Bool →ₒ Bool).QueryCache).cacheQuery true u), ∅), [.inl ()]))) <$>
        ($ᵗ Bool) := by
  simp only [touchThenGuess, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    CanonicalGraph.deferredImpl_run_touch, pure_bind, List.nil_append]
  rw [G.deferredImpl_run_inl (.inl (.inr true)),
    G.relabelImpl_run_pub_of_not_exists (not_exists_childVals_empty _ _), randomOracle.run_eq]
  simp [QueryCache.empty_apply]

/-- The end fill of the touched derivation draws it. -/
theorem endFill_touched (C : (Bool →ₒ Bool).QueryCache) :
    RelabelState.endFill ((C, ∅), [.inl ()]) =
      (fun v ↦ (C, (∅ : ((Unit ⊕ Unit) →ₒ Bool).QueryCache).cacheQuery (.inl ()) v)) <$>
        ($ᵗ Bool) := by
  rw [RelabelState.endFill_eq]
  simp [QueryCache.empty_apply]

/-- The final state of the deferred game after the end fill: the guess cached at a fair coin
`u`, and the derivation drawn at a fair coin `v`. -/
noncomputable def deferredFinal : ProbComp (RelabelState (Bool →ₒ Bool) Unit Unit Bool) := do
  let u ← $ᵗ Bool
  let v ← $ᵗ Bool
  pure ((∅ : (Bool →ₒ Bool).QueryCache).cacheQuery true u,
    (∅ : ((Unit ⊕ Unit) →ₒ Bool).QueryCache).cacheQuery (.inl ()) v)

/-- After the end fill, the final state of the deferred game is `deferredFinal`. -/
theorem prEvent_deferredImpl_endFill (E : RelabelState (Bool →ₒ Bool) Unit Unit Bool → Prop) :
    Pr{let z ← (simulateQ G.deferredImpl touchThenGuess).run ((∅, ∅), [])
       let st ← RelabelState.endFill z.2}[E st] = Pr{let st ← deferredFinal}[E st] := by
  simp only [deferredImpl_run_touchThenGuess, bind_map_left, endFill_touched, deferredFinal,
    bind_assoc, pure_bind]

/-- In the deferred game the label of the node is never drawn. -/
theorem prEvent_deferredImpl_label :
    Pr{let z ← (simulateQ G.deferredImpl touchThenGuess).run ((∅, ∅), [])
       let st ← RelabelState.endFill z.2}[(st.2 (.inr ())).isSome] = 0 := by
  rw [prEvent_deferredImpl_endFill]
  refine prEvent_eq_zero_of_forall_mem_support _ _ fun st hst ↦ ?_
  simp only [deferredFinal, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hst
  obtain ⟨u, -, v, -, rfl⟩ := hst
  simp [QueryCache.empty_apply]

/-- In the deferred game a conflict arises exactly when the derivation is drawn at the guess. -/
theorem prEvent_deferredImpl_conflict :
    Pr{let z ← (simulateQ G.deferredImpl touchThenGuess).run ((∅, ∅), [])
       let st ← RelabelState.endFill z.2}[G.Conflict st] = 2⁻¹ := by
  have hconf : ∀ u v, G.Conflict ((∅ : (Bool →ₒ Bool).QueryCache).cacheQuery true u,
      (∅ : ((Unit ⊕ Unit) →ₒ Bool).QueryCache).cacheQuery (.inl ()) v) ↔ v = true := by
    intro u v
    have hk : G.childVals ((∅ : (Bool →ₒ Bool).QueryCache).cacheQuery true u,
        (∅ : ((Unit ⊕ Unit) →ₒ Bool).QueryCache).cacheQuery (.inl ()) v) () = some [v] := by
      rw [childVals_eq, QueryCache.cacheQuery_self]; rfl
    refine ⟨fun ⟨k, vs, hk', hc⟩ ↦ ?_, fun hv ↦ ⟨(), [v], hk, ?_⟩⟩
    · rw [hk] at hk'
      cases hk'
      cases v
      · simp [G, QueryCache.empty_apply] at hc
      · rfl
    · subst hv
      simp [G]
  rw [prEvent_deferredImpl_endFill]
  simp only [deferredFinal, bind_assoc, pure_bind, hconf]
  let _ : MeasurableSpace Bool := ⊤
  rw [prEvent_bind_bind_eq_lintegral_of_discrete]
  simp only [lintegral_const, evalDist_apply_univ_eq_one, mul_one]
  rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_bool, Nat.cast_ofNat]

/-- The final state of the eager game when the touch draws the derivation at `v` and the guess
is answered by `u`: the guess draws the node's label at `u` when `v` is `true`, and is cached as a
public answer `u` otherwise. -/
def eagerFinal (v u : Bool) : RelabelState (Bool →ₒ Bool) Unit Unit Bool :=
  let cells := (∅ : ((Unit ⊕ Unit) →ₒ Bool).QueryCache).cacheQuery (.inl ()) v
  if v then (∅, cells.cacheQuery (.inr ()) u)
  else ((∅ : (Bool →ₒ Bool).QueryCache).cacheQuery true u, cells)

/-- In the eager game the touch draws the derivation at a fair coin `v`, and the guess is answered
by a fair coin `u`, reading the node's label exactly when `v` is `true`. -/
theorem eagerImpl_run_touchThenGuess :
    (simulateQ G.eagerImpl touchThenGuess).run (∅, ∅) =
      (do let v ← $ᵗ Bool; let u ← $ᵗ Bool; pure (u, eagerFinal v u)) := by
  simp only [touchThenGuess, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    CanonicalGraph.eagerImpl_apply_inr, RelabelState.labelImpl, bind_map_left]
  rw [RelabelState.drawCell_run_of_cell_eq_none (c := .inl ())
    (st := ((∅, ∅) : RelabelState (Bool →ₒ Bool) Unit Unit Bool)) rfl, bind_map_left]
  refine bind_congr fun v ↦ ?_
  set st : RelabelState (Bool →ₒ Bool) Unit Unit Bool :=
    (∅, (∅ : ((Unit ⊕ Unit) →ₒ Bool).QueryCache).cacheQuery (.inl ()) v)
  have hk : G.childVals st () = some [v] := by
    rw [childVals_eq, QueryCache.cacheQuery_self]; rfl
  cases v with
  | true =>
    have hl : st.2 (.inr ()) = none :=
      (QueryCache.cacheQuery_of_ne _ _ Sum.inr_ne_inl).trans (QueryCache.empty_apply _)
    change (G.relabelImpl (.inl (.inr (G.pt () [true])))).run st = _
    rw [G.relabelImpl_run_pt hk, RelabelState.drawCell_run_of_cell_eq_none hl, Functor.map_map,
      map_eq_bind_pure_comp]
    rfl
  | false =>
    have hnot : ¬∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = true := by
      rintro ⟨k, vs, hk', hpt⟩
      rw [hk] at hk'
      cases hk'
      exact Bool.false_ne_true hpt
    rw [CanonicalGraph.eagerImpl_apply_inl, G.relabelImpl_run_pub_of_not_exists hnot,
      randomOracle.run_eq]
    simp [QueryCache.empty_apply, eagerFinal, st]

/-- In the eager game the guess reads the node's label exactly when the touched derivation is
`true`. -/
theorem prEvent_eagerImpl_label :
    Pr{let z ← (simulateQ G.eagerImpl touchThenGuess).run (∅, ∅)}[(z.2.2 (.inr ())).isSome] =
      2⁻¹ := by
  have hlabel : ∀ v u, ((eagerFinal v u).2 (.inr ())).isSome = v := by
    intro v u
    cases v <;> simp [eagerFinal, QueryCache.empty_apply]
  rw [eagerImpl_run_touchThenGuess]
  simp only [bind_assoc, pure_bind, hlabel]
  rw [prEvent_bind_bind_swap ($ᵗ Bool) ($ᵗ Bool) fun v _ ↦ v = true]
  let _ : MeasurableSpace Bool := ⊤
  rw [prEvent_bind_bind_eq_lintegral_of_discrete]
  simp only [lintegral_const, evalDist_apply_univ_eq_one, mul_one]
  rw [SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_bool, Nat.cast_ofNat]

/-- In the eager game the guess never creates a conflict: when it hits the touched value it reads
the label, and otherwise it caches a point that is not the node's. -/
theorem not_conflict_of_mem_support_eagerImpl {z}
    (hz : z ∈ support ((simulateQ G.eagerImpl touchThenGuess).run (∅, ∅))) : ¬G.Conflict z.2 := by
  rw [eagerImpl_run_touchThenGuess] at hz
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨v, -, u, -, rfl⟩ := hz
  have hcell : (eagerFinal v u).2 (.inl ()) = some v := by
    cases v <;> simp [eagerFinal]
  rintro ⟨k, vs, hk, hc⟩
  rw [childVals_eq, hcell, Option.map_some, Option.some_inj] at hk
  subst hk
  cases v <;> cases u <;> simp_all [eagerFinal, QueryCache.empty_apply, G]

/-- In the eager game no conflict arises. -/
theorem prEvent_eagerImpl_conflict :
    Pr{let z ← (simulateQ G.eagerImpl touchThenGuess).run (∅, ∅)}[G.Conflict z.2] = 0 :=
  prEvent_eq_zero_of_forall_mem_support _ _ fun _ hz ↦ not_conflict_of_mem_support_eagerImpl hz

/-- The deferral bound at the label event: both sides are `2⁻¹`, the right-hand one carried
entirely by the conflict. -/
example : Pr{let z ← (simulateQ G.eagerImpl touchThenGuess).run (∅, ∅)}[
      (z.2.2 (.inr ())).isSome] ≤
    Pr{let z ← (simulateQ G.deferredImpl touchThenGuess).run ((∅, ∅), [])
       let st ← RelabelState.endFill z.2}[(st.2 (.inr ())).isSome ∨ G.Conflict st] :=
  G.prEvent_eagerImpl_le_deferredImpl_empty touchThenGuess fun z ↦ (z.2.2 (.inr ())).isSome

/-- The conflict disjunct of the deferral bound cannot be dropped. -/
example : ¬∀ P : Bool × RelabelState (Bool →ₒ Bool) Unit Unit Bool → Prop,
    Pr{let z ← (simulateQ G.eagerImpl touchThenGuess).run (∅, ∅)}[P z] ≤
      Pr{let z ← (simulateQ G.deferredImpl touchThenGuess).run ((∅, ∅), [])
         let st ← RelabelState.endFill z.2}[P (z.1, st)] := fun h ↦ by
  have h' := h fun z ↦ (z.2.2 (.inr ())).isSome
  rw [prEvent_eagerImpl_label, prEvent_deferredImpl_label] at h'
  exact absurd h' (by simp)

end DeferToy
