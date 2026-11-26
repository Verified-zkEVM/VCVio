/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.BLS.Abort

/-! # Selecting a fresh aggregate-forgery hash

The BLS deferred-challenge theorem applies to arbitrary output predicates. A fresh
eligible output message at the selected insertion index becomes a challenge-tagged entry
without an abort. The output predicate may include aggregate verification and distinctness.
-/

public section

open OracleComp OracleSpec

namespace BLS.Aggregate

/-- An output predicate together with a fresh eligible message at a fixed cache index. -/
@[expose] def FreshTarget {V M α : Type} (P : α → List M → Prop)
    (eligible : α → M → Prop) (j : ℕ) (z : α × OracleState V M) : Prop :=
  P z.1 z.2.signed ∧ ∃ msg, eligible z.1 msg ∧ msg ∉ z.2.signed ∧
    ∃ v, z.2.cache msg = some (v, j)

/-- The selected eligible message carries the challenge tag and the execution has not aborted. -/
@[expose] def ProgrammedTarget {V M α : Type} (P : α → List M → Prop)
    (eligible : α → M → Prop) (j : ℕ) (z : α × OracleState (Option V) M) : Prop :=
  P z.1 z.2.signed ∧ (∃ msg, eligible z.1 msg ∧ msg ∉ z.2.signed ∧
    z.2.cache msg = some (none, j)) ∧ ¬z.2.bad = true

/-- A fresh selected output transfers through the shared BLS deferred-challenge coupling.
This statement permits any verification predicate on the output and signing history. -/
theorem prEvent_freshTarget_le_programmed {V M G α : Type}
    [SampleableType V] [SampleableType G] [DecidableEq M]
    (f : V → G) (hf : Function.Bijective f) (sign : G → G) (j : ℕ)
    (oa : OracleComp ((unifSpec + (M →ₒ G)) + (M →ₒ G)) α)
    (P : α → List M → Prop) (eligible : α → M → Prop) :
    Pr{let z ← (simulateQ (indexedOracle (fun _ => $ᵗ V) f (sign ∘ f) (some j)) oa).run
        OracleState.empty}[FreshTarget P eligible j z] ≤
    Pr{let h ← ($ᵗ G : ProbComp G)
       let z ← (simulateQ (indexedOracle (tagDraw j) (fun tag => tag.elim h f)
         (fun tag => sign (tag.elim h f)) (some j)) oa).run OracleState.empty}[
      ProgrammedTarget P eligible j z] := by
  let run := (simulateQ (indexedOracle (fun _ => $ᵗ V) f (sign ∘ f) (some j)) oa).run
    (OracleState.empty : OracleState V M)
  have hle : Pr{let z ← run}[FreshTarget P eligible j z] ≤
      Pr{let w ← run >>= fun z => (fun st => (z.1, st)) <$> fillChallenge f j z.2}[
        ProgrammedTarget P eligible j (w.1, w.2.1)] := by
    apply prEvent_le_prEvent_bind_of_support
    intro z hz hw
    obtain ⟨hp, msg, hm, hns, v, hc⟩ := hw
    have hi := simulateQ_run_preservesInv _ _
      (indexedOracle_preserves_indexInv (fun _ => $ᵗ V) f (sign ∘ f) (some j))
      oa _ (indexInv_empty (some j)) z hz
    have hs := simulateQ_run_preservesInv _ _
      (indexedOracle_preserves_selectionInv (fun _ => $ᵗ V) f (sign ∘ f) j)
      oa _ (selectionInv_empty j) z hz
    have hsel := hs.selected msg v hc
    have hb := hi.not_bad_of_fresh hc hns
    simp only [fillChallenge, hsel, map_pure]
    suffices ProgrammedTarget P eligible j (z.1, tagState j z.2) by simp [this]
    refine ⟨hp, ⟨msg, hm, hns, ?_⟩, ?_⟩
    · simp [tagState, hc]
    · simpa only [tagState, hb] using Bool.false_ne_true
  have heq := simulateQ_fillChallenge_evalDistEq f hf sign j oa
    OracleState.empty (selectionInv_empty j)
  have hempty : fillChallenge f j (OracleState.empty : OracleState V M) =
      (fun h => (OracleState.empty, h)) <$> ($ᵗ G : ProbComp G) := by
    change (fun h => (tagState j OracleState.empty, h)) <$> ($ᵗ G : ProbComp G) = _
    rw [tagState_empty]
  have hev := heq.prEvent_eq (fun w => ProgrammedTarget P eligible j (w.1, w.2.1))
  simp only [hempty, bind_map_left, programmedOracle_run, map_bind, Functor.map_map] at hev
  simp only [run, map_bind, Functor.map_map] at hle
  exact hle.trans_eq hev

/-- Translating the challenge by any fixed mask preserves the fresh-target bound. The BLS
until-bad theorem permits scalar-derived signing responses away from the selected slot. -/
theorem prEvent_freshTarget_le_masked {V M G α : Type}
    [SampleableType V] [SampleableType G] [DecidableEq M] [AddGroup G]
    (f : V → G) (hf : Function.Bijective f) (sign : G → G)
    (sign' : Option V → G) (hsign : ∀ v, sign (f v) = sign' (some v))
    (j : ℕ) (mask : G)
    (oa : OracleComp ((unifSpec + (M →ₒ G)) + (M →ₒ G)) α)
    (P : α → List M → Prop) (eligible : α → M → Prop) :
    Pr{let z ← (simulateQ (indexedOracle (fun _ => $ᵗ V) f (sign ∘ f) (some j)) oa).run
        OracleState.empty}[FreshTarget P eligible j z] ≤
    Pr{let h ← ($ᵗ G : ProbComp G)
       let z ← (simulateQ (indexedOracle (tagDraw j) (fun tag => tag.elim (h + mask) f)
         sign' (some j)) oa).run OracleState.empty}[ProgrammedTarget P eligible j z] := by
  let run := fun h => (simulateQ (indexedOracle (tagDraw j) (fun tag => tag.elim h f)
    (fun tag => sign (tag.elim h f)) (some j)) oa).run
      (OracleState.empty : OracleState (Option V) M)
  have hshift := (SampleableType.map_uniformSample_evalDistEq_of_bijective
    (Equiv.addRight mask).bijective).bind_left run
  have heq := hshift.prEvent_eq (ProgrammedTarget P eligible j)
  simp only [bind_map_left, map_bind] at heq
  have hle := prEvent_freshTarget_le_programmed f hf sign j oa P eligible
  change _ ≤ Pr{let h ← ($ᵗ G : ProbComp G); let z ← run h}[
    ProgrammedTarget P eligible j z] at hle
  rw [← heq] at hle
  refine hle.trans ?_
  let : MeasurableSpace G := ⊤
  rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
  apply MeasureTheory.lintegral_mono
  intro h
  change Pr{let z ← (simulateQ (indexedOracle (tagDraw j)
      (fun tag => tag.elim (h + mask) f) (fun tag => sign (tag.elim (h + mask) f))
      (some j)) oa).run OracleState.empty}[ProgrammedTarget P eligible j z] ≤ _
  have habort := prEvent_indexedOracle_and_not_bad_le
    (fun tag => tag.elim (h + mask) f) (fun tag => sign (tag.elim (h + mask) f))
    sign' hsign j oa (ProgrammedTarget P eligible j)
  have hp : (fun z : α × OracleState (Option V) M =>
      ProgrammedTarget P eligible j z ∧ ¬z.2.bad = true) =
      ProgrammedTarget P eligible j := by
    funext z
    apply propext
    simp only [ProgrammedTarget, and_assoc, and_self]
  rw [hp] at habort
  exact habort

/-- Selecting a slot for passive bookkeeping does not change its fresh-target probability. -/
theorem prEvent_freshTarget_eraseSelection {V M G α : Type} [DecidableEq M]
    (draw : ℕ → ProbComp V) (hash sign : V → G) (j : ℕ)
    (oa : OracleComp ((unifSpec + (M →ₒ G)) + (M →ₒ G)) α)
    (P : α → List M → Prop) (eligible : α → M → Prop) :
    Pr{let z ← (simulateQ (indexedOracle draw hash sign none) oa).run OracleState.empty}[
      FreshTarget P eligible j z] =
    Pr{let z ← (simulateQ (indexedOracle draw hash sign (some j)) oa).run OracleState.empty}[
      FreshTarget P eligible j z] := by
  have h := simulateQ_indexedOracle_eraseSelection draw hash sign (some j) oa OracleState.empty
  have hp := congrArg (fun mx => Pr{let z ← mx}[FreshTarget P eligible j z]) h
  simp only [prEvent_map, FreshTarget, OracleState.eraseSelection, OracleState.empty,
    Prod.map, id_eq] at hp ⊢
  exact hp.symm

end BLS.Aggregate
