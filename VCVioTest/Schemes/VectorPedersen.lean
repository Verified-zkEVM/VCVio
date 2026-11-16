/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.VectorPedersen
public import Mathlib.Algebra.Field.ZMod

/-!
# Vector Pedersen regression tests

Two-coordinate commitments over `ZMod 101` exercise the named relation and DLog reductions,
the generic bound, and perfect hiding at a fixed and at a random generating blinding base. The
generic binder that compares the first two message handles wins with probability exactly `1/101`,
which pins the table layout and commitment readout of `ofGeneric`. All fixtures are local.
-/

public section

open OracleComp OracleSpec CommitmentScheme DiscreteLogRelation
open scoped ENNReal

namespace VectorPedersen

/-- Two-coordinate binding over `ZMod 101` reduces to the named discrete-log adversary. -/
theorem binding_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    ∀ binder : BindingAdversary (Option (Fin 2) → ZMod 101) (Fin 2 → ZMod 101)
        (ZMod 101) (ZMod 101),
      (scheme (uniformSetup (F := ZMod 101) 1)).bindingAdvantage binder ≤
        Pr{let b ← (DiffieHellman.dlogExperiment 1
          (plainReduction (bindingReduction binder)))}[b = true] + (1 / 101 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  intro binder
  refine (bindingAdvantage_le_dlog (1 : ZMod 101) one_ne_zero binder).trans_eq ?_
  simp [ZMod.card]

/-- Blinding by `1` perfectly hides a two-coordinate message over arbitrary fixed message bases. -/
theorem hiding_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    (scheme (F := ZMod 101)
      (pure (fun i : Option (Fin 2) => i.elim (1 : ZMod 101) ![3, 7]))).PerfectlyHiding := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  exact perfectlyHiding ![3, 7] (1 : ZMod 101)
    (by
      simp only [smul_eq_mul, mul_one]
      exact ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩)

/-- A random choice between the blinding bases `1` and `2` perfectly hides, since every possible
parameter vector has a generating blinding base. -/
theorem hiding_two_setups_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    (scheme (F := ZMod 101) (do
      let b ← $ᵗ Bool
      pure (fun i : Option (Fin 2) =>
        i.elim (if b then (1 : ZMod 101) else 2) ![3, 7]))).PerfectlyHiding := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  apply perfectlyHiding_of_forall
  intro pp hpp
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hpp
  obtain ⟨b, _, rfl⟩ := hpp
  have hbij (c : ZMod 101) (hc : c ≠ 0) : Function.Bijective (· • c : ZMod 101 → ZMod 101) :=
    ⟨smul_left_injective _ hc,
      fun y => ⟨y * c⁻¹, by simp [smul_eq_mul, mul_assoc, inv_mul_cancel₀ hc]⟩⟩
  cases b <;> exact hbij _ (by decide)

/-- A free-equality generic binder on three initial bases has advantage at most `7 / 101`. -/
theorem generic_binding_zmod_101 :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    let A : GenericBinder (ZMod 101) (Fin 2) := show
      OracleComp (GroupModel.genSpec (ZMod 101) GroupModel.groupSig)
        (ℕ × (Fin 2 → ZMod 101) × ZMod 101 × (Fin 2 → ZMod 101) × ZMod 101) from do
      let eq : Bool ← (GroupModel.genSpec (ZMod 101) GroupModel.groupSig).query (.inl (.eq () 0 1))
      pure (0, ![1, 0], 0, (if eq then ![0, 1] else ![1, 0]), 0)
    (scheme (uniformSetup (F := ZMod 101) (ι := Fin 2) (1 : ZMod 101))).bindingAdvantage
      (ofGeneric A) ≤ (7 / 101 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  dsimp only
  apply (bindingAdvantage_ofGeneric_le (1 : ZMod 101) one_ne_zero _ 0 ?_).trans
  · norm_num [ZMod.card, Nat.choose, FinEnum.card_fin]
  · exact ⟨by decide, fun _ => trivial⟩

/-- Two message bases of a uniform setup over `ZMod 101` agree with probability `1/101`. -/
private theorem prEvent_bases_eq :
    Pr{let x ← $ᵗ (Option (Fin 2) → ZMod 101)}[x (some 0) = x (some 1)] =
      (1 / 101 : ℝ≥0∞) := by
  let E : ZMod 101 × (ZMod 101 × ZMod 101) ≃ (Option (Fin 2) → ZMod 101) :=
    { toFun := fun p i => i.elim p.2.1 ![p.1 + p.2.2, p.2.2]
      invFun := fun y => (y (some 0) - y (some 1), y none, y (some 1))
      left_inv := fun p => by simp
      right_inv := fun y => by
        funext i
        rcases i with _ | i
        · rfl
        · fin_cases i <;> simp }
  rw [← SampleableType.prEvent_uniformSample_equiv E]
  have h (p : ZMod 101 × (ZMod 101 × ZMod 101)) : E p (some 0) = E p (some 1) ↔ p.1 = 0 := by
    simp [E]
  rw [prEvent_congr _ _ _ h, SampleableType.prEvent_uniformSample_fst (fun a : ZMod 101 => a = 0),
    SampleableType.prEvent_uniformSample_eq_singleton, ZMod.card]
  simp

/-- The binder of `generic_binding_zmod_101` wins exactly when the first two message bases agree,
so its advantage is exactly `1/101`. This pins the readout of `ofGeneric`: the table lists
`some 0`, `some 1` and `none` in that order, and the commitment is read from the returned handle.
A readout that ignored the handle and returned the zero commitment would need both message bases
to vanish, with advantage `1/101²`. -/
theorem generic_binding_zmod_101_exact :
    letI : Fact (Nat.Prime 101) := ⟨by decide⟩
    let A : GenericBinder (ZMod 101) (Fin 2) := show
      OracleComp (GroupModel.genSpec (ZMod 101) GroupModel.groupSig)
        (ℕ × (Fin 2 → ZMod 101) × ZMod 101 × (Fin 2 → ZMod 101) × ZMod 101) from do
      let eq : Bool ← (GroupModel.genSpec (ZMod 101) GroupModel.groupSig).query (.inl (.eq () 0 1))
      pure (0, ![1, 0], 0, (if eq then ![0, 1] else ![1, 0]), 0)
    (scheme (uniformSetup (F := ZMod 101) (ι := Fin 2) (1 : ZMod 101))).bindingAdvantage
      (ofGeneric A) = (1 / 101 : ℝ≥0∞) := by
  let : Fact (Nat.Prime 101) := ⟨by decide⟩
  intro A
  have hrun (pp : Option (Fin 2) → ZMod 101) :
      ofGeneric (G := ZMod 101) A pp =
        pure (pp (some 0), ![1, 0], 0,
          (if pp (some 0) = pp (some 1) then ![0, 1] else ![1, 0]), 0) := by
    change (pure (pp (some 0), ![1, 0], 0,
      (if decide (pp (some 0) = pp (some 1)) = true then ![0, 1] else ![1, 0]), 0) :
        ProbComp _) = _
    simp
  rw [bindingAdvantage, ← prEvent_eq_evalDist_singleton _ true]
  simp only [bindingExperiment, scheme, uniformSetup, bind_pure_comp, hrun, map_pure]
  rw [← prEvent_bases_eq, prEvent_map, prEvent_map]
  apply prEvent_congr
  intro x
  -- The commitment sums over `Fin 2` with the `Fintype` instance of its enumeration.
  have huniv : @Finset.univ (Fin 2) FinEnum.instFintype = Finset.univ := by
    congr 1
  by_cases hx : x (some 0) = x (some 1)
  · simp [hx, commitValue, representationEval, huniv, Fin.sum_univ_two]
  · simp [hx, commitValue, representationEval, huniv, Fin.sum_univ_two]

end VectorPedersen
