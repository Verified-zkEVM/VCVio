/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.CommitmentScheme
public import VCVio.CryptoFoundations.HardnessAssumptions.DiscreteLogRelation.Algebra
public import VCVio.CryptoFoundations.GroupModel.GenericRelation

/-!
 # Vector Pedersen commitments

The public basis has one blinding slot `none` and message slots `some i`. Commitment is
`∑ i, a i • gs i + r • h`. Correctness holds for every setup, and perfect hiding holds at
parameters whose blinding base generates the group. Uniform setup samples every slot, including
the blinding slot; its binding advantage reduces to a discrete-log relation on `Option ι`.
All security bounds name the coefficient-subtraction reduction.
-/

public section

open OracleComp OracleSpec CommitmentScheme DiscreteLogRelation
open scoped ENNReal

namespace VectorPedersen

variable {F G ι : Type}

/-- Commit to a vector using a separate blinding base. -/
@[expose] def commitValue [Fintype ι] [Semiring F] [AddCommMonoid G] [Module F G]
    (gs : ι → G) (h : G) (a : ι → F) (r : F) : G := representationEval gs a + r • h

/-- Vector Pedersen with an explicit distribution of public parameters.
The `none` slot is the blinding base and `some i` is message generator `i`. -/
@[expose] def scheme [Fintype ι] [Field F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (setup : ProbComp (Option ι → G)) : CommitmentScheme (Option ι → G) (ι → F) G F where
  setup := setup
  commit pp a := do
    let r ← $ᵗ F
    pure (commitValue (fun i => pp (some i)) (pp none) a r, r)
  verify pp a c r := decide (commitValue (fun i => pp (some i)) (pp none) a r = c)

/-- Uniform public parameters as independently sampled multiples of a generator. -/
@[expose] noncomputable def uniformSetup [Fintype ι] [DecidableEq ι]
    [Field F] [SampleableType F] [AddCommGroup G] [Module F G]
    (g : G) : ProbComp (Option ι → G) := do
  let x ← $ᵗ (Option ι → F)
  pure (fun i => x i • g)

/-- Every honest opening verifies, for any public-parameter distribution. -/
theorem correct [Fintype ι] [Field F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (setup : ProbComp (Option ι → G)) : (scheme (F := F) setup).PerfectlyCorrect := by
  intro pp _ a cd h
  change cd ∈ support (do let r ← $ᵗ F; pure (commitValue _ _ a r, r)) at h
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at h
  obtain ⟨r, _, rfl⟩ := h
  simp [scheme]

/-- At any fixed parameters with a generating blinding base, the commitment is perfectly hiding. -/
theorem perfectlyHiding [Fintype ι] [Field F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (gs : ι → G) (h : G) (hh : Function.Bijective (· • h : F → G)) :
    (scheme (F := F) (pure (fun i => i.elim h gs))).PerfectlyHiding := by
  let : MeasurableSpace G := ⊤
  intro pp hpp a b
  simp only [scheme, support_pure, Set.mem_singleton_iff] at hpp
  subst pp
  obtain ⟨d, hd⟩ := hh.surjective (representationEval gs a - representationEval gs b)
  have hb : Function.Bijective (fun r : F => r + d) :=
    ⟨fun _ _ he => add_right_cancel he, fun r => ⟨r - d, sub_add_cancel r d⟩⟩
  have he := (SampleableType.map_uniformSample_evalDistEq_of_bijective hb).map
    (fun r => commitValue gs h b r)
  have hv (r : F) : commitValue gs h b (r + d) = commitValue gs h a r := by
    simp only [commitValue, add_smul, hd]
    abel
  simpa [scheme, Functor.map_map, Function.comp_def, hv] using he.evalDist_eq

/-- The coefficient difference of two vector openings, including their blinding scalars. -/
@[expose] def openingDifference [Sub F] (a b : ι → F) (r s : F) : Option ι → F :=
  fun i => i.elim (r - s) (a - b)

/-- Subtract the two openings returned by a binding adversary to obtain relation coefficients. -/
@[expose] def bindingReduction [Sub F]
    (binder : BindingAdversary (Option ι → G) (ι → F) G F) :
    Adversary F G (Option ι) unifSpec := fun pp => do
  let (_, a, r, b, s) ← binder pp
  pure (openingDifference a b r s)

private theorem openingDifference_wins [Fintype ι] [Field F]
    [AddCommGroup G] [Module F G]
    (pp : Option ι → G) (a b : ι → F) (r s : F)
    (hne : a ≠ b)
    (he : commitValue (fun i => pp (some i)) (pp none) a r =
      commitValue (fun i => pp (some i)) (pp none) b s) :
    openingDifference a b r s ≠ 0 ∧
      ∑ i, openingDifference a b r s i • pp i = 0 := by
  constructor
  · intro hz
    apply hne
    apply sub_eq_zero.mp
    funext i
    exact congrFun hz (some i)
  · have hd := sub_eq_zero.mpr he
    simpa [commitValue, representationEval, openingDifference, Fintype.sum_option,
      sub_smul, Finset.sum_sub_distrib, add_sub_add_comm, add_comm] using hd

/-- Binding reduces without loss to the relation experiment on the full `Option ι` basis. -/
theorem bindingAdvantage_le_relation [Fintype ι] [DecidableEq ι]
    [Field F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (g : G) (binder : BindingAdversary (Option ι → G) (ι → F) G F) :
    (scheme (uniformSetup (F := F) (ι := ι) g)).bindingAdvantage binder ≤
      Pr{let b ← plainExperiment g (bindingReduction binder)}[b = true] := by
  rw [bindingAdvantage, ← prEvent_eq_evalDist_singleton _ true]
  simp only [bindingExperiment, scheme, uniformSetup, plainExperiment, experiment,
    plainAdversary, StateT.run'_eq, map_run_plainImpl, bindingReduction, prEvent_norm]
  apply prEvent_bind_mono_of_support
  intro x _
  apply prEvent_mono
  rintro ⟨c, a, r, b, s⟩ hw
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hw ⊢
  exact openingDifference_wins _ _ _ _ _ hw.1.1 (hw.1.2.trans hw.2.symm)

/-- Binding reduces to discrete logarithm with additive loss `1 / |F|`. -/
theorem bindingAdvantage_le_dlog [Fintype ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (g : G) (hg : Function.Bijective (· • g : F → G))
    (binder : BindingAdversary (Option ι → G) (ι → F) G F) :
    (scheme (uniformSetup (F := F) (ι := ι) g)).bindingAdvantage binder ≤
      Pr{let b ← (DiffieHellman.dlogExperiment g
        (plainReduction (bindingReduction binder)))}[b = true] + 1 / Fintype.card F :=
  (bindingAdvantage_le_relation g binder).trans
    (experiment_le plainImpl () g hg (plainAdversary (bindingReduction binder)))

/-- A generic binder returns a commitment handle and two vector openings. -/
abbrev GenericBinder (F ι : Type) :=
  OracleComp (GroupModel.genSpec F GroupModel.groupSig) (ℕ × (ι → F) × F × (ι → F) × F)

/-- Interpret a generic binder's commitment handle in its final group table. -/
@[expose] noncomputable def ofGeneric [Fintype ι] [Field F]
    [AddCommGroup G] [Module F G] [DecidableEq G] (A : GenericBinder F ι) :
    BindingAdversary (Option ι → G) (ι → F) G F := fun pp => do
  let (out, tbl) ← GroupModel.runGen (GroupModel.Model.group G) (fun _ => id) A
    (fun _ => List.ofFn (pp ∘ (Fintype.equivFin (Option ι)).symm))
  pure (GroupModel.lookup tbl () out.1, out.2)

/-- A generic relation finder subtracts the two scalar openings without any extra group query. -/
@[expose] def genericBindingReduction [Sub F] (A : GenericBinder F ι) :
    OracleComp (GroupModel.genSpec F GroupModel.groupSig) (Option ι → F) :=
  (fun out => openingDifference out.2.1 out.2.2.2.1 out.2.2.1 out.2.2.2.2) <$> A

/-- The generic coefficient reduction agrees with interpreting the binding reduction. -/
theorem bindingReduction_ofGeneric [Fintype ι] [Field F]
    [AddCommGroup G] [Module F G] [DecidableEq G] (A : GenericBinder F ι) :
    bindingReduction (ofGeneric (G := G) A) =
      GroupModel.DiscreteLogRelation.Adversary.ofGeneric (genericBindingReduction A) := by
  funext pp
  simp [bindingReduction, ofGeneric, GroupModel.DiscreteLogRelation.Adversary.ofGeneric,
    genericBindingReduction, GroupModel.runGen, GroupModel.run, StateT.run_map,
    Functor.map_map]

/-- A generic binder making at most `q` group operations has advantage at most
`((q + card ι + 2).choose 2 + 1) / |F|`; both the message and blinding bases count as inputs. -/
theorem bindingAdvantage_ofGeneric_le [Fintype ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (g : G) (hg : g ≠ 0) (A : GenericBinder F ι) (q : ℕ)
    (hq : IsQueryBoundP A (fun i => GroupModel.isGroupOp i = true) q) :
    (scheme (uniformSetup (F := F) (ι := ι) g)).bindingAdvantage (ofGeneric A) ≤
      (((q + Fintype.card ι + 2).choose 2 + 1 : ℕ) : ℝ≥0∞) / Fintype.card F := by
  refine (bindingAdvantage_le_relation g (ofGeneric A)).trans ?_
  rw [bindingReduction_ofGeneric]
  simpa [Fintype.card_option, Nat.add_assoc] using
    GroupModel.experiment_ofGeneric_le g hg (genericBindingReduction A) q
      ((isQueryBoundP_map_iff A _ q).mpr hq)

end VectorPedersen
