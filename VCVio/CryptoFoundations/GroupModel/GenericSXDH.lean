/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.GenericXDH
public import VCVio.CryptoFoundations.HardnessAssumptions.SXDH
import all VCVio.CryptoFoundations.GroupModel.Instances

/-! # Generic hardness of symmetric external Diffie–Hellman

At the Type 3 pairing signature, DDH in the second source group remains generically
hard when the first generator and the pairing are public. The real and random accessible
spans have equal relation kernels, with degree bounds `(0, 2, 2)` and `(0, 1, 1)`.

SXDH is the conjunction of XDH in the two source groups: for generic adversaries,
`XDH.advantage_ofGeneric_le` bounds the first-source advantage by
`3 * ((n₁ + 5).choose 2 + (nₜ + 1).choose 2) / |F|`, and
`XDH₂.advantage_ofGeneric_le` bounds the second-source advantage by
`3 * ((n₂ + 5).choose 2 + (nₜ + 1).choose 2) / |F|`.
Both statements assume nonzero source generators and their nonzero pairing.
-/

public section

open OracleComp OracleSpec MeasureTheory MvPolynomial GroupModel
open scoped ENNReal

namespace GroupModel

variable {F : Type}

/-- The symbolic XDH₂ table with fourth second-source entry `p`, first generator `1`,
and no initially supplied target elements. -/
@[expose] noncomputable def xdh₂Table [Field F] (p : MvPolynomial (Fin 3) F) :
    Tbl (fun _ : PSort => MvPolynomial (Fin 3) F)
  | .g₂ => [1, X 0, X 1, p]
  | .g₁ => [1]
  | .gₜ => []

private theorem evReprT_xdh₂Table [Field F] (p : MvPolynomial (Fin 3) F) (r : ReprT F) :
    evReprT (LinearMap.mul F _) (xdh₂Table p .g₁) (xdh₂Table p .g₂)
      (xdh₂Table p .gₜ) r = evRepr (xdh₂Table p .g₂) (fun i => r.2 0 i) := by
  simp [evReprT_apply, evRepr_apply, xdh₂Table]

/-- The real and random XDH₂ tables have the same accessible relation kernel.
Pairing with the sole first-source entry `1` preserves the second-source independent span. -/
theorem xdh₂Tables_sameKernel [Field F] :
    SameKernel.pairing (xdh₂Table (X 0 * X 1 : MvPolynomial (Fin 3) F)) (xdh₂Table (X 2)) := by
  refine ⟨fun s => by cases s <;> rfl, ?_⟩
  intro s r
  cases s with
  | g₂ => exact (ddhTables_sameKernel (F := F) ()).2 r
  | g₁ => rfl
  | gₜ =>
    change ReprT F at r
    change evReprT _ _ _ _ r = 0 ↔ evReprT _ _ _ _ r = 0
    rw [evReprT_xdh₂Table, evReprT_xdh₂Table]
    exact (ddhTables_sameKernel (F := F) ()).2 (fun i => r.2 0 i)

/-- The real XDH₂ table has per-sort degrees `(0, 2, 2)` and the random table
has per-sort degrees `(0, 1, 1)`. Both profiles are closed under the public pairing. -/
theorem xdh₂Tables_degreeLE [Field F] :
    DegreeLE (fun | .g₁ => 0 | .g₂ => 2 | .gₜ => 2)
      (xdh₂Table (X 0 * X 1 : MvPolynomial (Fin 3) F)) ∧
    DegreeLE (fun | .g₁ => 0 | .g₂ => 1 | .gₜ => 1) (xdh₂Table (F := F) (X 2)) := by
  constructor
  · intro s p hp
    cases s with
    | g₂ => exact (ddhTables_degreeLE (F := F)).1 () p hp
    | g₁ =>
      have hp : p = 1 := by simpa [xdh₂Table] using hp
      simp [hp]
    | gₜ => simp [xdh₂Table] at hp
  · intro s p hp
    cases s with
    | g₂ => exact (ddhTables_degreeLE (F := F)).2 () p hp
    | g₁ =>
      have hp : p = 1 := by simpa [xdh₂Table] using hp
      simp [hp]
    | gₜ => simp [xdh₂Table] at hp

end GroupModel

namespace XDH₂

variable {F G₁ G₂ Gₜ : Type}

/-- Run a generic Boolean adversary on the four second-source XDH₂ elements and the
first-source generator, with the supplied public pairing and an empty target table. -/
@[expose] def Adversary.ofGeneric [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (A : OracleComp (genSpec F pairingSig) Bool) :
    Adversary F G₁ G₂ :=
  fun g₂ X Y T g₁ => Prod.fst <$> runGen (pairingReal e) (fun _ => id) A
    (fun | .g₂ => [g₂, X, Y, T] | .g₁ => [g₁] | .gₜ => [])

private theorem runGen_xdh₂ [Field F] [DecidableEq F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0) (x : Fin 3 → F)
    (A : OracleComp (genSpec F pairingSig) Bool) (p : MvPolynomial (Fin 3) F) :
    Adversary.ofGeneric e A g₂ (x 0 • g₂) (x 1 • g₂) (MvPolynomial.eval x p • g₂) g₁ =
      Prod.fst <$> runGen (symbolic F pairingSig (Fin 3))
        (fun _ p => MvPolynomial.eval x p) A (xdh₂Table p) := by
  have ht : mapTbl (fun s => (evalHom.pairing e g₁ g₂ x).toFun s) (xdh₂Table p) =
      (fun | .g₂ => [g₂, x 0 • g₂, x 1 • g₂, MvPolynomial.eval x p • g₂]
           | .g₁ => [g₁] | .gₜ => []) := by
    funext s
    cases s <;> simp [mapTbl, xdh₂Table, evalAt_apply]
  unfold Adversary.ofGeneric
  rw [← ht, runGen_pairing_mapTbl_evalHom e g₁ g₂ hg₁ hg₂ he x A]
  simp only [Functor.map_map, Prod.map, id_eq]

private theorem real_experiment_evalDistEq [Field F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0) (A : OracleComp (genSpec F pairingSig) Bool) :
    realExperiment g₂ g₁ (Adversary.ofGeneric e A) =ᵈ
      (do let x ← $ᵗ (Fin 3 → F)
          Prod.fst <$> runGen (symbolic F pairingSig (Fin 3))
            (fun _ p => MvPolynomial.eval x p) A (xdh₂Table (X 0 * X 1))) := by
  have hs := (XDH.uniformSample_fin_three (F := F)).bind_left (fun x =>
    Adversary.ofGeneric e A g₂ (x 0 • g₂) (x 1 • g₂) ((x 0 * x 1) • g₂) g₁)
  have hc := EvalDistEq.bind_right ($ᵗ F : ProbComp F) (fun a =>
    EvalDistEq.bind_right ($ᵗ F : ProbComp F) (fun b =>
      OracleComp.EvalDistEq.bind_const ($ᵗ F)
        (Adversary.ofGeneric e A g₂ (a • g₂) (b • g₂) ((a * b) • g₂) g₁)))
  have heq := hc.symm.trans (by
    simpa only [bind_assoc, pure_bind, Matrix.cons_val_zero, Matrix.cons_val_one] using hs)
  apply EvalDistEq.of_forall_prEvent_eq
  intro p
  simpa [realExperiment, ← runGen_xdh₂ e g₁ g₂ hg₁ hg₂ he, prEvent_norm] using
    heq.prEvent_eq p

private theorem random_experiment_evalDistEq [Field F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0) (A : OracleComp (genSpec F pairingSig) Bool) :
    randomExperiment g₂ g₁ (Adversary.ofGeneric e A) =ᵈ
      (do let x ← $ᵗ (Fin 3 → F)
          Prod.fst <$> runGen (symbolic F pairingSig (Fin 3))
            (fun _ p => MvPolynomial.eval x p) A (xdh₂Table (X 2))) := by
  have hs := (XDH.uniformSample_fin_three (F := F)).bind_left (fun x =>
    Adversary.ofGeneric e A g₂ (x 0 • g₂) (x 1 • g₂) (x 2 • g₂) g₁)
  apply EvalDistEq.of_forall_prEvent_eq
  intro p
  simpa [randomExperiment, ← runGen_xdh₂ e g₁ g₂ hg₁ hg₂ he, prEvent_norm] using
    hs.prEvent_eq p

/-- In a Type 3 pairing group, a generic XDH₂ adversary with per-sort append budgets
`n₁, n₂, nₜ` has advantage at most
`3 * ((n₂ + 5).choose 2 + (nₜ + 1).choose 2) / |F|`.
The first-source degree is zero, so its budget contributes no collision term.
Equality queries are free. Nonzero generators suffice; they need not span the carriers. -/
theorem advantage_ofGeneric_le [Field F] [Fintype F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0)
    (A : OracleComp (genSpec F pairingSig) Bool) (n₁ n₂ nₜ : ℕ)
    (hn₁ : IsQueryBoundP A (appendsTo .g₁) n₁)
    (hn₂ : IsQueryBoundP A (appendsTo .g₂) n₂)
    (hnₜ : IsQueryBoundP A (appendsTo .gₜ) nₜ) :
    advantage g₂ g₁ (Adversary.ofGeneric e A) ≤
      (3 * ((n₂ + 5).choose 2 + (nₜ + 1).choose 2) : ℕ) / (Fintype.card F : ℝ≥0∞) := by
  classical
  let : Fintype PSort := ⟨{.g₂, .g₁, .gₜ}, by intro s; cases s <;> simp⟩
  let : MeasurableSpace ((Fin 3 → F) × Bool) := ⊤
  let D₀ : PSort → ℕ := fun | .g₁ => 0 | .g₂ => 2 | .gₜ => 2
  let D₁ : PSort → ℕ := fun | .g₁ => 0 | .g₂ => 1 | .gₜ => 1
  let n : PSort → ℕ := fun | .g₂ => n₂ | .g₁ => n₁ | .gₜ => nₜ
  have hD₀ : pairingSig.DegreeClosed D₀ := by
    convert degreeClosed_pairingSig 0 2 2 using 1
    funext s
    cases s <;> rfl
  have hD₁ : pairingSig.DegreeClosed D₁ := by
    convert degreeClosed_pairingSig 0 1 1 using 1
    funext s
    cases s <;> rfl
  have hn : ∀ s, IsQueryBoundP A (appendsTo s) (n s) := by
    intro s
    cases s
    · exact hn₁
    · exact hn₂
    · exact hnₜ
  let left : ProbComp ((Fin 3 → F) × Bool) := do
    let x ← $ᵗ (Fin 3 → F)
    let z ← runGen (symbolic F pairingSig (Fin 3))
      (fun _ p => MvPolynomial.eval x p) A (xdh₂Table (X 0 * X 1))
    pure (x, z.1)
  let right : ProbComp ((Fin 3 → F) × Bool) := do
    let x ← $ᵗ (Fin 3 → F)
    let z ← runGen (symbolic F pairingSig (Fin 3))
      (fun _ p => MvPolynomial.eval x p) A (xdh₂Table (X 2))
    pure (x, z.1)
  have hl : realExperiment g₂ g₁ (Adversary.ofGeneric e A) =ᵈ Prod.snd <$> left := by
    simpa only [left, map_bind, map_pure, bind_pure_comp, Functor.map_map, Function.comp_def] using
      real_experiment_evalDistEq e g₁ g₂ hg₁ hg₂ he A
  have hr : randomExperiment g₂ g₁ (Adversary.ofGeneric e A) =ᵈ Prod.snd <$> right := by
    simpa only [right, map_bind, map_pure, bind_pure_comp, Functor.map_map, Function.comp_def] using
      random_experiment_evalDistEq e g₁ g₂ hg₁ hg₂ he A
  rw [advantage, hl.evalDist_eq, hr.evalDist_eq]
  have hb := measureETVDist_runGen_pairing_sameKernel_uniform_le hD₀ hD₁ A hn
    (xdh₂Table (X 0 * X 1)) (xdh₂Table (X 2))
    xdh₂Tables_degreeLE.1 xdh₂Tables_degreeLE.2 xdh₂Tables_sameKernel
  calc
    _ ≤ measureETVDist (Prod.snd <$> left) (Prod.snd <$> right) :=
      measure_absDiff_apply_le_measureETVDist _ _ (MeasurableSet.singleton true)
    _ ≤ measureETVDist left right := measureETVDist_map_le _ _ _ Measurable.of_discrete
    _ ≤ ∑ s, (((xdh₂Table (X 0 * X 1 : MvPolynomial (Fin 3) F) s).length + n s + 1).choose 2 :
        ℝ≥0∞) * ((D₀ s : ℝ≥0∞) / Fintype.card F + (D₁ s : ℝ≥0∞) / Fintype.card F) := hb
    _ = _ := by
      change (∑ s ∈ ({.g₂, .g₁, .gₜ} : Finset PSort),
        (((xdh₂Table (X 0 * X 1 : MvPolynomial (Fin 3) F) s).length + n s + 1).choose 2 :
          ℝ≥0∞) * ((D₀ s : ℝ≥0∞) / Fintype.card F + (D₁ s : ℝ≥0∞) / Fintype.card F)) = _
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
      simp only [xdh₂Table, n, D₀, D₁, List.length_cons, List.length_nil, zero_add,
        Nat.cast_zero]
      simp only [Nat.add_comm 4 n₂, Nat.add_assoc, Nat.reduceAdd,
        Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, div_eq_mul_inv]
      ring

/-- A total group-operation budget bounds each append budget, giving the XDH₂ bound
`3 * ((q + 5).choose 2 + (q + 1).choose 2) / |F|`. Equality queries are free. -/
theorem advantage_ofGeneric_le_of_total [Field F] [Fintype F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0)
    (A : OracleComp (genSpec F pairingSig) Bool) (q : ℕ)
    (hq : IsQueryBoundP A (fun i => isGroupOp i = true) q) :
    advantage g₂ g₁ (Adversary.ofGeneric e A) ≤
      (3 * ((q + 5).choose 2 + (q + 1).choose 2) : ℕ) / (Fintype.card F : ℝ≥0∞) :=
  advantage_ofGeneric_le e g₁ g₂ hg₁ hg₂ he A q q q
    (hq.appendsTo .g₁) (hq.appendsTo .g₂) (hq.appendsTo .gₜ)

end XDH₂
