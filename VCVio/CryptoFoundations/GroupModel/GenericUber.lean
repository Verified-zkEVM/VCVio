/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.AccessibleSpan
public import VCVio.CryptoFoundations.GroupModel.GenericPairing
public import VCVio.CryptoFoundations.HardnessAssumptions.Uber
import all VCVio.CryptoFoundations.GroupModel.Instances

/-! # Generic computational uber bounds

A target outside the initial accessible span cannot equal any symbolic output polynomial.
T8 bounds recovery by the sorted collision sum and one additional root bound, at every
signature with closed degree bounds. The Type 3 instance transports this result to the
computational uber experiment of Boneh, Boyen and Goh (2005) and Boyen (2008).
-/

public section

open OracleComp OracleSpec MeasureTheory MvPolynomial
open scoped ENNReal


namespace GroupModel

variable {F S ι : Type}

/-- Computational uber hardness at any signature with closed degree bounds: a target
outside the accessible span contributes a nonzero difference polynomial of degree at most `k`. -/
theorem prEvent_runGen_symbolic_uber_le [Field F] [DecidableEq F]
    [Fintype S] [DecidableEq S] {σ : Sig S}
    (xs : ProbComp (ι → F)) {D : S → ℕ} {ε : S → ℝ≥0∞} {ε' : ℝ≥0∞} {n : S → ℕ}
    (hD : σ.DegreeClosed D)
    (hε : ∀ s (p : MvPolynomial ι F), p ≠ 0 → p.totalDegree ≤ D s →
      Pr{let x ← xs}[MvPolynomial.eval x p = 0] ≤ ε s)
    (oa : OracleComp (genSpec F σ) Handle)
    (hn : ∀ s, IsQueryBoundP oa (appendsTo s) (n s))
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (hd : DegreeLE D tbl)
    (s : S) (f : MvPolynomial ι F) (hf : f ∉ accessibleSpan σ tbl s)
    (k : ℕ) (hk : max f.totalDegree (D s) ≤ k)
    (hroot : ∀ p : MvPolynomial ι F, p ≠ 0 → p.totalDegree ≤ k →
      Pr{let x ← xs}[MvPolynomial.eval x p = 0] ≤ ε') :
    Pr{let x ← xs; let z ← (runGen (symbolic F σ ι)
      (fun _ p => MvPolynomial.eval x p) oa tbl)}[
        MvPolynomial.eval x (lookup z.2 s z.1) = MvPolynomial.eval x f] ≤
      (∑ t, (((tbl t).length + n t + 1).choose 2 : ℝ≥0∞) * ε t) + ε' := by
  classical
  apply prEvent_runGen_symbolic_le_add_of_polynomial xs hD hε oa hn tbl hd
    (fun z => f - lookup z.2 s z.1) k
  · intro z hz
    exact (MvPolynomial.totalDegree_sub _ _).trans
      ((max_le_max le_rfl
        (runGen_degreeLE hD (fun _ => id) oa tbl hd z hz |>.lookup s z.1)).trans hk)
  · intro x z hz heq
    constructor
    · intro hzero
      apply hf
      rw [sub_eq_zero.mp hzero]
      exact lookup_mem_submodule (runGen_mem_accessibleSpan (fun _ => id) oa tbl z hz) s z.1
    · simp only [map_sub, heq, sub_self]
  · exact hroot

/-- Uniform scalar sampling specializes the computational uber bound to Schwartz–Zippel
terms `D s / |F|` and `k / |F|`. -/
theorem prEvent_runGen_symbolic_uber_uniform_le [Field F] [DecidableEq F]
    [Fintype F] [Finite ι] [SampleableType (ι → F)]
    [Fintype S] [DecidableEq S] {σ : Sig S} {D n : S → ℕ}
    (hD : σ.DegreeClosed D) (oa : OracleComp (genSpec F σ) Handle)
    (hn : ∀ s, IsQueryBoundP oa (appendsTo s) (n s))
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (hd : DegreeLE D tbl)
    (s : S) (f : MvPolynomial ι F) (hf : f ∉ accessibleSpan σ tbl s)
    (k : ℕ) (hk : max f.totalDegree (D s) ≤ k) :
    Pr{let x ← $ᵗ (ι → F); let z ← (runGen (symbolic F σ ι)
      (fun _ p => MvPolynomial.eval x p) oa tbl)}[
        MvPolynomial.eval x (lookup z.2 s z.1) = MvPolynomial.eval x f] ≤
      (∑ t, (((tbl t).length + n t + 1).choose 2 : ℝ≥0∞) *
        ((D t : ℝ≥0∞) / Fintype.card F)) + (k : ℝ≥0∞) / Fintype.card F := by
  classical
  exact prEvent_runGen_symbolic_uber_le _ hD
    (fun _ p hp hdeg => prob_eval_zero_univ_le_div p hp hdeg) oa hn tbl hd s f hf k hk
    (fun p hp hdeg => prob_eval_zero_univ_le_div p hp hdeg)

/-- The Type 3 initial polynomial table, in the supplied list order. -/
@[expose] def uberTable [CommSemiring F]
    (P R Q : List (MvPolynomial ι F)) : Tbl (fun _ : PSort => MvPolynomial ι F)
  | .g₁ => P
  | .g₂ => R
  | .gₜ => Q

/-- Evaluation of the Type 3 polynomial table gives the three ordered lists of group elements. -/
theorem mapTbl_uberTable_evalHom {G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂) (x : ι → F)
    (P R Q : List (MvPolynomial ι F)) :
    mapTbl (fun s => (evalHom.pairing e g₁ g₂ x).toFun s) (uberTable P R Q) =
      (fun | .g₁ => P.map (fun p => MvPolynomial.eval x p • g₁)
           | .g₂ => R.map (fun p => MvPolynomial.eval x p • g₂)
           | .gₜ => Q.map (fun p => MvPolynomial.eval x p • e g₁ g₂)) := by
  funext s
  cases s <;> apply List.map_congr_left <;> intro p _ <;>
    simp only [evalHom.pairing_apply_g₁, evalHom.pairing_apply_g₂,
      evalHom.pairing_apply_gₜ, evalAt_apply] <;> rfl

end GroupModel

namespace Uber

open GroupModel

variable {F G₁ G₂ Gₜ : Type}

/-- Interpret a generic output handle as an element of the final target table. -/
@[expose] def ComputationalAdversary.ofGeneric [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (A : OracleComp (genSpec F pairingSig) Handle) :
    ComputationalAdversary G₁ G₂ Gₜ := fun xs ys zs =>
  (fun z => lookup z.2 .gₜ z.1) <$> runGen (pairingReal e) (fun _ => id) A
    (fun | .g₁ => xs | .g₂ => ys | .gₜ => zs)

/-- Interpret a generic Boolean adversary with the challenge appended to the target table. -/
@[expose] def DecisionalAdversary.ofGeneric [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (A : OracleComp (genSpec F pairingSig) Bool) :
    DecisionalAdversary G₁ G₂ Gₜ := fun xs ys zs t =>
  Prod.fst <$> runGen (pairingReal e) (fun _ => id) A
    (fun | .g₁ => xs | .g₂ => ys | .gₜ => zs ++ [t])

/-- At Type 3, computational uber success is bounded by the sorted collision terms and
`k / |F|`, where `k` bounds both the target degree and the reachable target-sort degree. -/
theorem experiment_ofGeneric_le [DecidableEq Gₜ] [Field F] [Fintype F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    {v : ℕ} (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0)
    (P R Q : List (MvPolynomial (Fin v) F)) (f : MvPolynomial (Fin v) F)
    (hf : f ∉ accessibleSpan pairingSig (uberTable P R Q) .gₜ)
    {D n : PSort → ℕ} (hD : pairingSig.DegreeClosed D)
    (hd : DegreeLE D (uberTable P R Q))
    (A : OracleComp (genSpec F pairingSig) Handle)
    (hn : ∀ s, IsQueryBoundP A (appendsTo s) (n s))
    (k : ℕ) (hk : max f.totalDegree (D .gₜ) ≤ k) :
    Pr{let b ← (computationalExperiment e g₁ g₂ P R Q f
      (ComputationalAdversary.ofGeneric e A))}[b = true] ≤
      ((((P.length + n .g₁ + 1).choose 2 * D .g₁ +
        (R.length + n .g₂ + 1).choose 2 * D .g₂ +
        (Q.length + n .gₜ + 1).choose 2 * D .gₜ + k : ℕ) : ℝ≥0∞) / Fintype.card F) := by
  classical
  let : Fintype PSort := ⟨{.g₁, .g₂, .gₜ}, by intro s; cases s <;> simp⟩
  have hr (x : Fin v → F) :
      runGen (pairingReal e) (fun _ => id) A (fun
        | .g₁ => P.map (fun p => MvPolynomial.eval x p • g₁)
        | .g₂ => R.map (fun p => MvPolynomial.eval x p • g₂)
        | .gₜ => Q.map (fun p => MvPolynomial.eval x p • e g₁ g₂)) =
      Prod.map id (mapTbl (fun s => (evalHom.pairing e g₁ g₂ x).toFun s)) <$>
        runGen (symbolic F pairingSig (Fin v)) (fun _ p => MvPolynomial.eval x p) A
          (uberTable P R Q) := by
    rw [← mapTbl_uberTable_evalHom e g₁ g₂ x P R Q]
    exact runGen_pairing_mapTbl_evalHom e g₁ g₂ hg₁ hg₂ he x A (uberTable P R Q)
  have had (x : Fin v → F) : ComputationalAdversary.ofGeneric e A
      (P.map (fun p => MvPolynomial.eval x p • g₁))
      (R.map (fun p => MvPolynomial.eval x p • g₂))
      (Q.map (fun p => MvPolynomial.eval x p • e g₁ g₂)) =
      (fun z => MvPolynomial.eval x (lookup z.2 .gₜ z.1) • e g₁ g₂) <$>
        runGen (symbolic F pairingSig (Fin v)) (fun _ p => MvPolynomial.eval x p) A
          (uberTable P R Q) := by
    have hh := congrArg (fun c => (fun z => lookup z.2 .gₜ z.1) <$> c) (hr x)
    rw [Functor.map_map] at hh
    have hm : (fun z : Handle × Tbl (fun _ : PSort => MvPolynomial (Fin v) F) =>
        lookup (mapTbl (fun s => (evalHom.pairing e g₁ g₂ x).toFun s) z.2) .gₜ z.1) =
        (fun z => MvPolynomial.eval x (lookup z.2 .gₜ z.1) • e g₁ g₂) := by
      funext z
      exact (lookup_mapTbl (fun s => (evalHom.pairing e g₁ g₂ x).toFun s) z.2 .gₜ z.1).trans
        ((evalHom.pairing_apply_gₜ e g₁ g₂ x _).trans (evalAt_apply (G := Gₜ) _ _ _))
    exact hh.trans (congrArg (fun g => g <$> runGen (symbolic F pairingSig (Fin v))
      (fun _ p => MvPolynomial.eval x p) A (uberTable P R Q)) hm)
  have hev : Pr{let b ← (computationalExperiment e g₁ g₂ P R Q f
      (ComputationalAdversary.ofGeneric e A))}[b = true] =
      Pr{let x ← $ᵗ (Fin v → F); let z ← (runGen (symbolic F pairingSig (Fin v))
        (fun _ p => MvPolynomial.eval x p) A (uberTable P R Q))}[
          MvPolynomial.eval x (lookup z.2 .gₜ z.1) = MvPolynomial.eval x f] := by
    simp only [computationalExperiment, had, prEvent_norm,
      (smul_left_injective F he).eq_iff, decide_eq_true_eq]
  rw [hev]
  have hb := prEvent_runGen_symbolic_uber_uniform_le hD A hn (uberTable P R Q) hd .gₜ f hf k hk
  refine hb.trans_eq ?_
  change (∑ s ∈ ({.g₁, .g₂, .gₜ} : Finset PSort),
    (((uberTable P R Q s).length + n s + 1).choose 2 : ℝ≥0∞) *
      ((D s : ℝ≥0∞) / Fintype.card F)) + (k : ℝ≥0∞) / Fintype.card F = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [uberTable, Nat.cast_add, Nat.cast_mul, ENNReal.add_div, mul_div_assoc]
  ac_rfl

/-- A total operation budget supplies each per-sort budget in the computational uber bound. -/
theorem experiment_ofGeneric_le_of_total [DecidableEq Gₜ] [Field F] [Fintype F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [∀ s, DecidableEq (PFam G₁ G₂ Gₜ s)]
    {v : ℕ} (e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ) (g₁ : G₁) (g₂ : G₂)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he : e g₁ g₂ ≠ 0)
    (P R Q : List (MvPolynomial (Fin v) F)) (f : MvPolynomial (Fin v) F)
    (hf : f ∉ accessibleSpan pairingSig (uberTable P R Q) .gₜ)
    {D : PSort → ℕ} (hD : pairingSig.DegreeClosed D) (hd : DegreeLE D (uberTable P R Q))
    (A : OracleComp (genSpec F pairingSig) Handle) (q : ℕ)
    (hq : IsQueryBoundP A (fun i => isGroupOp i = true) q)
    (k : ℕ) (hk : max f.totalDegree (D .gₜ) ≤ k) :
    Pr{let b ← (computationalExperiment e g₁ g₂ P R Q f
      (ComputationalAdversary.ofGeneric e A))}[b = true] ≤
      ((((P.length + q + 1).choose 2 * D .g₁ +
        (R.length + q + 1).choose 2 * D .g₂ +
        (Q.length + q + 1).choose 2 * D .gₜ + k : ℕ) : ℝ≥0∞) / Fintype.card F) :=
  experiment_ofGeneric_le e g₁ g₂ hg₁ hg₂ he P R Q f hf hD hd A
    (fun s => hq.appendsTo s) k hk

end Uber
