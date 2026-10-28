/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.SynchronizedPS.Functional
import all VCVio.Schemes.SynchronizedPS.Execution
import all VCVio.Schemes.SynchronizedPS.Reductions

/-! # Finite-table views of the synchronized PS reductions

Finite period tables occur only in proofs of the lazy programs. The common public transcript
retains the actual chronological coefficient positions of every received group input.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace SynchronizedPS.AGM

/-- The known scalar term after subtracting the certified co-signers' contribution. -/
@[expose] def knownTerm {F T : Type} [Field F]
    (coeff : List F) (tr : List (T ⊕ (T × F))) (tm : T × F)
    (others : List ((F × F) × F)) (ρ : T → F) : F :=
  (representation coeff tr ρ).1 - offset others * ρ tm.1

/-- The first-secret denominator on a scalar period table. -/
@[expose] def xDenominator {F T : Type} [Field F]
    (coeff : List F) (tr : List (T ⊕ (T × F))) (tm : T × F) (ρ : T → F) : F :=
  ρ tm.1 - (representation coeff tr ρ).2.1

/-- The second-secret denominator on a scalar period table. -/
@[expose] def yDenominator {F T : Type} [Field F]
    (coeff : List F) (tr : List (T ⊕ (T × F))) (tm : T × F) (ρ : T → F) : F :=
  ρ tm.1 * tm.2 - (representation coeff tr ρ).2.2

/-- On a finite public cover, the first-key reduction is the source extraction quotient
computed from the common scalar-table adversary view. -/
theorem xReduction_table {F T G₁ G₂ Gₜ : Type} [Field F] [SampleableType F] [DecidableEq T]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂) (x : F) (S : Finset T)
    (hS : ∀ y, WeightedInterfaceCovered S terms (fun out => out.value.data.1)
      (rawMain A (publicKeyOf g₂ (x, y)))) :
    xReduction A g₁ (x • g₁) g₂ (x • g₂) =ᵈ (do
      let y ← $ᵗ F
      let ρ ← $ᵗ (S → F)
      let H := extendTable S 0 ρ
      let z ← fixedView A H x y
      let c := (z.1.coefficients false).headD []
      return (knownTerm c z.2 z.1.value.data.1 z.1.value.data.2 H -
        y * yDenominator c z.2 z.1.value.data.1 H) /
          xDenominator c z.2 z.1.value.data.1 H) := by
  unfold xReduction
  apply _root_.EvalDistEq.bind_right
  intro y
  have h := (reductionRun_eq_table A (publicKeyOf g₂ (x, y))
    (fun r : F => r • g₁) (fun tm r => r • (x • g₁) + (r * (y * tm.2)) • g₁)
    (fun r => (r, (0 : F), (0 : F))) (fun tm r => (0, r, r * tm.2)) [(1, 0, 0)]
    S (hS y) 0).map (fun z =>
      let repr := evaluate (coefficients z.1) z.2.1
      (repr.1 - offset z.1.value.data.2 * z.2.2 -
        y * (z.2.2 * z.1.value.data.1.2 - repr.2.2)) / (z.2.2 - repr.2.1))
  have hsign (tm : T × F) (r : F) :
      r • (x • g₁) + (r * (y * tm.2)) • g₁ = (x + y * tm.2) • (r • g₁) := by
    rw [smul_smul, smul_smul, ← add_smul]
    congr 1
    ring
  simpa only [bind_pure_comp, map_bind, map_pure, Functor.map_map, coefficients, publicKeyOf,
    Function.comp_def, hsign, fixedView, representation, knownTerm, xDenominator,
    yDenominator, List.singleton_append] using h

/-- On a finite public cover, the second-key reduction is the source extraction quotient
computed from the common scalar-table adversary view. -/
theorem yReduction_table {F T G₁ G₂ Gₜ : Type} [Field F] [SampleableType F] [DecidableEq T]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂) (y : F) (S : Finset T)
    (hS : ∀ x, WeightedInterfaceCovered S terms (fun out => out.value.data.1)
      (rawMain A (publicKeyOf g₂ (x, y)))) :
    yReduction A g₁ (y • g₁) g₂ (y • g₂) =ᵈ (do
      let x ← $ᵗ F
      let ρ ← $ᵗ (S → F)
      let H := extendTable S 0 ρ
      let z ← fixedView A H x y
      let c := (z.1.coefficients false).headD []
      return (knownTerm c z.2 z.1.value.data.1 z.1.value.data.2 H -
        x * xDenominator c z.2 z.1.value.data.1 H) /
          yDenominator c z.2 z.1.value.data.1 H) := by
  unfold yReduction
  apply _root_.EvalDistEq.bind_right
  intro x
  have h := (reductionRun_eq_table A (publicKeyOf g₂ (x, y))
    (fun r : F => r • g₁) (fun tm r => (r * x) • g₁ + (r * tm.2) • (y • g₁))
    (fun r => (r, (0 : F), (0 : F))) (fun tm r => (0, r, r * tm.2)) [(1, 0, 0)]
    S (hS x) 0).map (fun z =>
      let repr := evaluate (coefficients z.1) z.2.1
      (repr.1 - offset z.1.value.data.2 * z.2.2 - x * (z.2.2 - repr.2.1)) /
        (z.2.2 * z.1.value.data.1.2 - repr.2.2))
  have hsign (tm : T × F) (r : F) :
      (r * x) • g₁ + (r * tm.2) • (y • g₁) = (x + y * tm.2) • (r • g₁) := by
    rw [smul_smul, smul_smul, ← add_smul]
    congr 1
    ring
  simpa only [bind_pure_comp, map_bind, map_pure, Functor.map_map, coefficients, publicKeyOf,
    Function.comp_def, hsign, fixedView, representation, knownTerm, xDenominator,
    yDenominator, List.singleton_append] using h

/-- Each key denominator is the matching finite-table verification-gap evaluation. -/
theorem denominator_eq_sum {F T : Type} [Field F] [DecidableEq T]
    (weighted : Bool) (S : Finset T) (ρ : S → F) (coeff : List F)
    (tr : List (T ⊕ (T × F))) (tm : T × F) :
    (if weighted then yDenominator coeff tr tm (extendTable S 0 ρ)
      else xDenominator coeff tr tm (extendTable S 0 ρ)) =
        ∑ i : S, verificationGap weighted coeff tr tm i.val * ρ i := by
  have hs := representation_secret weighted coeff tr (extendTable S 0 ρ)
  have h := verificationGap_table weighted S ρ coeff tr tm
  cases weighted <;>
    simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at hs h ⊢
  · simpa only [xDenominator, hs] using h
  · simpa only [yDenominator, hs] using h

/-- The masked signing contribution as a pair of chronological scalar evaluations. -/
@[expose] def maskSigning {F T : Type} [Field F] (weighted : Bool)
    (coeff : List F) (tr : List (T ⊕ (T × F))) (H : T → F × F) : F × F :=
  evaluate coeff.tail (tr.map (Sum.elim (fun _ => 0)
    (fun tm => (if weighted then tm.2 else 1) • H tm.1)))

/-- Pairing the two private tables pairs their signing-functional evaluations. -/
theorem maskSigning_eq {F T : Type} [Field F] (weighted : Bool)
    (coeff : List F) (tr : List (T ⊕ (T × F))) (a b : T → F) :
    maskSigning weighted coeff tr (fun t => (a t, b t)) =
      (signingScalar weighted coeff tr a, signingScalar weighted coeff tr b) := by
  apply Prod.ext
  · have h := evaluate_map (LinearMap.fst F F F) coeff.tail
      (tr.map (Sum.elim (fun _ => (0 : F × F))
        (fun tm => (if weighted then tm.2 else 1) • (a tm.1, b tm.1))))
    simp only [LinearMap.fst_apply] at h
    unfold maskSigning
    rw [← h]
    unfold signingScalar
    congr 1
    simp only [List.map_map]
    apply List.map_congr_left
    intro q _
    cases q <;> cases weighted <;> simp [mul_comm]
  · have h := evaluate_map (LinearMap.snd F F F) coeff.tail
      (tr.map (Sum.elim (fun _ => (0 : F × F))
        (fun tm => (if weighted then tm.2 else 1) • (a tm.1, b tm.1))))
    simp only [LinearMap.snd_apply] at h
    unfold maskSigning
    rw [← h]
    unfold signingScalar
    congr 1
    simp only [List.map_map]
    apply List.map_congr_left
    intro q _
    cases q <;> cases weighted <;> simp [mul_comm]

/-- The hash extractor's quotient from a paired private table and its public transcript. -/
@[expose] def maskGuess {F T : Type} [Field F] [DecidableEq F] [DecidableEq T]
    (coeff : List F) (tr : List (T ⊕ (T × F))) (tm : T × F) (H : T → F × F) : F :=
  let w := selectedWeight coeff tr tm
  let d := (if w then tm.2 else 1) • H tm.1 - maskSigning w coeff tr H
  (-d.2 / d.1)

/-- On a paired finite table, the masked quotient evaluates the selected gap on the two
independent tables. -/
theorem maskGuess_eq {F T : Type} [Field F] [DecidableEq F] [DecidableEq T]
    (S : Finset T) (a b : S → F) (coeff : List F) (tr : List (T ⊕ (T × F))) (tm : T × F) :
    maskGuess coeff tr tm (fun t => (extendTable S 0 a t, extendTable S 0 b t)) =
      (-∑ i : S, verificationGap (selectedWeight coeff tr tm) coeff tr tm i.val * b i) /
        (∑ i : S, verificationGap (selectedWeight coeff tr tm) coeff tr tm i.val * a i) := by
  dsimp only [maskGuess]
  rw [maskSigning_eq]
  simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  rw [mul_comm (if selectedWeight coeff tr tm then tm.2 else 1),
    verificationGap_table, mul_comm (if selectedWeight coeff tr tm then tm.2 else 1),
    verificationGap_table]

private theorem hashQuotient_trace {F T : Type} [Field F] [DecidableEq F] [DecidableEq T]
    (coeff : List F) (tr : List (T ⊕ (T × F))) (tm : T × F) (H : T → F × F) :
    hashQuotient coeff tm
      (none :: tr.map (Sum.elim (fun _ => none) (fun m => some (m, H m.1)))) (H tm.1) =
      maskGuess coeff tr tm H := by
  have heval {V : Type} [AddCommMonoid V] [Module F V] (v : (T × F) → F × F → V) :
      evaluate coeff
        ((none :: tr.map (Sum.elim (fun _ => none) (fun m => some (m, H m.1)))).map
          (fun p => p.elim 0 (fun mr => v mr.1 mr.2))) =
        evaluate coeff.tail (tr.map (Sum.elim (fun _ => 0) (fun m => v m (H m.1)))) := by
    simp only [List.map_cons, Option.elim_none, evaluate_cons, smul_zero, zero_add, List.map_map]
    congr 1
    apply List.map_congr_left
    intro q _
    cases q <;> rfl
  have hre : (1 : F) - evaluate coeff.tail
      (tr.map (Sum.elim (fun _ => 0) (fun m => if m.1 = tm.1 then 1 else 0))) =
      verificationGap false coeff tr tm tm.1 := by
    simp [verificationGap, signingFunctional, periodWeight]
  dsimp only [hashQuotient]
  simp only [heval (fun m _ => if m.1 = tm.1 then (1 : F) else 0),
    heval (fun _ r => r), heval (fun m r => m.2 • r), hre]
  dsimp only [maskGuess, selectedWeight, maskSigning]
  by_cases hz : verificationGap false coeff tr tm tm.1 = 0
  · simp only [hz, ne_eq, not_true_eq_false, ↓reduceIte, decide_true]
  · simp only [hz, ne_eq, not_false_eq_true, ↓reduceIte, decide_false, Bool.false_eq_true, one_smul]

/-- The hash reduction's paired finite table has the same distribution as its lazy cache,
with the source's target-period selection between the two gap functionals. -/
theorem hashReduction_pair_table {F T G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [DecidableEq F] [DecidableEq T]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂) (α : F) (S : Finset T)
    (hS : ∀ x y : F, WeightedInterfaceCovered S terms (fun out => out.value.data.1)
      (rawMain A (publicKeyOf g₂ (x, y)))) :
    hashReduction A g₁ (α • g₁) g₂ (α • g₂) =ᵈ (do
      let x ← $ᵗ F
      let y ← $ᵗ F
      let table ← $ᵗ (S → F × F)
      let H := extendTable S (0, 0) table
      let z ← fixedView A (fun t => (H t).1 * α + (H t).2) x y
      return maskGuess ((z.1.coefficients false).headD []) z.2 z.1.value.data.1 H) := by
  unfold hashReduction
  apply _root_.EvalDistEq.bind_right
  intro x
  apply _root_.EvalDistEq.bind_right
  intro y
  have h := (reductionRun_eq_table A (publicKeyOf g₂ (x, y))
    (fun r : F × F => r.1 • (α • g₁) + r.2 • g₁)
    (fun tm r => (x + y * tm.2) • (r.1 • (α • g₁) + r.2 • g₁))
    (fun _ => none) (fun tm r => some (tm, r)) [none] S (hS x y) (0, 0)).map
      (fun z => hashQuotient (coefficients z.1) z.1.value.data.1 z.2.1 z.2.2)
  simpa only [bind_pure_comp, map_bind, map_pure, Functor.map_map, coefficients,
    publicKeyOf, Function.comp_def, List.singleton_append, hashQuotient_trace,
    fixedView, add_smul, mul_smul] using h

/-- The lazy hash reduction evaluates the selected gap on independent slope and offset
tables, while the adversary sees only their affine combination. -/
theorem hashReduction_table {F T G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [DecidableEq F] [DecidableEq T]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F T G₁ G₂ e g₁ g₂) (α : F) (S : Finset T)
    (hS : ∀ x y : F, WeightedInterfaceCovered S terms (fun out => out.value.data.1)
      (rawMain A (publicKeyOf g₂ (x, y)))) :
    hashReduction A g₁ (α • g₁) g₂ (α • g₂) =ᵈ (do
      let x ← $ᵗ F
      let y ← $ᵗ F
      let a ← $ᵗ (S → F)
      let b ← $ᵗ (S → F)
      let z ← fixedView A (extendTable S 0 (fun i => a i * α + b i)) x y
      let c := (z.1.coefficients false).headD []
      let tm := z.1.value.data.1
      let w := selectedWeight c z.2 tm
      return (-∑ i : S, verificationGap w c z.2 tm i.val * b i) /
        (∑ i : S, verificationGap w c z.2 tm i.val * a i)) := by
  refine (hashReduction_pair_table A α S hS).trans ?_
  apply _root_.EvalDistEq.bind_right
  intro x
  apply _root_.EvalDistEq.bind_right
  intro y
  refine ((uniformSample_pair_tables (F := F) (I := S)).symm.bind_left _).trans ?_
  simp only [bind_assoc, pure_bind]
  apply _root_.EvalDistEq.bind_right
  intro a
  apply _root_.EvalDistEq.bind_right
  intro b
  have hp (t : T) : extendTable S (0, 0) (fun i => (a i, b i)) t =
      (extendTable S 0 a t, extendTable S 0 b t) := by
    apply Prod.ext
    · exact (extendTable_map S (0, 0) (fun i => (a i, b i)) Prod.fst t).symm
    · exact (extendTable_map S (0, 0) (fun i => (a i, b i)) Prod.snd t).symm
  have ha : (fun t => (extendTable S (0, 0) (fun i => (a i, b i)) t).1 * α +
      (extendTable S (0, 0) (fun i => (a i, b i)) t).2) =
      extendTable S 0 (fun i => a i * α + b i) := by
    funext t
    simpa only [zero_mul, zero_add] using
      (extendTable_map S (0, 0) (fun i => (a i, b i)) (fun r => r.1 * α + r.2) t).symm
  rw [ha]
  apply _root_.EvalDistEq.bind_right
  intro z
  simp only [show extendTable S (0, 0) (fun i => (a i, b i)) =
    (fun t => (extendTable S 0 a t, extendTable S 0 b t)) from funext hp, maskGuess_eq]
  exact _root_.EvalDistEq.refl _

end SynchronizedPS.AGM
