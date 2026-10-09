/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
public import VCVio.CryptoFoundations.SecExp
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.EvalDist.UniformCompatibility
public import VCVio.OracleComp.ProbComp
public import VCVio.EvalDist.Bool

/-!
# Discrete Logarithm Assumptions (DLog / CDH / DDH)

Standard hardness assumptions for cryptographic groups, formalized using Mathlib's
`Module F G` for scalar multiplication.

## Mathematical setup

We model a cyclic group as:
- `F` : the scalar field (exponents), e.g. `ZMod p` for a prime-order group
- `G` : the group of elements (e.g. elliptic curve points), with `[AddCommGroup G]`
- `Module F G` : scalar multiplication `a • g` (corresponds to `g^a` in multiplicative notation)
- `g : G` : a fixed generator (public system parameter)

## Notation correspondence

| Textbook (multiplicative) | This file (additive / EC-style) |
|---|---|
| `g^a`                     | `a • g`                         |
| `g^a · g^b = g^{a+b}`    | `a • g + b • g = (a + b) • g`  |
| `(g^a)^b = g^{ab}`       | `b • (a • g) = (b * a) • g`    |

## Assumptions

- **DLog**: given `(g, x • g)`, find `x`
- **CDH**: given `(g, a • g, b • g)`, find `(a * b) • g`
- **DDH**: distinguish `(g, a • g, b • g, (a * b) • g)` from `(g, a • g, b • g, c • g)`
-/

@[expose] public section


open OracleComp OracleSpec ENNReal

namespace DiffieHellman

variable {F : Type} [Field F]
variable {G : Type} [AddCommGroup G] [Module F G]

/-! ## DLog (Discrete Logarithm) -/

/-- A DLog adversary receives a generator and a group element, and tries to find the
discrete logarithm (scalar). -/
def DLogAdversary (F G : Type) := G → G → ProbComp F

section DLog

variable [DecidableEq F] [SampleableType F]

/-- DLog experiment: sample a random scalar `x`, give the adversary `(g, x • g)`,
and check whether the adversary's guess equals `x`. -/
def dlogExperiment (g : G) (adversary : DLogAdversary F G) : ProbComp Bool := do
  let x ← $ᵗ F
  let x' ← adversary g (x • g)
  return decide (x' = x)

end DLog

/-! ## CDH (Computational Diffie-Hellman) -/

/-- A CDH adversary receives `(g, a • g, b • g)` and tries to compute `(a * b) • g`.
`_F` is a phantom type parameter for the scalar field, enabling Lean to infer `F`
at call sites of `cdhExperiment`. -/
def CDHAdversary (_F G : Type) := G → G → G → ProbComp G

section CDH

variable [SampleableType F] [DecidableEq G]

/-- CDH experiment: sample random scalars `a, b`, give the adversary `(g, a • g, b • g)`,
and check whether the adversary's output equals `(a * b) • g`. -/
def cdhExperiment (g : G) (adversary : CDHAdversary F G) : ProbComp Bool := do
  let a ← $ᵗ F; let b ← $ᵗ F
  let h ← adversary g (a • g) (b • g)
  return decide (h = (a * b) • g)

end CDH

/-! ## DDH (Decisional Diffie-Hellman) -/

/-- A DDH adversary receives `(g, A, B, T)` and guesses whether `T = (a * b) • g`
(real) or `T` is a random group element (random).
`_F` is a phantom type parameter for the scalar field, enabling Lean to infer `F`
at call sites of `ddhGame` and related definitions. -/
def DDHAdversary (_F G : Type) := G → G → G → G → ProbComp Bool

section DDH

variable [SampleableType F]

/-- DDH game: sample random scalars `a, b` and a bit. If the bit is `true`, set
`c = a * b` (the real DH scalar); otherwise sample `c ← $ᵗ F` independently. The adversary
receives `(g, a • g, b • g, c • g)` and wins by guessing the bit. Its Boolean bias is
`ddhAdvantage` (`boolBias_evalDist_ddhGame`).

All sampling is from the scalar field `F`, so the game is well-defined for any
`Module F G` without requiring that `g` generates all of `G`. -/
def ddhGame (g : G) (adversary : DDHAdversary F G) : ProbComp Bool := do
  let a ← $ᵗ F; let b ← $ᵗ F
  let bit ← $ᵗ Bool
  let c ← if bit then pure (a * b) else $ᵗ F
  let b' ← adversary g (a • g) (b • g) (c • g)
  return (bit == b')

/-! ## DDH: real and random experiments -/

/-- DDH real experiment: the adversary receives a genuine DH triple
`(g, a • g, b • g, (a * b) • g)`. -/
def ddhRealExperiment (g : G) (adversary : DDHAdversary F G) : ProbComp Bool := do
  let a ← $ᵗ F; let b ← $ᵗ F
  adversary g (a • g) (b • g) ((a * b) • g)

/-- DDH random experiment: the adversary receives `(g, a • g, b • g, c • g)` with independent
`c ← $ᵗ F`. -/
def ddhRandomExperiment (g : G) (adversary : DDHAdversary F G) : ProbComp Bool := do
  let a ← $ᵗ F; let b ← $ᵗ F; let c ← $ᵗ F
  adversary g (a • g) (b • g) (c • g)

/-- DDH advantage: the Boolean distance between the real and random DDH experiments. -/
noncomputable def ddhAdvantage (g : G) (adversary : DDHAdversary F G) : ℝ≥0∞ :=
  𝒟[ddhRealExperiment g adversary].boolDist 𝒟[ddhRandomExperiment g adversary]

end DDH

/-! ## Standard reductions among DLog / CDH / DDH -/

section Reductions

variable [DecidableEq G]

/-- Reduction from CDH solving to DDH distinguishing: compute a candidate DH share and compare it
with the target group element. This is the concrete reduction underlying the hardness implication
`DDH ⇒ CDH`. -/
def cdhToDDHReduction (adversary : CDHAdversary F G) : DDHAdversary F G := fun g A B T => do
  let h ← adversary g A B
  return decide (h = T)

/-- Reduction from DLog solving to CDH solving: recover the two exponents separately and rebuild
the shared DH value. This is the concrete reduction underlying `CDH ⇒ DLog`. -/
def dlogToCDHReduction (adversary : DLogAdversary F G) : CDHAdversary F G := fun g A B => do
  let a ← adversary g A
  let b ← adversary g B
  return (a * b) • g

/-- Direct DLog-to-DDH reduction obtained by composing the standard DLog-to-CDH and CDH-to-DDH
reductions. This is the concrete reduction underlying `DDH ⇒ DLog`. -/
def dlogToDDHReduction (adversary : DLogAdversary F G) : DDHAdversary F G :=
  cdhToDDHReduction (F := F) (dlogToCDHReduction (F := F) adversary)

end Reductions

section DDHBranch

variable [SampleableType F]

/-- The DDH game is a uniform-bit branch over the real and random DDH experiments. -/
private lemma ddhGame_probOutput_eq_branch (g : G) (adversary : DDHAdversary F G) (x : Bool) :
    Pr[= x | ddhGame g adversary] =
    Pr[= x | do
      let bit ← ($ᵗ Bool)
      let z ← if bit then ddhRealExperiment g adversary
               else ddhRandomExperiment g adversary
      pure (bit == z)] := by
  unfold ddhGame
  rw [probOutput_bind_congr fun a _ => probOutput_bind_bind_swap _ _ _ _,
      probOutput_bind_bind_swap]
  refine probOutput_bind_congr' ($ᵗ Bool) x fun bit => ?_
  cases bit <;> simp [ddhRealExperiment, ddhRandomExperiment]

/-- The Boolean bias of the DDH game is the DDH advantage. -/
theorem boolBias_evalDist_ddhGame (g : G) (adversary : DDHAdversary F G) :
    𝒟[ddhGame g adversary].boolBias = ddhAdvantage g adversary := by
  rw [ddhAdvantage, ← evalDist_boolBias_bind_uniformBool]
  simp only [MeasureTheory.Measure.boolBias, evalDist_apply_singleton,
    ddhGame_probOutput_eq_branch]

end DDHBranch

section CDHToDDH

variable [SampleableType F] [DecidableEq G]

/-- In the real DDH experiment, the CDH-to-DDH reduction succeeds exactly when the underlying CDH
adversary computed the correct shared DH value. -/
theorem probOutput_ddhRealExperiment_cdhToDDHReduction_eq_cdhExperiment (g : G)
    (adversary : CDHAdversary F G) :
    Pr[= true | ddhRealExperiment g (cdhToDDHReduction (F := F) adversary)] =
      Pr[= true | cdhExperiment g adversary] := rfl

private lemma probOutput_decide_smul_eq_inv_card
    [Fintype F] (g : G) (hg : Function.Bijective (· • g : F → G)) (h : G) :
    Pr[= true | ($ᵗ F) >>= fun c => pure (decide (h = c • g))] =
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
  obtain ⟨c₀, rfl⟩ := hg.surjective h
  simp only [probOutput_bind_eq_tsum, probOutput_uniformSample, probOutput_pure]
  rw [tsum_fintype, Finset.sum_eq_single c₀]
  · simp
  · intro c _ hne
    simp [show c₀ • g ≠ c • g from fun heq => hne (hg.injective heq).symm]
  · exact absurd (Finset.mem_univ c₀)

/-- In the random DDH experiment, the CDH-to-DDH reduction only matches the target with the uniform
baseline probability. The bijectivity assumption identifies scalar samples with uniformly sampled
group elements in the subgroup generated by `g`. -/
theorem probOutput_ddhRandomExperiment_cdhToDDHReduction_eq_uniformScalar
    [Fintype F] (g : G) (hg : Function.Bijective (· • g : F → G))
    (adversary : CDHAdversary F G) :
    Pr[= true | ddhRandomExperiment g (cdhToDDHReduction (F := F) adversary)] =
      (Fintype.card F : ℝ≥0∞)⁻¹ := by
  simp only [ddhRandomExperiment, cdhToDDHReduction]
  have key : ∀ a b : F,
      Pr[= true | ($ᵗ F) >>= fun c =>
        adversary g (a • g) (b • g) >>= fun h =>
          pure (decide (h = c • g))] =
        (Fintype.card F : ℝ≥0∞)⁻¹ := by
    intro a b
    rw [probOutput_bind_bind_swap, probOutput_bind_of_const _ fun h _ =>
      probOutput_decide_smul_eq_inv_card g hg h]
    simp [probFailure_of_liftM_PMF]
  rw [probOutput_bind_of_const _ fun a _ =>
    probOutput_bind_of_const _ fun b _ => key a b]
  simp [probFailure_of_liftM_PMF]

/-- Concrete form of the hardness implication `DDH ⇒ CDH`: a CDH solver can only beat the uniform
DH-target baseline `1 / |F|` by the DDH advantage of the associated adversary-map reduction. -/
theorem cdhSuccess_le_uniform_add_ddhAdvantage
    [Fintype F] (g : G) (hg : Function.Bijective (· • g : F → G))
    (adversary : CDHAdversary F G) :
    Pr[= true | cdhExperiment g adversary] ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ + ddhAdvantage g (cdhToDDHReduction (F := F) adversary) := by
  have h := MeasureTheory.Measure.apply_true_le_add_boolDist
    𝒟[ddhRealExperiment g (cdhToDDHReduction (F := F) adversary)]
    𝒟[ddhRandomExperiment g (cdhToDDHReduction (F := F) adversary)]
  simp only [evalDist_apply_singleton,
    probOutput_ddhRandomExperiment_cdhToDDHReduction_eq_uniformScalar g hg adversary] at h
  exact probOutput_ddhRealExperiment_cdhToDDHReduction_eq_cdhExperiment g adversary ▸ h

end CDHToDDH

section DLogToCDH

variable [SampleableType F]

private lemma dlogExperiment_probOutput_eq_tsum [DecidableEq F] (g : G)
    (adversary : DLogAdversary F G) :
    Pr[= true | dlogExperiment g adversary] =
      ∑' x : F, Pr[= x | $ᵗ F] * Pr[= x | adversary g (x • g)] := by
  unfold dlogExperiment
  rw [probOutput_bind_eq_tsum]
  refine tsum_congr fun x => ?_
  congr 1
  rw [probOutput_bind_eq_tsum]
  refine (tsum_eq_single x fun x' hx' => ?_).trans (by simp)
  simp [show (decide (x' = x) : Bool) = false by simp [hx']]

private lemma cdhExperiment_dlogToCDHReduction_probOutput_eq_tsum [DecidableEq G] (g : G)
    (adversary : DLogAdversary F G) :
    Pr[= true | cdhExperiment g (dlogToCDHReduction (F := F) adversary)] =
      ∑' (a : F) (b : F) (a' : F) (b' : F),
        Pr[= a | $ᵗ F] * (Pr[= b | $ᵗ F] * (Pr[= a' | adversary g (a • g)] *
          (Pr[= b' | adversary g (b • g)] *
            (if (a' * b') • g = (a * b) • g then 1 else 0)))) := by
  unfold cdhExperiment dlogToCDHReduction
  simp only [monad_norm, probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun a => tsum_congr fun b => tsum_congr fun a' => tsum_congr fun b' => ?_
  simp [probOutput_pure]

variable [DecidableEq F] [DecidableEq G]

/-- Concrete form of the hardness implication `CDH ⇒ DLog`: if a DLog adversary succeeds with
probability `p`, the induced CDH adversary succeeds with probability at least `p^2`. -/
theorem dlogSuccess_sq_le_cdhSuccess_dlogToCDHReduction
    (g : G) (adversary : DLogAdversary F G) :
    Pr[= true | dlogExperiment g adversary] ^ 2 ≤
      Pr[= true | cdhExperiment g (dlogToCDHReduction (F := F) adversary)] := by
  set w : F → ℝ≥0∞ := fun x => Pr[= x | $ᵗ F]
  set f : F → ℝ≥0∞ := fun x => Pr[= x | adversary g (x • g)]
  rw [sq, dlogExperiment_probOutput_eq_tsum, ← ENNReal.tsum_mul_right,
    cdhExperiment_dlogToCDHReduction_probOutput_eq_tsum]
  refine ENNReal.tsum_le_tsum fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun b => ?_
  calc w a * f a * (w b * f b)
      = w a * (w b * (f a * (f b * (if (a * b) • g = (a * b) • g then 1 else 0)))) := by
        simp only [ite_true, mul_one]
        ring
    _ ≤ ∑' (b' : F), w a * (w b * (f a *
          (Pr[= b' | adversary g (b • g)] *
            (if (a * b') • g = (a * b) • g then 1 else 0)))) := by
      exact ENNReal.le_tsum (f := fun b' => w a * (w b * (f a *
        (Pr[= b' | adversary g (b • g)] *
          (if (a * b') • g = (a * b) • g then 1 else 0))))) b
    _ ≤ ∑' (a' : F) (b' : F), w a * (w b * (Pr[= a' | adversary g (a • g)] *
          (Pr[= b' | adversary g (b • g)] *
            (if (a' * b') • g = (a * b) • g then 1 else 0)))) := by
      exact ENNReal.le_tsum (f := fun a' => ∑' b', w a * (w b *
        (Pr[= a' | adversary g (a • g)] * (Pr[= b' | adversary g (b • g)] *
          (if (a' * b') • g = (a * b) • g then 1 else 0))))) a

/-- Concrete form of the hardness implication `DDH ⇒ DLog`, obtained by composing the previous two
adversary-map reductions. -/
theorem dlogSuccess_sq_le_uniform_add_ddhAdvantage
    [Fintype F] (g : G) (hg : Function.Bijective (· • g : F → G))
    (adversary : DLogAdversary F G) :
    Pr[= true | dlogExperiment g adversary] ^ 2 ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ + ddhAdvantage g (dlogToDDHReduction (F := F) adversary) :=
  (dlogSuccess_sq_le_cdhSuccess_dlogToCDHReduction g adversary).trans
    (cdhSuccess_le_uniform_add_ddhAdvantage g hg (dlogToCDHReduction (F := F) adversary))

end DLogToCDH

/-! ## Generable relation for discrete log -/

section DLogGenerable

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [Fintype G] [SampleableType G] [DecidableEq G]
variable (g : G)

variable (F) in
/-- The discrete log relation is generable by sampling `sk ← $ᵗ F` and returning
`(sk • g, sk)`. -/
def dlogGenerable :
    GenerableRelation G F (fun pk sk => decide (sk • g = pk)) where
  gen := do let sk ← $ᵗ F; return (sk • g, sk)
  gen_sound := fun _ _ _ => by grind

end DLogGenerable

/-! ## Cyclic group instantiation helpers -/

section CyclicInstantiation

variable {G : Type} [AddCommGroup G] [Fintype G]

/-- A generator `g` is nondegenerate if `fun a => a.val • g` surjects onto `G`,
ruling out the trivial case. Uses additive notation consistent with `Module F G`. -/
def NondegenerateGenerator (g : G) : Prop :=
  Function.Surjective fun a : Fin (Fintype.card G) => a.val • g

/-- A nondegenerate generator of a nontrivial group is nonzero. -/
lemma NondegenerateGenerator.ne_zero [Nontrivial G] {g : G}
    (hg : NondegenerateGenerator (G := G) g) : g ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx⟩ := exists_ne (0 : G)
  obtain ⟨a, ha⟩ := hg x
  exact hx (by simpa using ha.symm)

end CyclicInstantiation

end DiffieHellman
