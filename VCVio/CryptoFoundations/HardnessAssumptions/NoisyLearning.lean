/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module
public import VCVio.CryptoFoundations.SecExp
public import VCVio.OracleComp.ProbComp
public import VCVio.OracleComp.Constructions.SampleableType
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Noisy learning problems

This file defines `NoisyLearning.Problem`, the common shape of decision and search
assumptions of the "noisy linear learning" family: the adversary must distinguish
`(A, f(s, A) + e)` from `(A, u)` (decision) or recover `s` (search), where the
challenge `A`, the secret `s`, the error `e`, and the uniform reference `u` are
drawn from problem-specific distributions and `f` is the noiseless map.

Choosing the distributions specializes the single definition to the standard
assumptions:

- **LWE** over `ZMod q`: uniform matrix challenge, uniform secret, discrete
  Gaussian (or bounded) error — `zmodMatrixProblem`.
- **module- and ring-LWE**: the same matrix shape over a polynomial-ring carrier —
  `moduleMatrixProblem`, `ringProblem`.
- **LPN**: `ZMod 2` carrier with Bernoulli error — `lpnProblem`.
- **short-secret variants** (as used by ML-DSA's MLWE assumption): the secret
  and error samplers draw from an `η`-bounded box rather than the full carrier;
  these are obtained by supplying the appropriate samplers and live with the
  scheme that uses them.

The experiments (`experiment`, `advantage`, `searchExperiment`,
`searchAdvantage`) are stated once, generically. Lattice-specific
instantiations live downstream (e.g. `LatticeCrypto.HardnessAssumptions`,
which re-exports this namespace under its historical `LearningWithErrors`
name).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal Matrix

namespace NoisyLearning

/-- A generic noisy-learning problem instance.

`Sample` is the public challenge data (e.g. a matrix), `Secret` is the hidden
secret, and `Output` is the noisy linear output given to the adversary. The
same shape covers LWE, module-LWE, and LPN once the carrier and the samplers
are chosen. -/
structure Problem (Sample Secret Output : Type) where
  /-- Sampler for the public challenge (e.g. the matrix `A`). -/
  sampleChallenge : ProbComp Sample
  /-- Sampler for the hidden secret. Short-secret variants restrict this
  distribution; nothing in the experiments requires it to be uniform. -/
  sampleSecret : ProbComp Secret
  /-- Sampler for the additive error term. -/
  sampleError : ProbComp Output
  /-- The noiseless map, e.g. `fun s A => vecMul s A`. -/
  noiseless : Secret → Sample → Output
  /-- The uniform reference distribution the decision adversary must
  distinguish from. -/
  sampleUniform : ProbComp Output

section Generic

variable {Sample Secret Output : Type}

/-- The real noisy-learning distribution `(A, f(s, A) + e)`. -/
def distr [Add Output] (problem : Problem Sample Secret Output) :
    ProbComp (Sample × Output) := do
  let challenge ← problem.sampleChallenge
  let secret ← problem.sampleSecret
  let error ← problem.sampleError
  return (challenge, problem.noiseless secret challenge + error)

/-- The matching reference distribution `(A, u)`. -/
def uniformDistr (problem : Problem Sample Secret Output) :
    ProbComp (Sample × Output) := do
  let challenge ← problem.sampleChallenge
  let uniform ← problem.sampleUniform
  return (challenge, uniform)

/-- A decisional adversary for a noisy-learning problem. -/
abbrev Adversary (_problem : Problem Sample Secret Output) :=
  Sample × Output → ProbComp Bool

/-- The decision experiment: flip `b`, give the adversary either the real
distribution or the matching reference one, then check whether the guess
matches `b`. -/
def experiment [Add Output] (problem : Problem Sample Secret Output)
    (adv : Adversary problem) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let sample ← if b then distr problem else uniformDistr problem
  let b' ← adv sample
  return (b == b')

/-- Distinguishing advantage for the decision experiment. -/
noncomputable def advantage [Add Output] (problem : Problem Sample Secret Output)
    (adv : Adversary problem) : ℝ :=
  (experiment problem adv).boolBiasAdvantage

/-- Game 0: the adversary sees a sample from the real distribution. -/
def game0 [Add Output] (problem : Problem Sample Secret Output)
    (adv : Adversary problem) : ProbComp Bool := do
  adv (← distr problem)

/-- Game 1: the adversary sees a sample from the matching reference
distribution. -/
def game1 (problem : Problem Sample Secret Output)
    (adv : Adversary problem) : ProbComp Bool := do
  adv (← uniformDistr problem)

/-- A search adversary for a noisy-learning problem. -/
abbrev SearchAdversary (_problem : Problem Sample Secret Output) :=
  Sample × Output → ProbComp Secret

/-- The search experiment: the adversary must recover the sampled secret. -/
def searchExperiment [Add Output] [DecidableEq Secret]
    (problem : Problem Sample Secret Output) (adv : SearchAdversary problem) :
    ProbComp Bool := do
  let challenge ← problem.sampleChallenge
  let secret ← problem.sampleSecret
  let error ← problem.sampleError
  let secret' ← adv (challenge, problem.noiseless secret challenge + error)
  return decide (secret' = secret)

/-- Search advantage for the noisy-learning experiment. -/
noncomputable def searchAdvantage [Add Output] [DecidableEq Secret]
    (problem : Problem Sample Secret Output) (adv : SearchAdversary problem) : ℝ :=
  (Pr[= true | searchExperiment problem adv]).toReal

end Generic

section MatrixProblems

variable {α : Type}

/-- The standard matrix-based constructor. Choosing `α = ZMod q` recovers
ordinary LWE, while choosing a finite polynomial-ring carrier `α` gives the
corresponding module-LWE-style experiment. -/
def matrixProblem (n m : ℕ) [Semiring α] [DecidableEq α] [SampleableType α]
    (errSamp : ProbComp α) :
    Problem (Matrix (Fin n) (Fin m) α) (Fin n → α) (Fin m → α) where
  sampleChallenge := $ᵗ Matrix (Fin n) (Fin m) α
  sampleSecret := $ᵗ (Fin n → α)
  sampleError := ProbComp.sampleIID m errSamp
  noiseless := fun secret challenge => vecMul secret challenge
  sampleUniform := $ᵗ (Fin m → α)

/-- Ordinary LWE over `ZMod q` as a special case of `matrixProblem`. -/
def zmodMatrixProblem (n m q : ℕ) [NeZero q]
    (errSamp : ProbComp (ZMod q)) :
    Problem (Matrix (Fin n) (Fin m) (ZMod q)) (Fin n → ZMod q) (Fin m → ZMod q) :=
  matrixProblem (α := ZMod q) n m errSamp

/-- Module-LWE-style problems use the same experiment shape as ordinary LWE;
only the coefficient ring changes. This alias makes the intended instantiation
explicit at call sites. -/
def moduleMatrixProblem (n m : ℕ) [Semiring α] [DecidableEq α] [SampleableType α]
    (errSamp : ProbComp α) :
    Problem (Matrix (Fin n) (Fin m) α) (Fin n → α) (Fin m → α) :=
  matrixProblem (α := α) n m errSamp

/-- Ring-LWE-style problems are the rank-one module case: a single ring element
challenge per sample column. -/
def ringProblem (m : ℕ) [Semiring α] [DecidableEq α] [SampleableType α]
    (errSamp : ProbComp α) :
    Problem (Matrix (Fin 1) (Fin m) α) (Fin 1 → α) (Fin m → α) :=
  moduleMatrixProblem 1 m errSamp

/-- The ring problem is definitionally the rank-one module problem, so the two
decision advantages agree for every adversary. -/
lemma ringProblem_advantage (m : ℕ) [Semiring α] [DecidableEq α] [SampleableType α]
    (errSamp : ProbComp α)
    (adv : Adversary (moduleMatrixProblem 1 m errSamp)) :
    advantage (ringProblem m errSamp) adv = advantage (moduleMatrixProblem 1 m errSamp) adv :=
  rfl

end MatrixProblems

section LPN

/-- A Bernoulli bit with bias `k / d`: sample uniformly from `Fin d` and test
membership in the first `k` values. `bernoulliBit k d` is `1` with probability
`k / d` (for `k ≤ d`). -/
def bernoulliBit (k d : ℕ) [NeZero d] : ProbComp (ZMod 2) := do
  let x ← $ᵗ Fin d
  return if x.val < k then 1 else 0

/-- Learning parity with noise: the `ZMod 2` matrix problem with Bernoulli
error of bias `k / d` in each coordinate. -/
def lpnProblem (n m k d : ℕ) [NeZero d] :
    Problem (Matrix (Fin n) (Fin m) (ZMod 2)) (Fin n → ZMod 2) (Fin m → ZMod 2) :=
  zmodMatrixProblem n m 2 (bernoulliBit k d)

end LPN

end NoisyLearning
