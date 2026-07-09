/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Examples.KatzLindell.PrivKEav

/-!
# Katz–Lindell §3.2.2: Semantic Security (Statements)

Statement-level formalization of semantic security in the presence of an eavesdropper
from Katz and Lindell, *Introduction to Modern Cryptography*, §3.2.2: the real/ideal
experiments (`semRealExp` / `semIdealExp`), Definition 3.13 (`SemanticallySecure`),
Claim 3.12 (`exists_simulator_predict_of_eavSecure`), and Theorem 3.14
(`eavSecure_iff_semanticallySecure`). The theorems are stated with `sorry`; the book
itself only sketches Claim 3.12 and defers Theorem 3.14 to the literature.

Beyond the book's own gaps, two concrete framework blockers keep the mechanization deferred, both
rooted in the uniform machine model rather than in the mathematics:

* **Derandomization bridge.** The simulator is a `coinSpec` program that must run the scheme's
  probabilistic `keygen`/`encrypt` internally. There is no `ProbComp → poly-time coinSpec` bridge
  turning an arbitrary probabilistic algorithm into a coin-oracle program; the existing
  `SamplerMachine`/`fillBits` machinery only derandomizes uniform bitvector sampling. This is why
  Claim 3.12 must additionally assume `SchemePolyTime π`.
* **Ensemble ↔ two-message translation.** Both theorems require moving between the predict-a-function
  presentation over plaintext ensembles and the two-message-choice eavesdropping game; that
  translation (and its advantage bookkeeping) is the second half of the deferred proof.

Two deliberate simplifications relative to the book, both flagged here:

* Variable-length data over `{0,1}*` is modeled as fixed-length-per-parameter bitstring
  families (`BitVec (vl n)` for target values, `BitVec (ll n)` for leakage), the book's
  own fixed-length regime; consequently the simulator's `1^{|m|}` input is dropped
  (message length is determined by `n`), and Claim 3.12's uniform distribution is over
  all of `{0,1}^n` rather than an efficiently sampleable subset.
* All efficient objects — adversary, simulator, plaintext ensemble, and the functions
  `f` (target) and `h` (leakage) — carry uniform `OracleComp.IsPolyTime` /
  `IsPolyTimeFun` hypotheses. The book lets `f` be arbitrary in Claim 3.12 via
  non-uniformity; the uniform machine model here must compute `f` inside the
  reduction, so polynomial-time computability is the honest uniform reading (as
  Definition 3.13 itself requires).
-/

open ENNReal OracleComp OracleSpec SymmEncAlg

namespace KatzLindell

variable {K C : ℕ → Type} {vl ll : ℕ → ℕ}

/-- Real semantic-security experiment: the adversary sees an encryption of `m` (drawn
from the ensemble `X`) together with the leakage `h m`, and tries to output `f m`. -/
noncomputable def semRealExp (π : (n : ℕ) → SymmEncAlg ProbComp (BitVec n) (K n) (C n))
    (X : (n : ℕ) → OracleComp coinSpec (BitVec n))
    (f : (n : ℕ) → BitVec n → BitVec (vl n)) (h : (n : ℕ) → BitVec n → BitVec (ll n))
    (A : (n : ℕ) → C n × BitVec (ll n) → OracleComp coinSpec (BitVec (vl n)))
    (n : ℕ) : ProbComp Bool := do
  let m ← simulateQ uniformSampleImpl (X n)
  let k ← (π n).keygen
  let c ← (π n).encrypt k m
  let v ← simulateQ uniformSampleImpl (A n (c, h n m))
  pure (v == f n m)

/-- Ideal semantic-security experiment: the simulator sees only the leakage `h m` and
tries to output `f m`. -/
noncomputable def semIdealExp (X : (n : ℕ) → OracleComp coinSpec (BitVec n))
    (f : (n : ℕ) → BitVec n → BitVec (vl n)) (h : (n : ℕ) → BitVec n → BitVec (ll n))
    (A' : (n : ℕ) → BitVec (ll n) → OracleComp coinSpec (BitVec (vl n)))
    (n : ℕ) : ProbComp Bool := do
  let m ← simulateQ uniformSampleImpl (X n)
  let v ← simulateQ uniformSampleImpl (A' n (h n m))
  pure (v == f n m)

/-- **Katz–Lindell Definition 3.13** (fixed-length form): a scheme is semantically
secure in the presence of an eavesdropper when every PPT adversary has a PPT simulator
that, seeing only the leakage, computes any polynomial-time target function of the
plaintext essentially as well — over every efficiently sampleable plaintext ensemble. -/
def SemanticallySecure (π : (n : ℕ) → SymmEncAlg ProbComp (BitVec n) (K n) (C n)) :
    Prop :=
  ∀ (vl ll : ℕ → ℕ)
    (A : (n : ℕ) → C n × BitVec (ll n) → OracleComp coinSpec (BitVec (vl n))),
    OracleComp.IsPolyTime A →
    ∃ A' : (n : ℕ) → BitVec (ll n) → OracleComp coinSpec (BitVec (vl n)),
      OracleComp.IsPolyTime A' ∧
        ∀ (X : (n : ℕ) → OracleComp coinSpec (BitVec n)),
          OracleComp.IsPolyTime (fun n (_ : Unit) => X n) →
          ∀ (f : (n : ℕ) → BitVec n → BitVec (vl n)), IsPolyTimeFun f →
          ∀ (h : (n : ℕ) → BitVec n → BitVec (ll n)), IsPolyTimeFun h →
          negligible fun n => ENNReal.ofReal
            |(Pr[= true | semRealExp π X f h A n]).toReal -
              (Pr[= true | semIdealExp X f h A' n]).toReal|

/-- **Katz–Lindell Claim 3.12** (statement): for an eavesdropping-secure scheme, any
PPT adversary receiving an encryption of a uniform plaintext has a ciphertext-free PPT
simulator computing every polynomial-time target function with almost the same success
probability. The book gives a proof sketch; the mechanization is deferred.

The `SchemePolyTime π` hypothesis — absent from the §3.2 indistinguishability theorems, where the
challenger runs the scheme — is genuinely needed here: the simulator is a `coinSpec` program that
must itself run `keygen`/`encrypt` internally to fabricate a ciphertext for `A`, so those algorithms
must be polynomial-time computable *inside a reduction*. This is exactly the concrete blocker for a
mechanized proof: closing the `sorry` requires a `ProbComp → poly-time coinSpec` **derandomization
bridge** turning the scheme's probabilistic algorithms into coin-oracle programs of the simulator
(the current `SamplerMachine`/`fillBits` bridge only derandomizes uniform bitvector sampling, not an
arbitrary `ProbComp`), together with the ensemble ↔ two-message-choice translation between this
predict-a-function form and the eavesdropping game. -/
theorem exists_simulator_predict_of_eavSecure
    (π : (n : ℕ) → SymmEncAlg ProbComp (BitVec n) (K n) (C n)) (hπ : EavSecure π)
    (hπ_poly : SchemePolyTime π)
    (vl : ℕ → ℕ) (A : (n : ℕ) → C n → OracleComp coinSpec (BitVec (vl n)))
    (hA : OracleComp.IsPolyTime A) :
    ∃ A' : (n : ℕ) → Unit → OracleComp coinSpec (BitVec (vl n)),
      OracleComp.IsPolyTime A' ∧
        ∀ (f : (n : ℕ) → BitVec n → BitVec (vl n)), IsPolyTimeFun f →
          negligible fun n => ENNReal.ofReal
            |(Pr[= true | do
                let m ← $ᵗ BitVec n
                let k ← (π n).keygen
                let c ← (π n).encrypt k m
                let v ← simulateQ uniformSampleImpl (A n c)
                pure (v == f n m)]).toReal -
              (Pr[= true | do
                let m ← $ᵗ BitVec n
                let v ← simulateQ uniformSampleImpl (A' n ())
                pure (v == f n m)]).toReal| := by
  sorry

/-- **Katz–Lindell Theorem 3.14** (statement): eavesdropping indistinguishability and
semantic security coincide. The book states this without proof; the mechanization is
deferred. -/
theorem eavSecure_iff_semanticallySecure
    (π : (n : ℕ) → SymmEncAlg ProbComp (BitVec n) (K n) (C n)) :
    EavSecure π ↔ SemanticallySecure π := by
  sorry

end KatzLindell
