/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SymmEncAlg
import VCVio.OracleComp.Coinductive.PolyTimeConstructions

/-!
# Katz–Lindell Definition 3.8: Private-Key Encryption Schemes

The asymptotic syntax of private-key encryption from Katz and Lindell, *Introduction to
Modern Cryptography*, Definition 3.8: a security-parameter-indexed family of
`SymmEncAlg`s (following the library convention that asymptotic statements quantify over
scheme families), split into its correctness half (`SchemeCorrect`, decryption recovers
every message) and its efficiency half (`SchemePolyTime`, the three algorithms are
Turing-machine-grounded polynomial time). The fixed-length variant with length parameter
`ℓ` is `FixedLengthScheme`, with message space `{0,1}^(ℓ n)` as `BitVec (ℓ n)`.

`IsPolyTimeFun` names polynomial-time computability of a pure function family, used by
the semantic-security statements of §3.2.2: a function is polynomial-time computable
when its `pure`-lift over the coin oracle (the trivial random tape) is a polynomial-time
program family.

None of the §3.2 security theorems consume `SchemePolyTime` — the challenger, not the
reduction, runs the scheme's algorithms — but it is part of the textbook definition and
recorded here for fidelity.
-/


open OracleComp OracleSpec

namespace KatzLindell

variable {M K C : ℕ → Type}

/-- **Katz–Lindell Definition 3.8**, fixed-length variant: a private-key scheme family
whose message space at parameter `n` is the bitstrings `{0,1}^(ℓ n)`. -/
abbrev FixedLengthScheme (ℓ : ℕ → ℕ) (K C : ℕ → Type) :=
  (n : ℕ) → SymmEncAlg ProbComp (BitVec (ℓ n)) (K n) (C n)

/-- Correctness half of Katz–Lindell Definition 3.8: decryption recovers every message
with probability one, at every security parameter. -/
def SchemeCorrect (π : (n : ℕ) → SymmEncAlg ProbComp (M n) (K n) (C n)) : Prop :=
  ∀ n, (π n).Complete

/-- Efficiency half of Katz–Lindell Definition 3.8: key generation, encryption, and
decryption are all polynomial-time program families, at pinned canonical boundaries
for messages, keys, and ciphertexts. Fidelity-only in §3.2 — the security theorems
never run the honest algorithms inside a reduction.

**Interim caveat**: the scheme algorithms are `ProbComp` programs over `unifSpec`,
whose query indices range over all of `ℕ` — an infinite type admits no fixed-width
canonical interface encoding, so `OracleSpec.InterfaceBitEnc (fun _ => unifSpec)` is
uninhabited and this definition is currently vacuous. The faithful definition awaits
the `ProbComp → coinSpec` derandomization bridge (the textbook's algorithms run on a
random bit tape, i.e. the coin oracle), the same bridge blocking Claim 3.12; the
interface encoding is an explicit parameter so the statement shape is already final. -/
def SchemePolyTime (eM : Computability.BitEncFam M) (eK : Computability.BitEncFam K)
    (eC : Computability.BitEncFam C)
    (eU : OracleSpec.InterfaceBitEnc (fun _ => unifSpec))
    (π : (n : ℕ) → SymmEncAlg ProbComp (M n) (K n) (C n)) : Prop :=
  OracleComp.IsPolyTime ⟨.unit, eK, eU⟩ (fun n (_ : Unit) => (π n).keygen) ∧
    OracleComp.IsPolyTime ⟨eK.pair eM, eC, eU⟩ (fun n (p : K n × M n) =>
      (π n).encrypt p.1 p.2) ∧
    OracleComp.IsPolyTime ⟨eK.pair eC, eM.option, eU⟩ (fun n (p : K n × C n) =>
      (π n).decrypt p.1 p.2)

/-- A pure function family is polynomial-time computable, at pinned canonical
boundaries, when its `pure`-lift (over the coin oracle, i.e. with a random tape it
never reads) is a polynomial-time program family. Used to state the efficiency
hypotheses of the semantic-security definitions. -/
def IsPolyTimeFun {α β : ℕ → Type} (eIn : Computability.BitEncFam α)
    (eOut : Computability.BitEncFam β) (g : (n : ℕ) → α n → β n) : Prop :=
  OracleComp.IsPolyTime (BoundaryData.coin eIn eOut)
    fun n x => (pure (g n x) : OracleComp coinSpec (β n))

/-! `IsPolyTimeFun` for a concrete function family is discharged by supplying uniform
machine families through `OracleComp.isPolyTime_pure_of_witnesses` (or, for input types
of polynomially bounded cardinality, hypothesis-free via
`OracleComp.isPolyTime_pure_ofFintype`). There is deliberately no hypothesis-free route
for bitvector functions: a finite table over `BitVec n` inputs is `2 ^ n` states of
advice, exactly the collapse the machine model's advice bound exists to prevent — even
the identity needs a genuine (deferred) base machine. -/

end KatzLindell
