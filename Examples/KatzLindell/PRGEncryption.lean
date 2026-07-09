/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Examples.KatzLindell.PrivKEav
import VCVio.CryptoFoundations.SymmEncAlg.Keystream
import VCVio.CryptoFoundations.PRGGame

/-!
# Katz–Lindell §3.3: Encryption from a Pseudorandom Generator (Construction 3.17)

The fixed-length private-key scheme `Enc_s(m) = m ⊕ G(s)` built from a pseudorandom generator
`G`, and its eavesdropping security (Katz–Lindell Theorem 3.18): if `G` is a secure PRG then the
scheme is EAV-secure.

- `prgEnc`: the construction, a thin instance of the XOR-keystream former
  `SymmEncAlg.keystreamEnc` with a uniform seed as the key and the PRG as the keystream generator.
- `prgEnc_correct`: correctness, immediate from `SymmEncAlg.keystreamEnc_complete`.
- `prgReduction`: the EAV → PRG distinguisher, a single coin-oracle program that runs the
  eavesdropping adversary against a challenge value in place of the keystream.
- `eavSecure_prgEnc`: Theorem 3.18, assembled from a PRG-advantage bound on `prgReduction` and its
  polynomial time via the generic reduction meta-theorem
  `SecurityGame.secureAgainst_of_poly_reduction`.

## Surfaced gap

The reduction `prgReduction` sequences the eavesdropping adversary's *choose* and *distinguish*
phases into one program and post-composes the result with `· == b`. Establishing its polynomial
time therefore needs closure of `OracleComp.IsPolyTime` under **sequential composition of two
query-bearing programs** (`IsPolyTime.bind`) and under **output maps of an abstract
`IsPolyTime` family** — neither is available: the machine model closes `IsPolyTime` under input
precomposition (`IsPolyTime.precomp`) and under output maps of *concrete finite-state* bundles
(`IsPolyTime.map_of_adversary`), but not of an existential `IsPolyTime` hypothesis whose machine
state is only `FinEncoding`, not `Fintype`. The two-phase `TwoPhaseGame` pipeline was designed to
avoid `IsPolyTime.bind`; carrying that all the way through the PRG reduction is the remaining
plumbing. Both the PRG-advantage bound (`prgReduction_advantage_bound`) and the reduction's
polynomial time (`prgReduction_isPolyTime`) are therefore taken as explicit hypotheses of
`eavSecure_prgEnc`, isolating exactly the two facts that the surrounding argument reduces to.
-/

open ENNReal OracleComp OracleSpec SymmEncAlg PRGScheme

namespace KatzLindell

variable {ℓ : ℕ → ℕ}

/-- **Katz–Lindell Construction 3.17**: the PRG-based fixed-length encryption scheme
`Enc_s(m) = m ⊕ G(s)`, with a uniform seed `s ∈ {0,1}^n` as the key and the PRG `G` as the
keystream generator. A thin instance of `SymmEncAlg.keystreamEnc`. -/
noncomputable def prgEnc (prg : (n : ℕ) → PRGScheme (BitVec n) (BitVec (ℓ n))) :
    (n : ℕ) → SymmEncAlg ProbComp (BitVec (ℓ n)) (BitVec n) (BitVec (ℓ n)) :=
  fun n => SymmEncAlg.keystreamEnc ($ᵗ BitVec n) (prg n).gen

/-- The PRG-based scheme is correct: decryption recovers every message, inherited from the
XOR-keystream correctness `SymmEncAlg.keystreamEnc_complete`. -/
theorem prgEnc_correct (prg : (n : ℕ) → PRGScheme (BitVec n) (BitVec (ℓ n))) :
    SchemeCorrect (prgEnc prg) :=
  fun _ => SymmEncAlg.keystreamEnc_complete _ _

/-- The EAV → PRG reduction distinguisher: on a challenge value `y` (either `G(s)` or uniform),
run the eavesdropping adversary against the ciphertext `m_b ⊕ y` for a fresh hidden bit `b`, and
report whether the adversary's guess matched `b`. When `y = G(s)` this is exactly `PrivK^eav`
against `prgEnc`; when `y` is uniform, `m_b ⊕ y` is uniform independent of `b`. -/
def prgReduction
    (A : PPTEavAdversary (fun n => BitVec (ℓ n)) (fun n => BitVec (ℓ n))) :
    PPTPRGAdversary (fun n => BitVec (ℓ n)) :=
  fun n y => do
    let (m₀, m₁, st) ← A.choose n
    let b ← OracleComp.coin
    let b' ← A.distinguish n (st, (if b then m₁ else m₀) ^^^ y)
    pure (b' == b)

/-- **Katz–Lindell Theorem 3.18**: if `prg` is a secure pseudorandom generator, the PRG-based
scheme `prgEnc prg` is eavesdropping-secure.

The two facts the argument reduces to are named as explicit hypotheses rather than proven here,
each isolating one deferred component (see the module docstring):

* `hadv` is the **advantage reduction** (the probability core): every eavesdropping adversary's
  bias against `prgEnc` is at most twice the PRG-distinguishing advantage of `prgReduction A` — on
  a real challenge `y = G(s)` the reduction reproduces `PrivK^eav`, and on a uniform challenge the
  masked message `m_b ⊕ y` is uniform independent of `b`, so the reduction's two branches coincide.
* `hppt` is the reduction's **polynomial time**, blocked on `IsPolyTime.bind` / abstract output-map
  closure as described in the module docstring.

Given both, security transfers through the generic polynomial-loss reduction meta-theorem
`SecurityGame.secureAgainst_of_poly_reduction` with loss factor `2`. -/
theorem eavSecure_prgEnc (prg : (n : ℕ) → PRGScheme (BitVec n) (BitVec (ℓ n)))
    (hprg : PRGSecure prg)
    (hadv : ∀ (A : PPTEavAdversary (fun n => BitVec (ℓ n)) (fun n => BitVec (ℓ n))) (n : ℕ),
      (eavGuessGame (prgEnc prg)).advantage A n ≤
        (↑(Polynomial.eval n (2 : Polynomial ℕ)) : ℝ≥0∞) *
          (prgSecurityGame prg).advantage (prgReduction A) n)
    (hppt : ∀ (A : PPTEavAdversary (fun n => BitVec (ℓ n)) (fun n => BitVec (ℓ n))),
      A.IsPPT → OracleComp.IsPolyTime (prgReduction A)) :
    EavSecure (prgEnc prg) :=
  SecurityGame.secureAgainst_of_poly_reduction (loss := 2) hppt hadv hprg

end KatzLindell
