/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import KatzLindell.Chapter03.PrivKEav
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
- `eavGuessGame_advantage_prgEnc_eq`: the probability core of Theorem 3.18, an *exact* advantage
  identity — the eavesdropping bias against `prgEnc` is precisely twice the PRG-distinguishing
  advantage of `prgReduction A` (real branch = `PrivK^eav` on the nose, ideal branch = a fair
  coin by the one-time-pad change of variables `y ↦ m_b ^^^ y`).
- `eavSecure_prgEnc`: Theorem 3.18, the identity fed to the generic reduction meta-theorem
  `SecurityGame.secureAgainst_of_poly_reduction` with loss factor `2`.

## Surfaced gap

The reduction `prgReduction` sequences the eavesdropping adversary's *choose* and *distinguish*
phases into one program and post-composes the result with `· == b`. The output post-map is
closed abstractly (`OracleComp.IsPolyTime.map`, derivable at canonical boundaries), so the single
remaining gap is closure under **sequential composition of two query-bearing programs**
(`IsPolyTime.bind`) — the two-phase machine construction, whose statement the canonical
boundaries finally make well-formed (the mid boundary is shared by construction). The
reduction's polynomial time is therefore the one explicit hypothesis of `eavSecure_prgEnc`;
the advantage side is proven. Note the boundary parameters make the Katz–Lindell `1^n`
convention visible: the theorem explicitly requires the expansion length `ℓ` to be polynomially
bounded (`pℓ`/`hℓ`), which the textbook leaves implicit in "expansion factor `ℓ(n)` polynomial
in `n`".
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

/-! ## The advantage reduction: the probability core of Theorem 3.18 -/

section AdvantageCore

variable (prg : (n : ℕ) → PRGScheme (BitVec n) (BitVec (ℓ n)))
  (A : PPTEavAdversary (fun n => BitVec (ℓ n)) (fun n => BitVec (ℓ n)))

/-- Comparing a Boolean experiment's output against an independently pre-sampled fair
coin succeeds with probability exactly `1/2`, whatever prefix sampling precedes the
coin: the coin is uniform and independent of the comparison target. -/
private lemma probOutput_bind_uniformBool_bind_beq {γ : Type} (pref : ProbComp γ)
    (q : γ → ProbComp Bool) :
    Pr[= true | do
      let a ← pref
      let b ← ($ᵗ Bool)
      let z ← q a
      pure (z == b)] = 1 / 2 := by
  rw [probOutput_bind_eq_tsum]
  have hinner : ∀ a : γ, Pr[= true | do
      let b ← ($ᵗ Bool)
      let z ← q a
      pure (z == b)] = 1 / 2 := by
    intro a
    rw [probOutput_bind_eq_tsum, tsum_fintype (L := .unconditional _), Fintype.sum_bool]
    have ht : Pr[= true | do let z ← q a; pure (z == true)] = Pr[= true | q a] := by
      simp
    have hf : Pr[= true | do let z ← q a; pure (z == false)] = Pr[= false | q a] := by
      simp
    rw [ht, hf, probOutput_uniformSample, probOutput_uniformSample]
    simp only [Fintype.card_bool, Nat.cast_ofNat]
    rw [← left_distrib, probOutput_true_add_false]
    simp [one_div]
  simp_rw [hinner]
  rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_sub]
  simp

/-- **Real branch of the reduction**: on a PRG output `y = G(s)`, `prgReduction A`
reproduces the eavesdropping experiment `PrivK^eav` against `prgEnc prg` exactly. -/
theorem probOutput_prgRealExpFamily_prgReduction (n : ℕ) :
    Pr[= true | prgRealExpFamily prg (prgReduction A) n]
      = Pr[= true | privKEav (prgEnc prg) A n] := by
  have hreal : prgRealExpFamily prg (prgReduction A) n = (do
      let s ← $ᵗ BitVec n
      let ms ← simulateQ uniformSampleImpl (A.choose n)
      let b ← ($ᵗ Bool)
      let b' ← simulateQ uniformSampleImpl
        (A.distinguish n (ms.2.2, (if b then ms.2.1 else ms.1) ^^^ (prg n).gen s))
      pure (b' == b)) := by
    simp only [prgRealExpFamily, prgReduction, OracleComp.coin, simulateQ_bind,
      simulateQ_spec_query, simulateQ_pure, uniformSampleImpl]
  have hpriv : privKEav (prgEnc prg) A n = (do
      let ms ← simulateQ uniformSampleImpl (A.choose n)
      let s ← $ᵗ BitVec n
      let b ← ($ᵗ Bool)
      let b' ← simulateQ uniformSampleImpl
        (A.distinguish n (ms.2.2, (if b then ms.2.1 else ms.1) ^^^ (prg n).gen s))
      pure (b == b')) := by
    simp only [privKEav, EavExp, prgEnc, SymmEncAlg.keystreamEnc,
      PPTEavAdversary.toEavAdversary, pure_bind]
  rw [hreal, hpriv, probOutput_bind_bind_swap]
  simp_rw [Bool.beq_comm]

/-- **Ideal branch of the reduction**: on a uniform value `y`, the masked message
`m_b ^^^ y` is uniform independently of the hidden bit `b`, so the reduction's guess
matches a fresh fair coin — probability exactly `1/2`. -/
theorem probOutput_prgIdealExpFamily_prgReduction (n : ℕ) :
    Pr[= true | prgIdealExpFamily (prgReduction A) n] = 1 / 2 := by
  have hideal : prgIdealExpFamily (prgReduction A) n = (do
      let r ← $ᵗ BitVec (ℓ n)
      let ms ← simulateQ uniformSampleImpl (A.choose n)
      let b ← ($ᵗ Bool)
      let b' ← simulateQ uniformSampleImpl
        (A.distinguish n (ms.2.2, (if b then ms.2.1 else ms.1) ^^^ r))
      pure (b' == b)) := by
    simp only [prgIdealExpFamily, prgReduction, OracleComp.coin, simulateQ_bind,
      simulateQ_spec_query, simulateQ_pure, uniformSampleImpl]
  rw [hideal, probOutput_bind_bind_swap]
  refine Eq.trans (probOutput_bind_congr' _ _ fun ms => ?_)
    (probOutput_bind_uniformBool_bind_beq (simulateQ uniformSampleImpl (A.choose n))
      (fun ms => do
        let r ← $ᵗ BitVec (ℓ n)
        simulateQ uniformSampleImpl (A.distinguish n (ms.2.2, r))))
  rw [probOutput_bind_bind_swap]
  refine probOutput_bind_congr' _ _ fun b => ?_
  have hxor : Function.Bijective
      (fun r : BitVec (ℓ n) => (if b then ms.2.1 else ms.1) ^^^ r) := by
    refine Function.Involutive.bijective fun r => ?_
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  simpa using probOutput_bind_bijective_uniform_cross (BitVec (ℓ n))
    (fun r => (if b then ms.2.1 else ms.1) ^^^ r) hxor
    (fun y => simulateQ uniformSampleImpl (A.distinguish n (ms.2.2, y)) >>=
      fun b' => pure (b' == b)) true

/-- **The advantage identity behind Theorem 3.18**: the eavesdropping bias of any
two-phase adversary against `prgEnc prg` is *exactly twice* the PRG-distinguishing
advantage of the reduction `prgReduction A` — the real branch reproduces `PrivK^eav`
and the ideal branch is a fair coin, so the distinguishing gap is the distance of the
guessing probability from `1/2`. -/
theorem eavGuessGame_advantage_prgEnc_eq (n : ℕ) :
    (eavGuessGame (prgEnc prg)).advantage A n
      = 2 * (prgSecurityGame prg).advantage (prgReduction A) n := by
  change ENNReal.ofReal (privKEav (prgEnc prg) A n).boolBiasAdvantage
    = 2 * ENNReal.ofReal ((prgRealExpFamily prg (prgReduction A) n).boolDistAdvantage
        (prgIdealExpFamily (prgReduction A) n))
  rw [ProbComp.boolBiasAdvantage_eq_two_mul_abs_sub_half, ProbComp.boolDistAdvantage,
    probOutput_prgRealExpFamily_prgReduction prg A n,
    probOutput_prgIdealExpFamily_prgReduction A n,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  simp

end AdvantageCore

/-- **Katz–Lindell Theorem 3.18**: if `prg` is a secure pseudorandom generator, the PRG-based
scheme `prgEnc prg` is eavesdropping-secure.

The advantage side is proven outright — `eavGuessGame_advantage_prgEnc_eq` gives the bias as
*exactly* twice the reduction's PRG-distinguishing advantage. The one remaining hypothesis is
`hppt`, the reduction's **polynomial time**, blocked on `IsPolyTime.bind` as described in the
module docstring. Security then transfers through the generic polynomial-loss reduction
meta-theorem `SecurityGame.secureAgainst_of_poly_reduction` with loss factor `2`. -/
theorem eavSecure_prgEnc (pℓ : Polynomial ℕ) (hℓ : ∀ n, ℓ n ≤ pℓ.eval n)
    (prg : (n : ℕ) → PRGScheme (BitVec n) (BitVec (ℓ n)))
    (hprg : PRGSecure (Computability.BitEncFam.bitVec ℓ pℓ hℓ) prg)
    (hppt : ∀ (A : PPTEavAdversary (fun n => BitVec (ℓ n)) (fun n => BitVec (ℓ n))),
      A.IsPPT (.bitVec ℓ pℓ hℓ) (.bitVec ℓ pℓ hℓ) →
        OracleComp.IsPolyTime
          (BoundaryData.coin (.bitVec ℓ pℓ hℓ) .bool) (prgReduction A)) :
    EavSecure (prgEnc prg) (.bitVec ℓ pℓ hℓ) (.bitVec ℓ pℓ hℓ) :=
  SecurityGame.secureAgainst_of_poly_reduction (loss := 2) hppt
    (fun A n => le_of_eq (by
      rw [eavGuessGame_advantage_prgEnc_eq prg A n]
      simp))
    hprg

end KatzLindell
