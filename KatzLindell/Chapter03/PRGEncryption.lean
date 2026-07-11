/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import KatzLindell.Chapter03.PrivKEav
import VCVio.CryptoFoundations.SymmEncAlg.Keystream
import VCVio.CryptoFoundations.PRGGame
import VCVio.OracleComp.Coinductive.PolyTimeCarry
import VCVio.OracleComp.Coinductive.PolyTimeConstructions
import VCVio.OracleComp.Coinductive.PolyTimeSeqComp

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
- `prgReductionGlue` / `PRGReductionGlueWitness`: the reduction's pure inter-phase glue
  (hidden-bit select, XOR mask, state projection) and its machine-witness type — the sole
  residual polynomial-time hypothesis.
- `isPolyTime_prgReduction`: the reduction is polynomial time, assembled from the closure
  calculus of `OracleComp.IsPolyTime`, given a glue witness.
- `eavSecure_prgEnc`: Theorem 3.18, the advantage identity and the polynomial-time proof fed
  to the generic reduction meta-theorem `SecurityGame.secureAgainst_of_poly_reduction` with
  loss factor `2`.

## Surfaced gap

The reduction `prgReduction` sequences the eavesdropping adversary's *choose* and *distinguish*
phases into one program, threads its own challenge value and a sampled hidden bit across them,
and post-composes the comparison `· == b`. All of that is discharged by the closure calculus in
`isPolyTime_prgReduction`: `OracleComp.IsPolyTime.bind` chains the query-bearing stages at
shared mid boundaries, `IsPolyTime.carry` threads the fixed-width challenge and hidden bit
across the phases, `IsPolyTime.precompComp` reshapes inputs, and `IsPolyTime.map` closes the
final comparison at the canonical `Bool` boundary. The single residual hypothesis is `hglue`, a
machine witness (`PRGReductionGlueWitness`) for the reduction's pure inter-phase glue
`prgReductionGlue` — per-adversary because its boundary contains the adversary's own
cross-phase state encoding `A.encState`. Splitting the glue into an `A`-independent bitvector
atom (select and XOR) and a pure block permutation around the inert state block would make the
residue adversary-free; that refinement is not done here. Note the boundary parameters make
the Katz–Lindell `1^n` convention visible: the theorem explicitly requires the expansion
length `ℓ` to be polynomially bounded (`pℓ`/`hℓ`), which the textbook leaves implicit in
"expansion factor `ℓ(n)` polynomial in `n`".
-/

open ENNReal OracleComp OracleSpec SymmEncAlg PRGScheme Computability

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

/-! ## The reduction's polynomial time

`prgReduction A` factors as three query-bearing stages chained by
`OracleComp.IsPolyTime.bind` at shared mid boundaries — the choose phase with the challenge
value carried across it, a coin flip with the accumulated data carried across it, and the
distinguish phase behind the pure glue `prgReductionGlue` with the hidden bit carried across
it — followed by the comparison `· == b`, an output map at the canonical `Bool` boundary. -/

section PolyTime

/-- The unit boundary has width zero, so pairing a trailing unit is string-equal to the bare
encoding. -/
private lemma enc_pair_unit {α : ℕ → Type} (e : BitEncFam α) (n : ℕ) (x : α n) :
    (e.pair BitEncFam.unit).enc n (x, PUnit.unit) = e.enc n x := by
  simp [BitEncFam.pair, BitEncFam.const, natToBits]

/-- Pad a value with a trailing unit: the identity machine recoded along the string-equal
width-zero pairing — the input reshaping that feeds a bare value to a carried `Unit`-input
phase. -/
private noncomputable def pairUnitWit {α : ℕ → Type} (e : BitEncFam α) :
    EncPolyTimeFam e.enc (e.pair BitEncFam.unit).enc (fun _ x => (x, PUnit.unit)) :=
  (EncPolyTimeFam.id e.enc).recode (fun _ x => x) (fun _ x => (x, PUnit.unit))
    (fun _ _ => rfl) (enc_pair_unit e)

/-- The reduction's inter-phase pure glue: reshape the pipeline state after the coin flip —
the challenge value `y`, the choose phase's output `(m₀, m₁, st)`, and the hidden bit `b` —
into the distinguish phase's carried input `(b, (st, (if b then m₁ else m₀) ^^^ y))`:
hidden-bit select, XOR mask, and state projection. This deterministic bitstring map is the
exact base-machine ticket surfaced by `eavSecure_prgEnc`; its machine-witness type is
`PRGReductionGlueWitness`. -/
def prgReductionGlue (A : PPTEavAdversary (fun n => BitVec (ℓ n)) (fun n => BitVec (ℓ n)))
    (n : ℕ) (q : (BitVec (ℓ n) × (BitVec (ℓ n) × BitVec (ℓ n) × A.State n)) × Bool) :
    Bool × (A.State n × BitVec (ℓ n)) :=
  (q.2, (q.1.2.2.2, (if q.2 then q.1.2.2.1 else q.1.2.1) ^^^ q.1.1))

/-- The machine-witness type for the reduction's pure glue `prgReductionGlue A`, between its
pinned boundary encodings: from the mid-pipeline layout (challenge value, messages and state,
hidden bit) to the distinguish phase's carried input (hidden bit alongside the
state/ciphertext pair). The sole residual hypothesis of `eavSecure_prgEnc` — per-adversary
because the boundary contains the adversary's own cross-phase state encoding `A.encState`. -/
abbrev PRGReductionGlueWitness (pℓ : Polynomial ℕ) (hℓ : ∀ n, ℓ n ≤ pℓ.eval n)
    (A : PPTEavAdversary (fun n => BitVec (ℓ n)) (fun n => BitVec (ℓ n))) : Type 1 :=
  EncPolyTimeFam
    ((((BitEncFam.bitVec ℓ pℓ hℓ).pair ((BitEncFam.bitVec ℓ pℓ hℓ).pair
      ((BitEncFam.bitVec ℓ pℓ hℓ).pair A.encState))).pair BitEncFam.bool).enc)
    ((BitEncFam.bool.pair (A.encState.pair (BitEncFam.bitVec ℓ pℓ hℓ))).enc)
    (prgReductionGlue A)

/-- **The reduction `prgReduction A` is polynomial time**, assembled from the closure
calculus: the choose phase crosses the carried challenge value (`IsPolyTime.carry` +
`IsPolyTime.precompComp` against the width-zero unit pad), the coin flip carries the
accumulated data, the distinguish phase consumes the glued input, the three stages chain by
`IsPolyTime.bind` at the shared mid boundaries, and the final comparison `· == b` is an
output map at the canonical `Bool` boundary (`IsPolyTime.map`). The sole machine hypothesis
is `hglue`, a witness for the pure inter-phase glue `prgReductionGlue`. -/
theorem isPolyTime_prgReduction (pℓ : Polynomial ℕ) (hℓ : ∀ n, ℓ n ≤ pℓ.eval n)
    (A : PPTEavAdversary (fun n => BitVec (ℓ n)) (fun n => BitVec (ℓ n)))
    (hA : A.IsPPT (.bitVec ℓ pℓ hℓ) (.bitVec ℓ pℓ hℓ))
    (hglue : Nonempty (PRGReductionGlueWitness pℓ hℓ A)) :
    OracleComp.IsPolyTime (BoundaryData.coin (.bitVec ℓ pℓ hℓ) .bool) (prgReduction A) := by
  obtain ⟨wit⟩ := hglue
  set eR : BitEncFam (fun n => BitVec (ℓ n)) := .bitVec ℓ pℓ hℓ
  set eMMSt : BitEncFam (fun n => BitVec (ℓ n) × (BitVec (ℓ n) × A.State n)) :=
    eR.pair (eR.pair A.encState)
  -- Stage 1: the choose phase, with the challenge value carried across it.
  have h₁ : OracleComp.IsPolyTime (BoundaryData.coin eR (eR.pair eMMSt))
      (fun n (y : BitVec (ℓ n)) => (y, ·) <$> A.choose n) :=
    (hA.1.carry eR).precompComp (fun _ y => (y, PUnit.unit)) eR (pairUnitWit eR)
  -- Stage 2: the coin flip, with the accumulated data carried across it.
  have h₂ : OracleComp.IsPolyTime
      (BoundaryData.coin (eR.pair eMMSt) ((eR.pair eMMSt).pair .bool))
      (fun n (p : BitVec (ℓ n) × (BitVec (ℓ n) × BitVec (ℓ n) × A.State n)) =>
        (p, ·) <$> OracleComp.coin) :=
    (OracleComp.isPolyTime_coin.carry (eR.pair eMMSt)).precompComp
      (fun _ p => (p, PUnit.unit)) (eR.pair eMMSt) (pairUnitWit (eR.pair eMMSt))
  -- Stage 3: the glue, then the distinguish phase with the hidden bit carried across it.
  have h₃ : OracleComp.IsPolyTime
      (BoundaryData.coin ((eR.pair eMMSt).pair .bool) (BitEncFam.bool.pair .bool))
      (fun n (q : (BitVec (ℓ n) × (BitVec (ℓ n) × BitVec (ℓ n) × A.State n)) × Bool) =>
        (q.2, ·) <$> A.distinguish n
          (q.1.2.2.2, (if q.2 then q.1.2.2.1 else q.1.2.1) ^^^ q.1.1)) :=
    (hA.2.carry .bool).precompComp (prgReductionGlue A) ((eR.pair eMMSt).pair .bool) wit
  -- Chain the stages and post-map the comparison against the carried hidden bit.
  have h₁₂ := OracleComp.IsPolyTime.bind
    (bd := BoundaryData.coin eR ((eR.pair eMMSt).pair .bool)) (eR.pair eMMSt) h₁ h₂
  have h₁₂₃ := OracleComp.IsPolyTime.bind
    (bd := BoundaryData.coin eR (BitEncFam.bool.pair .bool)) ((eR.pair eMMSt).pair .bool)
    h₁₂ h₃
  have hmap := h₁₂₃.map (fun _ (p : Bool × Bool) => p.2 == p.1) .bool (.C 4)
    (fun n => by simp)
  refine hmap.congr (fun n y => ?_)
  simp only [prgReduction, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]

end PolyTime

/-- **Katz–Lindell Theorem 3.18**: if `prg` is a secure pseudorandom generator, the PRG-based
scheme `prgEnc prg` is eavesdropping-secure.

The advantage side is proven outright — `eavGuessGame_advantage_prgEnc_eq` gives the bias as
*exactly* twice the reduction's PRG-distinguishing advantage — and the reduction's polynomial
time is proven from the closure calculus in `isPolyTime_prgReduction`. The one remaining
hypothesis is `hglue`, a per-adversary machine witness for the reduction's pure inter-phase
glue `prgReductionGlue` (see the module docstring). Security then transfers through the
generic polynomial-loss reduction meta-theorem `SecurityGame.secureAgainst_of_poly_reduction`
with loss factor `2`. -/
theorem eavSecure_prgEnc (pℓ : Polynomial ℕ) (hℓ : ∀ n, ℓ n ≤ pℓ.eval n)
    (prg : (n : ℕ) → PRGScheme (BitVec n) (BitVec (ℓ n)))
    (hprg : PRGSecure (Computability.BitEncFam.bitVec ℓ pℓ hℓ) prg)
    (hglue : ∀ (A : PPTEavAdversary (fun n => BitVec (ℓ n)) (fun n => BitVec (ℓ n))),
      Nonempty (PRGReductionGlueWitness pℓ hℓ A)) :
    EavSecure (prgEnc prg) (.bitVec ℓ pℓ hℓ) (.bitVec ℓ pℓ hℓ) :=
  SecurityGame.secureAgainst_of_poly_reduction (loss := 2)
    (fun A hA => isPolyTime_prgReduction pℓ hℓ A hA (hglue A))
    (fun A n => le_of_eq (by
      rw [eavGuessGame_advantage_prgEnc_eq prg A n]
      simp))
    hprg

end KatzLindell
