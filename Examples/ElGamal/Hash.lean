/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Examples.ElGamal.Common
public import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA
public import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
public import VCVio.CryptoFoundations.HardnessAssumptions.EntropySmoothing
public import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.ProgramLogic.Tactics.Unary

/-!
# Hashed ElGamal Encryption

This file defines hashed ElGamal encryption and proves that its one-time IND-CPA
advantage is at most twice the sum of the DDH advantage and the entropy smoothing advantage.

Unlike standard ElGamal (where the message space is the group `G`), hashed ElGamal
uses a hash function `hash : HK → G → M` to map the DH shared secret into the
message space `M`. This allows encrypting messages in an arbitrary additive group `M`
(e.g. `BitVec n` with XOR).

## Security proof (4-game hop)

| Game | Description | Distance to next |
|------|-------------|-----------------|
| Game 0 (CPA) | Real hashed ElGamal | = DDH real |
| Game 1 | Replace the DH shared secret with an independent random multiple of `g` | DDH advantage |
| Game 2 (= Game 1) | Reinterpret as entropy smoothing real | 0 |
| Game 3 | Replace hash output with random | ES advantage |
| Game 4 (= 1/2) | The masking term is uniform, so the challenge bit is hidden | 0 |

Main theorem: the one-time IND-CPA advantage is at most `2 * (ddhAdvantage + esAdvantage)`.

## References

Port of EasyCrypt's `hashed_elgamal_std.ec`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal DiffieHellman

/-! ## Hashed ElGamal Scheme -/

/-- Hashed ElGamal encryption over a module `Module F G` with hash `hash : HK → G → M`.

| Operation | Definition |
|-----------|-----------|
| Keygen | Sample `hk ← $ᵗ HK`, `sk ← $ᵗ F`; PK = `(hk, sk • g)`, SK = `(hk, sk)` |
| Encrypt(pk, msg) | Sample `y ← $ᵗ F`; output `(y • g, hash hk (y • pk.2) + msg)` |
| Decrypt(sk, c) | Compute `c.2 - hash sk.1 (sk.2 • c.1)` |

The additive group operation `+` on `M` plays the role of XOR.
Following `elGamalAsymmEnc`, `F` and `G` are explicit type parameters. -/
@[simps!] def hashedElGamal
    (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {G : Type} [AddCommGroup G] [Module F G]
    {HK : Type} [SampleableType HK]
    {M : Type} [AddCommGroup M] [SampleableType M]
    (g : G) (hash : HK → G → M) :
    AsymmEncAlg ProbComp (M := M) (PK := HK × G) (SK := HK × F) (C := G × M) where
  keygen := do
    let hk ← $ᵗ HK
    let sk ← $ᵗ F
    return ((hk, sk • g), (hk, sk))
  encrypt pk msg := do
    let y ← $ᵗ F
    return (y • g, hash pk.1 (y • pk.2) + msg)
  decrypt sk c :=
    return (some (c.2 - hash sk.1 (sk.2 • c.1)))

namespace hashedElGamal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G]
variable {HK : Type} [SampleableType HK]
variable {M : Type} [AddCommGroup M] [SampleableType M]
variable {g : G} {hash : HK → G → M}

/-! ## Correctness -/

theorem correct [DecidableEq M] :
    (hashedElGamal F g hash).PerfectlyCorrect ProbCompRuntime.probComp := by
  have hcomm : ∀ (a b : F), a • (b • g) = b • (a • g) := by
    intro a b; rw [← mul_smul, mul_comm, mul_smul]
  intro msg
  rw [ProbCompRuntime.probComp_evalDist]
  simp [AsymmEncAlg.correctnessExperiment, hashedElGamal, hcomm]

/-! ## DDH Reduction -/

section Security

/-- Construct a DDH adversary from a CPA adversary for hashed ElGamal.
Given DDH challenge `(g, A, B, T)`:
- Set `pk = (hk, A)` where `hk ← $ᵗ HK`
- Let adversary choose messages
- Encrypt using `B` as first ciphertext component, `hash hk T + m_b` as second
- Return adversary's guess -/
def ddhReduction (adv : AsymmEncAlg.IND_CPA_OneTime_Adversary (hashedElGamal F g hash)) :
    DDHAdversary F G :=
  fun _g A B T => do
    let hk ← $ᵗ HK
    let (m₁, m₂, st) ← adv.chooseMessages (hk, A)
    let b ← $ᵗ Bool
    let c : G × M := (B, hash hk T + (if b then m₁ else m₂))
    let b' ← adv.distinguish st c
    return (b == b')

/-! ## Entropy Smoothing Reduction -/

/-- Construct an ES adversary from a CPA adversary for hashed ElGamal.
Given `(hk, v)` where `v` is either `hash hk (z • g)` or random:
- Sample a fresh secret key `sk` and encryption randomness `y`
- Set `pk = sk • g`
- Let adversary choose messages
- Encrypt using `(y • g, v + m_b)` as ciphertext
- Return adversary's guess -/
def esReduction (adv : AsymmEncAlg.IND_CPA_OneTime_Adversary (hashedElGamal F g hash)) :
    HK × M → ProbComp Bool :=
  fun (hk, v) => do
    let sk ← ($ᵗ F)
    let (m₁, m₂, st) ← adv.chooseMessages (hk, sk • g)
    let b ← $ᵗ Bool
    let y ← ($ᵗ F)
    let c : G × M := (y • g, v + (if b then m₁ else m₂))
    let b' ← adv.distinguish st c
    return (b == b')

/-! ## Game-hop lemmas -/

/-- Game 0 = CPA game equals DDH real branch (by construction): both are the canonical program
up to the order of the independent draws, the game drawing the bit first and the reduction
drawing the second exponent second. -/
theorem cpaGame_eq_ddhReal
    (adv : AsymmEncAlg.IND_CPA_OneTime_Adversary (hashedElGamal F g hash)) :
    ProbCompRuntime.probComp.evalDist (AsymmEncAlg.IND_CPA_OneTime_Game
        (encAlg := hashedElGamal F g hash) adv ProbCompRuntime.probComp) =
      𝒟[ddhRealExperiment g (ddhReduction (F := F) (hash := hash) adv)] := by
  let canonical : ProbComp Bool := do
    let hk ← ($ᵗ HK)
    let a ← ($ᵗ F)
    let x ← adv.chooseMessages (hk, a • g)
    let b ← ($ᵗ Bool)
    let y ← ($ᵗ F)
    let b' ← adv.distinguish x.2.2
      (y • g, hash hk (y • (a • g)) + if b then x.1 else x.2.1)
    pure (b == b')
  have hleft :
      ProbCompRuntime.probComp.evalDist (AsymmEncAlg.IND_CPA_OneTime_Game
          (encAlg := hashedElGamal F g hash) adv ProbCompRuntime.probComp) =
        𝒟[canonical] := by
    change 𝒟[($ᵗ Bool) >>= fun b => _] = _
    simp only [hashedElGamal, canonical, bind_pure_comp, map_eq_bind_pure_comp, bind_assoc,
      Function.comp_apply, pure_bind, smul_smul, mul_comm]
    prrw move 0 3
  have hright :
      𝒟[ddhRealExperiment g (ddhReduction (F := F) (hash := hash) adv)] = 𝒟[canonical] := by
    simp only [ddhRealExperiment, ddhReduction, canonical, monad_norm, smul_smul, mul_comm]
    prrw move 1 4
    prrw move 0 1
  exact hleft.trans hright.symm

/-- DDH random branch equals ES real experiment (by construction): both are the canonical
program up to the order of the independent draws. -/
theorem ddhRand_eq_esReal
    (adv : AsymmEncAlg.IND_CPA_OneTime_Adversary (hashedElGamal F g hash)) :
    𝒟[ddhRandomExperiment g (ddhReduction (F := F) (hash := hash) adv)] =
    𝒟[EntropySmoothing.realExperiment F g hash (esReduction (F := F) (g := g) adv)] := by
  let canonical : ProbComp Bool := do
    let hk ← ($ᵗ HK)
    let a ← ($ᵗ F)
    let x ← adv.chooseMessages (hk, a • g)
    let b ← ($ᵗ Bool)
    let z ← ($ᵗ F)
    let y ← ($ᵗ F)
    let b' ← adv.distinguish x.2.2
      (y • g, hash hk (z • g) + if b then x.1 else x.2.1)
    pure (b == b')
  have hleft :
      𝒟[ddhRandomExperiment g (ddhReduction (F := F) (hash := hash) adv)] = 𝒟[canonical] := by
    simp only [ddhRandomExperiment, ddhReduction, canonical, monad_norm]
    prrw move 1 5
    prrw move 1 4
    prrw move 0 1
  have hright :
      𝒟[EntropySmoothing.realExperiment F g hash (esReduction (F := F) (g := g) adv)] =
        𝒟[canonical] := by
    simp only [EntropySmoothing.realExperiment, esReduction, canonical, monad_norm]
    prrw move 1 4
  exact hleft.trans hright.symm

/-- ES ideal experiment: the ciphertext `v + m_b` with uniform `v` is uniform
regardless of `b`, so the game reduces to random guessing.
Uses the same uniform-masking principle as the one-time pad. -/
theorem esIdeal_eq_half
    (adv : AsymmEncAlg.IND_CPA_OneTime_Adversary (hashedElGamal F g hash)) :
    𝒟[EntropySmoothing.idealExperiment (esReduction (F := F) (g := g) adv)] {true} = 1 / 2 := by
  let : MeasurableSpace M := ⊤
  have hM : 𝒟[($ᵗ M : ProbComp M)] = ProbabilityTheory.uniformOn Set.univ :=
    SampleableType.evalDist_uniformSample
  let inner : HK → ProbComp Bool := fun hk => do
    let h ← ($ᵗ M)
    let sk ← ($ᵗ F)
    let (m₁, m₂, st) ← adv.chooseMessages (hk, sk • g)
    let b ← ($ᵗ Bool)
    let y ← ($ᵗ F)
    let b' ← adv.distinguish st (y • g, h + if b then m₁ else m₂)
    pure (decide (b = b'))
  let f : HK → Bool → ProbComp Bool := fun hk b => do
    let sk ← ($ᵗ F)
    let (m₁, m₂, st) ← adv.chooseMessages (hk, sk • g)
    let y ← ($ᵗ F)
    let h ← ($ᵗ M)
    adv.distinguish st (y • g, h + if b then m₁ else m₂)
  have hf : ∀ hk, 𝒟[f hk true] = 𝒟[f hk false] := by
    intro hk
    prrw congr' as ⟨sk, x, y⟩
    rcases x with ⟨m₁, m₂, st⟩
    simpa [add_comm, add_left_comm, add_assoc] using
      ElGamalExamples.evalDist_uniformMaskedCipher_bind_dist_indep ($ᵗ M) hM
        (y • g) m₁ m₂ (adv.distinguish st)
  have hrepr : ∀ hk,
      𝒟[inner hk] =
        𝒟[do
          let b ← ($ᵗ Bool)
          let b' ← f hk b
          pure (decide (b = b'))] := by
    intro hk
    simp only [inner, f, monad_norm]
    prrw move 0 4
    prrw move 2 0
  have hhalf : ∀ hk, 𝒟[inner hk] {true} = 1 / 2 := fun hk => by
    rw [hrepr hk]
    exact ProbComp.evalDist_decide_eq_uniformBool_half (f hk) (hf hk)
  calc
    𝒟[EntropySmoothing.idealExperiment (esReduction (F := F) (g := g) adv)] {true} =
        𝒟[do
          let hk ← ($ᵗ HK)
          inner hk] {true} := by
      simp [EntropySmoothing.idealExperiment, esReduction,
        show ∀ a b : Bool, (a == b) = decide (a = b) from by decide,
        inner]
    _ = 𝒟[do
          let _hk ← ($ᵗ HK)
          ($ᵗ Bool)] {true} :=
      OracleComp.evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton _)
        fun hk _ => by rw [hhalf hk]; simp
    _ = 1 / 2 := by simp

/-! ## Main theorem -/

/-- **Main theorem.** The one-time IND-CPA advantage of hashed ElGamal is at most twice the sum of
the DDH advantage of `ddhReduction` and the entropy-smoothing advantage of `esReduction`, both
constructed from the CPA adversary. The game hops bound the distance of the success probability
from `1 / 2`, and the Boolean bias of the guessing game is twice that distance. -/
theorem hashedElGamal_IND_CPA_bound
    (adv : AsymmEncAlg.IND_CPA_OneTime_Adversary (hashedElGamal F g hash)) :
    AsymmEncAlg.IND_CPA_OneTime_Advantage (hashedElGamal F g hash) ProbCompRuntime.probComp
        adv ≤
      2 * (ddhAdvantage g (ddhReduction (F := F) (hash := hash) adv) +
        EntropySmoothing.advantage F g hash (esReduction (F := F) (g := g) adv)) := by
  rw [AsymmEncAlg.IND_CPA_OneTime_Advantage,
    MeasureTheory.Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure,
    cpaGame_eq_ddhReal (F := F) (g := g) (hash := hash)]
  gcongr
  let real := ddhRealExperiment g (ddhReduction (F := F) (hash := hash) adv)
  let rand := ddhRandomExperiment g (ddhReduction (F := F) (hash := hash) adv)
  let esReal := EntropySmoothing.realExperiment F g hash (esReduction (F := F) (g := g) adv)
  let ideal := EntropySmoothing.idealExperiment (esReduction (F := F) (g := g) adv)
  change ENNReal.absDiff (𝒟[real] {true}) (1 / 2) ≤
    𝒟[real].boolDist 𝒟[rand] + 𝒟[esReal].boolDist 𝒟[ideal]
  have hideal : 𝒟[ideal] {true} = 1 / 2 := esIdeal_eq_half (F := F) (g := g) (hash := hash) adv
  have hrand : 𝒟[rand] {true} = 𝒟[esReal] {true} := by
    rw [ddhRand_eq_esReal (F := F) (g := g) (hash := hash) adv]
  calc
    ENNReal.absDiff (𝒟[real] {true}) (1 / 2) = 𝒟[real].boolDist 𝒟[ideal] := by
      rw [MeasureTheory.Measure.boolDist, hideal]
    _ ≤ 𝒟[real].boolDist 𝒟[rand] + 𝒟[rand].boolDist 𝒟[ideal] :=
      MeasureTheory.Measure.boolDist_triangle _ _ _
    _ = 𝒟[real].boolDist 𝒟[rand] + 𝒟[esReal].boolDist 𝒟[ideal] := by
      simp only [MeasureTheory.Measure.boolDist, hrand]

end Security

end hashedElGamal
