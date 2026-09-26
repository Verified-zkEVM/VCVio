/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import Examples.ElGamal.Common
public import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA
public import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.OracleComp.EvalDist.UniformCompatibility
import VCVio.OracleComp.Constructions.SampleableType.MeasureCompatibility
import ToMathlib.Probability.UniformOn

/-!
# ElGamal Encryption: IND-CPA via the generic one-time lift

This file defines ElGamal encryption over a module `Module F G` and treats the security proof as
a one-time DDH client of the generic IND-CPA lift in `AsymmEncAlg`.

## Mathematical notation

We use additive / EC-style notation throughout:

| Textbook (multiplicative) | This file (additive)             |
|---------------------------|----------------------------------|
| `g^a`                     | `a • gen`                        |
| `g^a · g^b = g^{a+b}`     | `a • gen + b • gen`              |
| `(g^a)^b = g^{ab}`        | `b • (a • gen) = (b * a) • gen` |
| `m · g^{ab}`              | `m + (a * b) • gen`              |

Here `F` is the scalar field (for example `ZMod p`), `G` is the additive group of ciphertext
payloads (for example elliptic-curve points), and `gen : G` is a fixed public generator.

## Proof structure

1. ElGamal definition and correctness.
2. One-time DDH bridge:
   `IND_CPA_OneTime_DDHReduction`,
   `IND_CPA_OneTime_Game_eq_ddhRealExperiment`,
   `IND_CPA_OneTime_DDHReduction_rand_half`, and
   `elGamal_oneTime_advantage_eq_two_mul_ddhAdvantage`.
3. Final theorem:
   `elGamal_IND_CPA_le_q_mul_ddh` is a direct instantiation of
   `AsymmEncAlg.IND_CPA_Advantage_le_mul_of_oneTime_bound` with one-time loss `2 * ε`.
-/

@[expose] public section

open OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]

/-- ElGamal encryption over a module `Module F G` with generator `gen : G`.

Key generation samples a scalar `sk ← $ᵗ F` and returns `(sk • gen, sk)`.
Encryption of `msg` under public key `pk` samples `r ← $ᵗ F` and returns
`(r • gen, msg + r • pk)`. Decryption recovers `msg` as `c₂ - sk • c₁`. -/
@[simps!] def elGamalAsymmEnc (F G : Type) [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] [AddCommGroup G] [Module F G] [SampleableType G]
    (gen : G) : AsymmEncAlg ProbComp
    (M := G) (PK := G) (SK := F) (C := G × G) where
  keygen := do
    let sk ← $ᵗ F
    return (sk • gen, sk)
  encrypt := fun pk msg => do
    let r ← $ᵗ F
    return (r • gen, msg + r • pk)
  decrypt := fun sk (c₁, c₂) =>
    return (some (c₂ - sk • c₁))

namespace elGamalAsymmEnc

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]
variable {gen : G}

/-- The shared one-time DDH reduction body, parameterized by its three effectful operations.

The closed probabilistic reduction, the open adversary interface, the profiled reduction, and the
fully syntactic oracle program all instantiate this definition. -/
abbrev oneTimeDDHReductionBody {m : Type → Type} [Monad m] {State : Type}
    (chooseMessages : m (G × G × State)) (coin : m Bool)
    (distinguish : State → G × G → m Bool) (B T : G) : m Bool :=
  chooseMessages >>= fun ⟨m₁, m₂, state⟩ ↦
    coin >>= fun bit ↦ do
      let bit' ← distinguish state (B, T + if bit then m₁ else m₂)
      pure (bit == bit')

/-- ElGamal decryption perfectly inverts encryption: `Dec(sk, Enc(pk, msg)) = msg`. -/
theorem correct [DecidableEq G] :
    (elGamalAsymmEnc F G gen).PerfectlyCorrect ProbCompRuntime.probComp := by
  have hcancel : ∀ (msg : G) (sk r : F),
      msg + r • (sk • gen) - sk • (r • gen) = msg := by
    intro msg sk r
    have : r • (sk • gen) = sk • (r • gen) := by
      rw [← mul_smul, ← mul_smul, mul_comm]
    rw [this, add_sub_cancel_right]
  simp only [AsymmEncAlg.PerfectlyCorrect]
  intro msg
  rw [ProbCompRuntime.probComp_evalDist, evalDist_apply_singleton]
  simp [AsymmEncAlg.correctnessExperiment, elGamalAsymmEnc, hcancel,
    probOutput_bind_const, probOutput_map_const]

section IND_CPA

local instance : Inhabited G := ⟨0⟩

/-- One-time DDH reduction for ElGamal. On input `(gen, A, B, T)`, use `A` as the ElGamal public
key, form the challenge ciphertext `(B, T + m_b)`, and return whether the one-time adversary
guessed the hidden bit `b`. -/
def IND_CPA_OneTime_DDHReduction
    (adv : AsymmEncAlg.IND_CPA_OneTime_Adversary (elGamalAsymmEnc F G gen)) :
    DiffieHellman.DDHAdversary F G := fun _ A B T =>
  oneTimeDDHReductionBody (adv.chooseMessages A) ($ᵗ Bool) adv.distinguish B T

/-- Real-branch identification for the one-time ElGamal reduction. After unfolding
`AsymmEncAlg.IND_CPA_OneTime_Game`, `elGamalAsymmEnc`, `DiffieHellman.ddhRealExperiment`, and
`IND_CPA_OneTime_DDHReduction`, both sides normalize to the same sample space. -/
private lemma IND_CPA_OneTime_Game_eq_ddhRealExperiment
    (adv : AsymmEncAlg.IND_CPA_OneTime_Adversary (elGamalAsymmEnc F G gen)) :
    ProbCompRuntime.probComp.evalDist (AsymmEncAlg.IND_CPA_OneTime_Game
        (encAlg := elGamalAsymmEnc F G gen) adv ProbCompRuntime.probComp) =
      𝒟[DiffieHellman.ddhRealExperiment (F := F) gen
          (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)] := by
  change 𝒟[($ᵗ Bool) >>= fun b => _] = _
  refine evalDist_eq_of_evalSPMF_eq _ _ ?_
  simp only [DiffieHellman.ddhRealExperiment, IND_CPA_OneTime_DDHReduction, elGamalAsymmEnc]
  ext z
  change Pr[= z | _] = Pr[= z | _]
  simp only [bind_pure_comp, bind_map_left]
  simp only [map_eq_pure_bind]
  -- Step 1: swap $ᵗ Bool past $ᵗ F in LHS
  rw [probOutput_bind_bind_swap ($ᵗ Bool) ($ᵗ F)]
  -- Now LHS starts with $ᵗ F. Use congr under $ᵗ F.
  refine probOutput_bind_congr' ($ᵗ F) z (fun sk => ?_)
  -- Step 2: swap $ᵗ Bool past chooseMessages in LHS
  rw [probOutput_bind_bind_swap ($ᵗ Bool) (adv.chooseMessages (sk • gen))]
  -- Step 3: swap chooseMessages past $ᵗ F in RHS
  conv_rhs => rw [probOutput_bind_bind_swap ($ᵗ F) (adv.chooseMessages (sk • gen))]
  -- Now both start with chooseMessages. Congr under it.
  refine probOutput_bind_congr' (adv.chooseMessages (sk • gen)) z (fun cm => ?_)
  -- Step 4: swap $ᵗ Bool past $ᵗ F in LHS
  rw [probOutput_bind_bind_swap ($ᵗ Bool) ($ᵗ F)]
  -- Now both: $ᵗ F >>= fun r => $ᵗ Bool >>= fun bit => ...
  refine probOutput_bind_congr' ($ᵗ F) z (fun r => ?_)
  refine probOutput_bind_congr' ($ᵗ Bool) z (fun bit => ?_)
  -- Now need to show the ciphertext expressions match
  -- LHS: (r•gen, (if bit then cm.1 else cm.2.1) + r • (sk • gen))
  -- RHS: (r•gen, (sk * r)•gen + (if bit then cm.1 else cm.2.1))
  congr 2
  rw [smul_smul, add_comm, mul_comm]

/-- Random-branch half lemma for the one-time ElGamal reduction. Under bijectivity of `(· • gen)`,
the DDH-random branch gives a uniform additive mask independent of the challenge bit, so the
adversary can do no better than random guessing. -/
private lemma IND_CPA_OneTime_DDHReduction_rand_half
    (hg : Function.Bijective (· • gen : F → G))
    (adv : AsymmEncAlg.IND_CPA_OneTime_Adversary (elGamalAsymmEnc F G gen)) :
    Pr[= true | DiffieHellman.ddhRandomExperiment (F := F) gen
      (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)] = 1 / 2 := by
  let inner : G → ProbComp Bool := fun pk => do
    let head ← ($ᵗ G)
    let mask ← ($ᵗ G)
    let (m₁, m₂, st) ← adv.chooseMessages pk
    let bit ← ($ᵗ Bool)
    let bit' ← adv.distinguish st (head, mask + if bit then m₁ else m₂)
    pure (decide (bit = bit'))
  let f : G → Bool → ProbComp Bool := fun pk bit => do
    let head ← ($ᵗ G)
    let (m₁, m₂, st) ← adv.chooseMessages pk
    let mask ← ($ᵗ G)
    adv.distinguish st (head, mask + if bit then m₁ else m₂)
  have hf : ∀ pk, 𝒮[f pk true] = 𝒮[f pk false] := by
    intro pk
    unfold f
    rw [evalSPMF_bind, evalSPMF_bind]
    congr 1
    funext head
    rw [evalSPMF_bind, evalSPMF_bind]
    congr 1
    funext x
    rcases x with ⟨m₁, m₂, st⟩
    simpa [add_comm] using
      ElGamalExamples.uniformMaskedCipher_bind_dist_indep
        (head := head) (m₁ := m₁) (m₂ := m₂) (cont := adv.distinguish st)
  have hrepr : ∀ pk, Pr[= true | inner pk] =
      Pr[= true | do
        let bit ← ($ᵗ Bool)
        let bit' ← f pk bit
        pure (decide (bit = bit'))] := by
    intro pk
    trans Pr[= true | do
      let head ← ($ᵗ G)
      let x ← adv.chooseMessages pk
      let bit ← ($ᵗ Bool)
      let mask ← ($ᵗ G)
      let bit' ← adv.distinguish x.2.2 (head, mask + if bit then x.1 else x.2.1)
      pure (decide (bit = bit'))]
    · refine probOutput_bind_congr' ($ᵗ G) true ?_
      intro head
      simpa [inner, monad_norm] using
        (probOutput_bind_bind_swap
          ($ᵗ G)
          (do
            let x ← adv.chooseMessages pk
            let bit ← ($ᵗ Bool)
            pure (x, bit))
          (fun mask ⟨x, bit⟩ => do
            let bit' ← adv.distinguish x.2.2 (head, mask + if bit then x.1 else x.2.1)
            pure (decide (bit = bit')))
          true)
    · simpa [f, monad_norm] using
        (probOutput_bind_bind_swap
          (do
            let head ← ($ᵗ G)
            let x ← adv.chooseMessages pk
            pure (head, x))
          ($ᵗ Bool)
          (fun ⟨head, x⟩ bit => do
            let mask ← ($ᵗ G)
            let bit' ← adv.distinguish x.2.2 (head, mask + if bit then x.1 else x.2.1)
            pure (decide (bit = bit')))
          true)
  have hhalf : ∀ pk, Pr[= true | inner pk] = 1 / 2 := by
    intro pk
    rw [hrepr pk]
    exact probOutput_decide_eq_uniformBool_half (f pk) (hf pk)
  calc
    Pr[= true | DiffieHellman.ddhRandomExperiment (F := F) gen
      (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)] =
        Pr[= true | do
          let pk ← ($ᵗ G)
          inner pk] := by
      trans Pr[= true | do
        let pk ← ($ᵗ G)
        let b ← ($ᵗ F)
        let c ← ($ᵗ F)
        let (m₁, m₂, st) ← adv.chooseMessages pk
        let bit ← ($ᵗ Bool)
        let bit' ← adv.distinguish st (b • gen, c • gen + if bit then m₁ else m₂)
        pure (decide (bit = bit'))]
      · simpa [DiffieHellman.ddhRandomExperiment, IND_CPA_OneTime_DDHReduction,
          oneTimeDDHReductionBody, monad_norm,
          show ∀ a b : Bool, (a == b) = decide (a = b) from by decide] using
          (probOutput_bind_bijective_uniform_cross
            (α := F) (β := G) (f := (· • gen)) hg
            (g := fun pk => do
              let b ← ($ᵗ F)
              let c ← ($ᵗ F)
              let (m₁, m₂, st) ← adv.chooseMessages pk
              let bit ← ($ᵗ Bool)
              let bit' ← adv.distinguish st (b • gen, c • gen + if bit then m₁ else m₂)
              pure (decide (bit = bit')))
            true)
      · refine probOutput_bind_congr' ($ᵗ G) true ?_
        intro pk
        trans Pr[= true | do
          let head ← ($ᵗ G)
          let c ← ($ᵗ F)
          let (m₁, m₂, st) ← adv.chooseMessages pk
          let bit ← ($ᵗ Bool)
          let bit' ← adv.distinguish st (head, c • gen + if bit then m₁ else m₂)
          pure (decide (bit = bit'))]
        · simpa [monad_norm] using
            (probOutput_bind_bijective_uniform_cross
              (α := F) (β := G) (f := (· • gen)) hg
              (g := fun head => do
                let c ← ($ᵗ F)
                let (m₁, m₂, st) ← adv.chooseMessages pk
                let bit ← ($ᵗ Bool)
                let bit' ← adv.distinguish st (head, c • gen + if bit then m₁ else m₂)
                pure (decide (bit = bit')))
              true)
        · refine probOutput_bind_congr' ($ᵗ G) true ?_
          intro head
          simpa [inner, monad_norm] using
            (probOutput_bind_bijective_uniform_cross
              (α := F) (β := G) (f := (· • gen)) hg
              (g := fun mask => do
                let (m₁, m₂, st) ← adv.chooseMessages pk
                let bit ← ($ᵗ Bool)
                let bit' ← adv.distinguish st (head, mask + if bit then m₁ else m₂)
                pure (decide (bit = bit')))
              true)
    _ = Pr[= true | do
          let pk ← ($ᵗ G)
          ($ᵗ Bool)] :=
      probOutput_bind_congr' ($ᵗ G) true (fun pk => by
        simpa [probOutput_uniformSample] using hhalf pk)
    _ = 1 / 2 := by
      let : MeasurableSpace G := ⊤
      rw [← evalDist_apply_singleton, OracleComp.evalDist_bind_const, evalDist_uniformSample,
        ProbabilityTheory.uniformOn_univ_apply_singleton]
      norm_num

/-- The one-time IND-CPA advantage of ElGamal is exactly twice the DDH advantage of the reduction
above. The reduction's real branch is the one-time game, whose bias is twice the distance of its
success probability from `1 / 2`, and its random branch succeeds with probability `1 / 2`. -/
theorem elGamal_oneTime_advantage_eq_two_mul_ddhAdvantage
    (hg : Function.Bijective (· • gen : F → G))
    (adv : AsymmEncAlg.IND_CPA_OneTime_Adversary (elGamalAsymmEnc F G gen)) :
    AsymmEncAlg.IND_CPA_OneTime_Advantage (elGamalAsymmEnc F G gen) ProbCompRuntime.probComp adv =
      2 * DiffieHellman.ddhAdvantage gen
        (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv) := by
  rw [AsymmEncAlg.IND_CPA_OneTime_Advantage, IND_CPA_OneTime_Game_eq_ddhRealExperiment,
    MeasureTheory.Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure,
    DiffieHellman.ddhAdvantage, MeasureTheory.Measure.boolDist]
  simp only [evalDist_apply_singleton]
  rw [IND_CPA_OneTime_DDHReduction_rand_half hg adv]

/-- **Main theorem.** If an adversary makes at most `q` LR queries and every extracted one-time
ElGamal DDH reduction has DDH advantage at most `ε`, then ElGamal has IND-CPA advantage at most
`q * (2 * ε)`. -/
theorem elGamal_IND_CPA_le_q_mul_ddh [DecidableEq G]
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : (elGamalAsymmEnc F G gen).IND_CPA_Adversary)
    (q : ℕ) (ε : ℝ≥0∞)
    (hq : adversary.MakesAtMostQueries q)
    (hddh : ∀ adv : AsymmEncAlg.IND_CPA_OneTime_Adversary (elGamalAsymmEnc F G gen),
      DiffieHellman.ddhAdvantage gen
        (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv) ≤ ε) :
    (elGamalAsymmEnc F G gen).IND_CPA_Advantage adversary ≤ q * (2 * ε) := by
  refine AsymmEncAlg.IND_CPA_Advantage_le_mul_of_oneTime_bound
    (encAlg' := elGamalAsymmEnc F G gen) adversary q (2 * ε) hq fun adv => ?_
  rw [elGamal_oneTime_advantage_eq_two_mul_ddhAdvantage hg adv]
  gcongr
  exact hddh adv

end IND_CPA

end elGamalAsymmEnc
