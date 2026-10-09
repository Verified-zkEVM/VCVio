/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import Examples.ElGamal.Common
public import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA
public import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure
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
  rw [ProbCompRuntime.probComp_evalDist]
  simp [AsymmEncAlg.correctnessExperiment, elGamalAsymmEnc, hcancel]

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
  simp only [DiffieHellman.ddhRealExperiment, IND_CPA_OneTime_DDHReduction, elGamalAsymmEnc]
  simp only [bind_pure_comp, bind_map_left]
  simp only [map_eq_pure_bind]
  -- Step 1: swap $ᵗ Bool past $ᵗ F in LHS
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool) ($ᵗ F)]
  -- Now LHS starts with $ᵗ F. Use congruence under $ᵗ F.
  refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun sk _ => ?_
  -- Step 2: swap $ᵗ Bool past chooseMessages in LHS
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool) (adv.chooseMessages (sk • gen))]
  -- Step 3: swap chooseMessages past $ᵗ F in RHS
  conv_rhs => rw [OracleComp.evalDist_bind_bind_swap ($ᵗ F) (adv.chooseMessages (sk • gen))]
  -- Now both start with chooseMessages. Congruence under it.
  refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun cm _ => ?_
  -- Step 4: swap $ᵗ Bool past $ᵗ F in LHS
  rw [OracleComp.evalDist_bind_bind_swap ($ᵗ Bool) ($ᵗ F)]
  -- Now both: $ᵗ F >>= fun r => $ᵗ Bool >>= fun bit => ...
  refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun r _ => ?_
  refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun bit _ => ?_
  -- The ciphertext expressions agree:
  -- LHS: (r•gen, (if bit then cm.1 else cm.2.1) + r • (sk • gen))
  -- RHS: (r•gen, (sk * r)•gen + (if bit then cm.1 else cm.2.1))
  congr 3
  rw [smul_smul, add_comm, mul_comm]

/-- Random-branch half lemma for the one-time ElGamal reduction. Under bijectivity of `(· • gen)`,
the DDH-random branch gives a uniform additive mask independent of the challenge bit, so the
adversary can do no better than random guessing. -/
private lemma IND_CPA_OneTime_DDHReduction_rand_half
    (hg : Function.Bijective (· • gen : F → G))
    (adv : AsymmEncAlg.IND_CPA_OneTime_Adversary (elGamalAsymmEnc F G gen)) :
    𝒟[DiffieHellman.ddhRandomExperiment (F := F) gen
      (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)] {true} = 1 / 2 := by
  let : MeasurableSpace F := ⊤
  let : MeasurableSpace G := ⊤
  have hF : 𝒟[($ᵗ F : ProbComp F)] = ProbabilityTheory.uniformOn Set.univ :=
    SampleableType.evalDist_uniformSample
  have hG : 𝒟[($ᵗ G : ProbComp G)] = ProbabilityTheory.uniformOn Set.univ :=
    SampleableType.evalDist_uniformSample
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
  have hf : ∀ pk, 𝒟[f pk true] = 𝒟[f pk false] := by
    intro pk
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun head _ => ?_
    refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun x _ => ?_
    rcases x with ⟨m₁, m₂, st⟩
    simpa [add_comm] using
      ElGamalExamples.evalDist_uniformMaskedCipher_bind_dist_indep ($ᵗ G) hG
        head m₁ m₂ (adv.distinguish st)
  have hrepr : ∀ pk, 𝒟[inner pk] {true} =
      𝒟[do
        let bit ← ($ᵗ Bool)
        let bit' ← f pk bit
        pure (decide (bit = bit'))] {true} := by
    intro pk
    trans 𝒟[do
      let head ← ($ᵗ G)
      let x ← adv.chooseMessages pk
      let bit ← ($ᵗ Bool)
      let mask ← ($ᵗ G)
      let bit' ← adv.distinguish x.2.2 (head, mask + if bit then x.1 else x.2.1)
      pure (decide (bit = bit'))] {true}
    · congr 1
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun head _ => ?_
      simpa [inner, monad_norm] using
        (OracleComp.evalDist_bind_bind_swap
          ($ᵗ G)
          (do
            let x ← adv.chooseMessages pk
            let bit ← ($ᵗ Bool)
            pure (x, bit))
          (fun mask (y : (G × G × adv.State) × Bool) => do
            let bit' ← adv.distinguish y.1.2.2 (head, mask + if y.2 then y.1.1 else y.1.2.1)
            pure (decide (y.2 = bit'))))
    · congr 1
      simpa [f, monad_norm] using
        (OracleComp.evalDist_bind_bind_swap
          (do
            let head ← ($ᵗ G)
            let x ← adv.chooseMessages pk
            pure (head, x))
          ($ᵗ Bool)
          (fun (y : G × G × G × adv.State) bit => do
            let mask ← ($ᵗ G)
            let bit' ← adv.distinguish y.2.2.2 (y.1, mask + if bit then y.2.1 else y.2.2.1)
            pure (decide (bit = bit'))))
  have hhalf : ∀ pk, 𝒟[inner pk] {true} = 1 / 2 := fun pk =>
    (hrepr pk).trans (ProbComp.evalDist_decide_eq_uniformBool_half (f pk) (hf pk))
  calc
    𝒟[DiffieHellman.ddhRandomExperiment (F := F) gen
      (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)] {true} =
        𝒟[do
          let pk ← ($ᵗ G)
          inner pk] {true} := by
      trans 𝒟[do
        let pk ← ($ᵗ G)
        let b ← ($ᵗ F)
        let c ← ($ᵗ F)
        let (m₁, m₂, st) ← adv.chooseMessages pk
        let bit ← ($ᵗ Bool)
        let bit' ← adv.distinguish st (b • gen, c • gen + if bit then m₁ else m₂)
        pure (decide (bit = bit'))] {true}
      · congr 1
        simpa [DiffieHellman.ddhRandomExperiment, IND_CPA_OneTime_DDHReduction,
          oneTimeDDHReductionBody, monad_norm,
          show ∀ a b : Bool, (a == b) = decide (a = b) from by decide] using
          evalDist_bind_bijective_uniform_cross ($ᵗ F) ($ᵗ G) hF hG (· • gen) hg
            (fun pk => do
              let b ← ($ᵗ F)
              let c ← ($ᵗ F)
              let (m₁, m₂, st) ← adv.chooseMessages pk
              let bit ← ($ᵗ Bool)
              let bit' ← adv.distinguish st (b • gen, c • gen + if bit then m₁ else m₂)
              pure (decide (bit = bit')))
      · congr 1
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun pk _ => ?_
        trans 𝒟[do
          let head ← ($ᵗ G)
          let c ← ($ᵗ F)
          let (m₁, m₂, st) ← adv.chooseMessages pk
          let bit ← ($ᵗ Bool)
          let bit' ← adv.distinguish st (head, c • gen + if bit then m₁ else m₂)
          pure (decide (bit = bit'))]
        · simpa [monad_norm] using
            evalDist_bind_bijective_uniform_cross ($ᵗ F) ($ᵗ G) hF hG (· • gen) hg
              (fun head => do
                let c ← ($ᵗ F)
                let (m₁, m₂, st) ← adv.chooseMessages pk
                let bit ← ($ᵗ Bool)
                let bit' ← adv.distinguish st (head, c • gen + if bit then m₁ else m₂)
                pure (decide (bit = bit')))
        · refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun head _ => ?_
          simpa [inner, monad_norm] using
            evalDist_bind_bijective_uniform_cross ($ᵗ F) ($ᵗ G) hF hG (· • gen) hg
              (fun mask => do
                let (m₁, m₂, st) ← adv.chooseMessages pk
                let bit ← ($ᵗ Bool)
                let bit' ← adv.distinguish st (head, mask + if bit then m₁ else m₂)
                pure (decide (bit = bit')))
    _ = 𝒟[do
          let _pk ← ($ᵗ G)
          ($ᵗ Bool)] {true} :=
      OracleComp.evalDist_bind_apply_congr_of_support _ _ _ (measurableSet_singleton _)
        fun pk _ => by rw [hhalf pk]; simp
    _ = 1 / 2 := by simp

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
