/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio
public import Examples.ElGamal.Basic
public meta import VCVio.ProgramLogic.Tactics
import Mathlib.Util.CountHeartbeats

-- A probe: its proofs are measurements, not library code, so Mathlib's style set is off.
set_option linter.mathlibStandardSet false

/-!
# Probe P5: ElGamal sample reordering with relational tactics

Restates the two private one-time ElGamal bridge lemmas of `Examples/ElGamal/Basic.lean`,
copies the original proofs verbatim (`*_orig`) and re-proves them with `by_equiv` / `rvcgen` /
`rvcstep` (`*_rel`), for a same-file line and heartbeat comparison.
-/

set_option linter.hashCommand false

open OracleSpec OracleComp ENNReal
open OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational
open scoped OracleComp.ProgramLogic

namespace VCVioTest.ProgramLogic.Probes.P5

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]
variable {gen : G}

open elGamalAsymmEnc

local instance : Inhabited G := ⟨0⟩

/-! ## Original proofs, verbatim -/

#count_heartbeats in
lemma game_eq_real_orig
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

#count_heartbeats in
lemma rand_half_orig
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

/-! ## Relational proofs -/

#count_heartbeats in
lemma game_eq_real_rel
    (adv : AsymmEncAlg.IND_CPA_OneTime_Adversary (elGamalAsymmEnc F G gen)) :
    ProbCompRuntime.probComp.evalDist (AsymmEncAlg.IND_CPA_OneTime_Game
        (encAlg := elGamalAsymmEnc F G gen) adv ProbCompRuntime.probComp) =
      𝒟[DiffieHellman.ddhRealExperiment (F := F) gen
          (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)] := by
  have h (sk b : F) (m : G) : m + b • sk • gen = (sk * b) • gen + m := by
    rw [smul_smul, add_comm, mul_comm]
  change 𝒟[($ᵗ Bool) >>= fun b => _] = _
  simp only [DiffieHellman.ddhRealExperiment, IND_CPA_OneTime_DDHReduction, elGamalAsymmEnc,
    oneTimeDDHReductionBody, monad_norm, h]
  by_equiv
  rvcstep swap left
  rvcstep
  rintro sk _ rfl
  rvcstep swap left
  rvcstep swap right
  rvcstep
  rintro cm _ rfl
  rvcstep swap left
  rvcgen

#count_heartbeats in
lemma game_eq_real_vcstep
    (adv : AsymmEncAlg.IND_CPA_OneTime_Adversary (elGamalAsymmEnc F G gen)) :
    ProbCompRuntime.probComp.evalDist (AsymmEncAlg.IND_CPA_OneTime_Game
        (encAlg := elGamalAsymmEnc F G gen) adv ProbCompRuntime.probComp) =
      𝒟[DiffieHellman.ddhRealExperiment (F := F) gen
          (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)] := by
  have h (sk b : F) (m : G) : m + b • sk • gen = (sk * b) • gen + m := by
    rw [smul_smul, add_comm, mul_comm]
  change 𝒟[($ᵗ Bool) >>= fun b => _] = _
  simp only [DiffieHellman.ddhRealExperiment, IND_CPA_OneTime_DDHReduction, elGamalAsymmEnc,
    oneTimeDDHReductionBody, monad_norm, h]
  vcstep rw
  vcstep rw congr' as ⟨sk⟩
  vcstep rw
  symm
  vcstep rw
  symm
  vcstep rw congr' as ⟨cm⟩
  vcstep rw

#count_heartbeats in
lemma rand_half_rel
    (hg : Function.Bijective (· • gen : F → G))
    (adv : AsymmEncAlg.IND_CPA_OneTime_Adversary (elGamalAsymmEnc F G gen)) :
    𝒟[DiffieHellman.ddhRandomExperiment (F := F) gen
      (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)] {true} = 1 / 2 := by
  have key : 𝒟[DiffieHellman.ddhRandomExperiment (F := F) gen
      (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)] =
      𝒟[do
        let bit ← ($ᵗ Bool)
        let bit' ← (do
          let a ← ($ᵗ F)
          let b ← ($ᵗ F)
          let cm ← adv.chooseMessages (a • gen)
          let c ← ($ᵗ F)
          adv.distinguish cm.2.2 (b • gen, c • gen))
        return decide (bit = bit')] := by
    simp only [DiffieHellman.ddhRandomExperiment, IND_CPA_OneTime_DDHReduction,
      oneTimeDDHReductionBody, monad_norm, Bool.beq_eq_decide_eq]
    by_equiv
    rvcstep swap right
    rvcstep
    rintro a _ rfl
    rvcstep swap right
    rvcstep
    rintro b _ rfl
    rvcstep swap right
    rvcstep swap left
    rvcstep
    rintro cm _ rfl
    rvcstep swap left
    rvcstep using EqRel Bool
    rintro bit _ rfl
    rvcstep using ((· + (Equiv.ofBijective _ hg).symm (if bit then cm.1 else cm.2.1)) : F → F)
    · have hinv (m : G) : (Equiv.ofBijective _ hg).symm m • gen = m :=
        Equiv.ofBijective_apply_symm_apply _ hg m
      simp only [add_smul, hinv]
      exact relTriple_refl _
    · exact (Equiv.addRight _).bijective
  rw [key]
  exact ProbComp.evalDist_decide_eq_uniformBool_half _ rfl

/-! ## Tactic defect found by the probe

`rvcstep` on a synchronized bind whose continuations end in a `<$>` whose function mentions an
outer bound variable crashes with a loose bound variable, instead of stepping or failing cleanly.
In `rand_half_rel` the same defect surfaces as `unknown free variable` for plain `rvcstep` at the
`$ᵗ Bool` step and for the closing `rvcgen`; the proof works around it with
`rvcstep using EqRel Bool` and `exact relTriple_refl _`. -/

/-- error: unexpected bound variable #2 -/
#guard_msgs in
example (f g : Bool → F → ProbComp Bool) :
    ⟪do let b ← $ᵗ Bool; let a ← $ᵗ F; (fun x => decide (b = x)) <$> f b a
    ~ do let b ← $ᵗ Bool; let a ← $ᵗ F; (fun x => decide (b = x)) <$> g b a | EqRel Bool⟫ := by
  rvcstep

end VCVioTest.ProgramLogic.Probes.P5
