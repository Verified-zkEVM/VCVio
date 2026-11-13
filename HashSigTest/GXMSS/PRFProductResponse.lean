/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.PRFDerivedUnforgeability
public import HashSig.GXMSS.Security.Interval.PRFDerivedFullRange
public import HashSig.GXMSS.Security.Interval.Reductions.PRFDerivedFullRangeBounds

/-!
# Product responses and actual PRF key sampling

Finite product responses supply the four projection laws. A fixed Boolean key generator exercises
security and full-range transport without a uniform-key premise.
-/

public section

namespace GXMSS.PRFProductResponseTest

open Encoding IntervalMerkle OracleComp OracleSpec ENNReal

/-- Product response for one seed, one chain start, one retry and one filler projection. -/
abbrev Response := Unit × Bool × Bool × Bool

/-- Uniform pairs have the canonical first-coordinate marginal. -/
private theorem product_fst (A B : Type) [SampleableType A] [SampleableType B] :
    (Prod.fst <$> ($ᵗ (A × B))) =ᵈ ($ᵗ A) := by
  apply evalDistEq_iff_evalDist_eq.mpr
  let : MeasurableSpace A := ⊤
  simpa using SampleableType.evalDist_uniformSample_prod_bind_fst
    (β := B) (pure : A → ProbComp A)

/-- Uniform pairs have the canonical second-coordinate marginal. -/
private theorem product_snd (A B : Type) [SampleableType A] [SampleableType B] :
    (Prod.snd <$> ($ᵗ (A × B))) =ᵈ ($ᵗ B) := by
  apply evalDistEq_iff_evalDist_eq.mpr
  let : MeasurableSpace B := ⊤
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp [map_bind]

/-- The interval interpretation extends its complete-tree projections. -/
@[expose] def projection : Interval.PRFDerived.Interpretation Unit Bool Bool Response where
  publicParameter := Prod.fst
  chainStart := fun response => response.2.1
  retryRandomizer := fun response => response.2.2.1
  fillerDigest := fun response => response.2.2.2

private theorem start_marginal :
    (projection.chainStart <$> ($ᵗ Response)) =ᵈ ($ᵗ Bool) := by
  calc
    _ =ᵈ (Prod.fst <$> ($ᵗ (Bool × Bool × Bool))) := by
      simpa only [Functor.map_map, Function.comp_def, projection] using
        (product_snd Unit (Bool × Bool × Bool)).map Prod.fst
    _ =ᵈ ($ᵗ Bool) := product_fst Bool (Bool × Bool)

private theorem retry_marginal :
    (projection.retryRandomizer <$> ($ᵗ Response)) =ᵈ ($ᵗ Bool) := by
  calc
    _ =ᵈ ((fun response : Bool × Bool × Bool => response.2.1) <$>
        ($ᵗ (Bool × Bool × Bool))) := by
      simpa only [Functor.map_map, Function.comp_def, projection] using
        (product_snd Unit (Bool × Bool × Bool)).map (fun response => response.2.1)
    _ =ᵈ (Prod.fst <$> ($ᵗ (Bool × Bool))) := by
      simpa only [Functor.map_map, Function.comp_def] using
        (product_snd Bool (Bool × Bool)).map Prod.fst
    _ =ᵈ ($ᵗ Bool) := product_fst Bool Bool

private theorem filler_marginal :
    (projection.fillerDigest <$> ($ᵗ Response)) =ᵈ ($ᵗ Bool) := by
  calc
    _ =ᵈ ((fun response : Bool × Bool × Bool => response.2.2) <$>
        ($ᵗ (Bool × Bool × Bool))) := by
      simpa only [Functor.map_map, Function.comp_def, projection] using
        (product_snd Unit (Bool × Bool × Bool)).map (fun response => response.2.2)
    _ =ᵈ (Prod.snd <$> ($ᵗ (Bool × Bool))) := by
      simpa only [Functor.map_map, Function.comp_def] using
        (product_snd Bool (Bool × Bool)).map Prod.snd
    _ =ᵈ ($ᵗ Bool) := product_snd Bool Bool

/-- A finite hash interface with a lossless unit public seed. -/
@[expose] def hash : HashInstance Unit ((Fin 8 × Fin 2 × Fin 1) ⊕ (Fin 4 × Fin 8))
    (Bool ⊕ ((Bool × Bool) ⊕ (Fin 2 → Bool))) Bool 3 1 2 where
  thf := ⟨pure (), fun _ _ input => match input with | .inl x => !x | .inr _ => false⟩
  digestInput := ⟨Sum.inl, Sum.inl_injective⟩
  pairInput := ⟨fun pair => Sum.inr (Sum.inl pair),
    Function.Injective.comp Sum.inr_injective Sum.inl_injective⟩
  vectorInput := ⟨fun vector => Sum.inr (Sum.inr vector),
    Function.Injective.comp Sum.inr_injective Sum.inr_injective⟩
  chainTweak := ⟨Sum.inl, Sum.inl_injective⟩
  treeTweak := ⟨Sum.inr, Sum.inr_injective⟩
  chain_ne_tree := fun c t => Sum.inl_ne_inr (a := c) (b := t)

/-- All four projection laws are proved for the canonical product sampler. -/
theorem projection_laws :
    Interval.PRFDerived.Unforgeability.PublicSeedSamplingLaw hash projection ∧
    Interval.PRFDerived.Unforgeability.ChainStartSamplingLaw projection ∧
    Interval.PRFDerived.Unforgeability.RetrySamplingLaw projection ∧
    Interval.PRFDerived.Unforgeability.FillerSamplingLaw projection := by
  refine ⟨?_, start_marginal.evalDist_eq, retry_marginal.evalDist_eq,
    filler_marginal.evalDist_eq⟩
  change 𝒟[Prod.fst <$> ($ᵗ Response)] = 𝒟[pure ()]
  have h := (product_fst Unit (Bool × Bool × Bool)).evalDist_eq
  apply h.trans
  apply MeasureTheory.Measure.ext_of_singleton
  intro x
  cases x
  simp [SampleableType.evalDist_uniformSample_singleton]

/-- The two length-two binary words of digit sum one form the entire code. -/
@[expose] def enc : IncomparableEncoding Unit Unit Bool (Fin 8) 2 2 where
  code := {word | ∑ i, (word i).val = 1}
  incomparable := by
    intro x hx y hy hne
    exact incomparableWords_of_sum_eq hne (hx.trans hy.symm)
  encode := fun _ _ r _ =>
    some ⟨(if r then ![0, 1] else ![1, 0]), by cases r <;> decide⟩

private theorem two_codewords : ∃ x y : Codeword 2 2,
    x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y := by
  exact ⟨![0, 1], ![1, 0], by simp [enc, Fin.sum_univ_two],
    by simp [enc, Fin.sum_univ_two], by decide⟩

/-- A fixed key generator is accepted without a uniform-key hypothesis. -/
@[expose] def prf :
    PRFScheme Bool (Interval.PRFDerived.Query Unit Unit 3 2) Response where
  keygen := pure false
  eval key _ := ((), key, key, key)

/-- Request an active signature and alter its returned randomizer before forging. -/
@[expose] def adversary : SyncSignatureUnforgeability.Adversary unifSpec
    (PublicKey Unit Bool) (Fin 8) Unit (Signature Bool Bool 3 2) where
  forge _ := do
    let answer ← (unifSpec + SyncSignatureUnforgeability.signingSpec (Fin 8) Unit
      (Signature Bool Bool 3 2)).query (.inr (3, ()))
    let sig := answer.getD ⟨false, fun _ => false, fun _ => false⟩
    return (3, (), {sig with randomizer := !sig.randomizer})

private theorem one_signing_request :
    Unforgeability.SigningQueryBound (h := 3) (v := 2) 1 adversary := by
  intro pk
  dsimp [adversary, SyncSignatureUnforgeability.Forgery]
  rw [isQueryBoundP_query_bind_iff]
  constructor
  · simp
  · intro answer
    exact isQueryBoundP_pure _ _ _

noncomputable section

local instance : DecidableEq (Interval.PRFDerived.Query Unit Unit 3 2) := Classical.decEq _
local instance : DecidableEq (PRFDerived.Query Unit Unit 3 2) := Classical.decEq _

/-- An interior interval security application supplies every projection law from the product. -/
theorem interval_security :
    let I : Interval 3 := ⟨3, 4, by decide⟩
    SyncSignatureUnforgeability.strongAdvantage
      (Interval.PRFDerived.scheme prf.keygen hash enc prf.eval projection 1 I)
      ProbCompRuntime.probComp adversary ≤
      Interval.PRFDerived.Unforgeability.strongUnforgeabilityBound hash enc prf projection 1 1 I
        (by decide) (by decide) adversary := by
  obtain ⟨hseed, hstart, hretry, hfiller⟩ := projection_laws
  exact Interval.PRFDerived.Unforgeability.strong_unforgeability_reduction_bound
    hash enc prf projection 1 1 ⟨3, 4, by decide⟩ (by decide) (by decide) two_codewords
    adversary one_signing_request hseed hstart hretry hfiller

/-- One full-range application checks whole strong measures, real/ideal PRF transport, the
actual eighteen-query bound and the displayed complete security bound. -/
theorem full_range_application :
    SyncSignatureUnforgeability.strongUnforgeableExp
      (Interval.PRFDerived.scheme prf.keygen hash enc prf.eval projection 1 (Interval.full 3))
      ProbCompRuntime.probComp adversary =
        SyncSignatureUnforgeability.strongUnforgeableExp
          (PRFDerived.scheme prf.keygen hash enc
            (Interval.PRFDerived.Unforgeability.restrictPRF prf).eval projection.toComplete 1)
          ProbCompRuntime.probComp adversary ∧
    prf.prfAdvantage (Interval.PRFDerived.Unforgeability.randgenPRFReduction hash enc projection 1
      (Interval.full 3) adversary) =
        (Interval.PRFDerived.Unforgeability.restrictPRF prf).prfAdvantage
          (PRFDerived.Unforgeability.randgenPRFReduction hash enc projection.toComplete 1
            adversary) ∧
    IsQueryBoundP (Interval.PRFDerived.Unforgeability.randgenPRFReduction hash enc projection 1
      (Interval.full 3) adversary) (fun query => query.isRight = true) 18 ∧
    SyncSignatureUnforgeability.strongAdvantage
      (Interval.PRFDerived.scheme prf.keygen hash enc prf.eval projection 1 (Interval.full 3))
      ProbCompRuntime.probComp adversary ≤
        PRFDerived.Unforgeability.strongUnforgeabilityBound hash enc
          (Interval.PRFDerived.Unforgeability.restrictPRF prf) projection.toComplete 1 1
          (by decide) (by decide) adversary := by
  refine ⟨Interval.PRFDerived.Unforgeability.fullRangeStrongExperiment hash enc prf projection 1
    adversary, ?_, ?_, ?_⟩
  · have hreal := Interval.PRFDerived.Unforgeability.fullRangeRealCorrespondence
      hash enc prf projection 1 adversary
    have hideal := Interval.PRFDerived.Unforgeability.fullRangeIdealCorrespondence
      hash enc projection 1 adversary
    unfold Interval.PRFDerived.Unforgeability.FullRangeRealCorrespondence at hreal
    unfold Interval.PRFDerived.Unforgeability.FullRangeIdealCorrespondence at hideal
    unfold PRFScheme.prfAdvantage
    rw [hreal, hideal]
  · have hqueries := Interval.PRFDerived.Unforgeability.randgenPRFReduction_functionQuery_bound
      hash enc projection 1 1 (Interval.full 3) adversary one_signing_request
    have hzero : Fintype.card (Subtree.FrontierNode (Interval.full 3)) = 0 :=
      Fintype.card_eq_zero
    have hlength : (Interval.full 3).last.val - (Interval.full 3).first.val + 1 = 8 := by
      decide
    simpa only [hzero, hlength, Nat.reduceMul, Nat.reduceAdd] using hqueries
  · obtain ⟨hseed, hstart, hretry, _⟩ := projection_laws
    have hbound := Interval.PRFDerived.Unforgeability.fullRangeStrongReductionBound
      hash enc prf projection 1 1 (by decide) (by decide) two_codewords adversary
      one_signing_request hseed hstart hretry
    unfold Interval.PRFDerived.Unforgeability.fullRangeStrongUnforgeabilityBound at hbound
    rw [Interval.PRFDerived.Unforgeability.fullRangeDisplayedBound
      hash enc prf projection 1 1 (by decide) (by decide) adversary] at hbound
    simpa only [PRFDerived.Unforgeability.strongUnforgeabilityBound,
      Unforgeability.reductionBound, Nat.cast_pow, Nat.cast_ofNat] using hbound

end

end GXMSS.PRFProductResponseTest
