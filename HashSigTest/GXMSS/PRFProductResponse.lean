/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.PRFDerivedUnforgeability
public import HashSig.GXMSS.Security.Interval.PRFDerivedFullRange

/-!
# Product responses and actual PRF key sampling

Finite product responses supply the projection laws. A nonuniform captured Boolean key sampler
exercises native complete and interval transports; full range also accepts a false filler law.
-/

public section

namespace GXMSS.PRFProductResponseTest

open IncomparableEncoding IntervalMerkle OracleComp OracleSpec ENNReal

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
  code := {word | word = ![0, 1] ∨ word = ![1, 0]}
  incomparable := by
    intro x hx y hy hne
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      exact incomparableWords_of_sum_eq hne (by decide)
  encode := fun _ _ r _ =>
    some ⟨(if r then ![0, 1] else ![1, 0]), by cases r <;> simp⟩

/-- The explicit two-word code is exactly the length-two binary fixed-sum code. -/
theorem code_iff_sum (word : Codeword 2 2) :
    word ∈ enc.code ↔ ∑ i, (word i).val = 1 := by
  change (word = ![0, 1] ∨ word = ![1, 0]) ↔ _
  have hword : word = ![word 0, word 1] := by
    funext index
    fin_cases index <;> rfl
  rw [hword]
  generalize word 0 = first, word 1 = second
  fin_cases first <;> fin_cases second <;> decide

private theorem two_codewords : ∃ x y : Codeword 2 2,
    x ∈ enc.code ∧ y ∈ enc.code ∧ x ≠ y := by
  exact ⟨![0, 1], ![1, 0], by simp [enc],
    by simp [enc], by decide⟩

/-- The actual captured key sampler gives true mass one third. -/
@[expose] def prf :
    PRFScheme Bool (Interval.PRFDerived.Query Unit Unit 3 2) Response where
  keygen := (fun i : Fin 3 => decide (i = 0)) <$> ($ᵗ Fin 3)
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
    SyncSignatureUnforgeability.SigningQueryBound 1 adversary := by
  intro pk
  dsimp [adversary, SyncSignatureUnforgeability.Forgery]
  rw [isQueryBoundP_query_bind_iff]
  constructor
  · simp
  · intro answer
    exact isQueryBoundP_pure _ _ _

noncomputable section

/-- Decidable input equality for the native interval game. -/
local instance intervalQueryDecidableEq :
    DecidableEq (Interval.PRFDerived.Query Unit Unit 3 2) := Classical.decEq _
/-- Decidable input equality for the native complete game. -/
local instance completeQueryDecidableEq :
    DecidableEq (PRFDerived.Query Unit Unit 3 2) := Classical.decEq _

/-- The Boolean key draw has true mass one third, rather than the uniform one half. -/
theorem keygen_true_mass :
    let : MeasurableSpace Bool := ⊤
    𝒟[prf.keygen] {true} = (3 : ENNReal)⁻¹ := by
  let : MeasurableSpace Bool := ⊤
  let : MeasurableSpace (Fin 3) := ⊤
  change 𝒟[(fun i : Fin 3 => decide (i = 0)) <$> ($ᵗ Fin 3)] {true} = _
  rw [evalDist_map_of_discrete,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton true)]
  have hpre : (fun i : Fin 3 => decide (i = 0)) ⁻¹' {true} = {0} := by
    ext i
    simp
  rw [hpre, SampleableType.evalDist_uniformSample_singleton]
  norm_num

/-- This captured generator does not satisfy UniformKey. -/
theorem keygen_not_uniform : ¬ prf.UniformKey := by
  intro h
  let : MeasurableSpace Bool := ⊤
  have hmass := keygen_true_mass
  change 𝒟[prf.keygen] {true} = (3 : ENNReal)⁻¹ at hmass
  rw [h, SampleableType.evalDist_uniformSample_singleton] at hmass
  norm_num at hmass

/-- An intentionally biased filler leaves the complete projections unchanged. -/
@[expose] def badFillerProjection : Interval.PRFDerived.Interpretation Unit Bool Bool Response :=
  { projection with fillerDigest := fun _ => false }

/-- The fourth global projection premise is actually false. -/
theorem bad_filler_law :
    ¬ Interval.PRFDerived.Unforgeability.FillerSamplingLaw badFillerProjection := by
  intro h
  let : MeasurableSpace Bool := ⊤
  change 𝒟[(fun _ : Response => false) <$> ($ᵗ Response)] = 𝒟[$ᵗ Bool] at h
  have htrue := congrArg (fun μ : MeasureTheory.Measure Bool => μ {true}) h
  norm_num at htrue
  have hn : (2 : ENNReal)⁻¹ ≠ 0 := by simp
  exact hn htrue.symm

/-- The interior interval still uses all four product projection laws. -/
theorem interval_security :
    let I : Interval 3 := ⟨3, 4, by decide⟩
    SyncSignatureUnforgeability.strongAdvantage
      (Interval.PRFDerived.scheme prf.keygen hash enc prf.eval projection 1 I)
      ProbCompRuntime.probComp adversary ≤
      Interval.PRFDerived.Unforgeability.strongUnforgeabilityBound hash enc prf projection 1 1 I
        (by decide) (by decide) adversary := by
  obtain ⟨hseed, hstart, hretry, hfiller⟩ := projection_laws
  exact Interval.PRFDerived.Unforgeability.strong_unforgeability_reduction_bound
    hash enc prf projection 1 1 ⟨3, 4, by decide⟩ (by decide) (by decide)
    (enc.noMaximumOutput_of_two_codewords two_codewords) adversary one_signing_request
    hseed hstart hretry hfiller

/-- A complete public endpoint applies with precisely the three complete projection laws. -/
theorem complete_security :
    let complete := PRFScheme.DomainTransport.pullback prf Interval.PRFDerived.Query.ofComplete
    SyncSignatureUnforgeability.strongAdvantage
      (PRFDerived.scheme complete.keygen hash enc complete.eval projection.toComplete 1)
      ProbCompRuntime.probComp adversary ≤
      PRFDerived.Unforgeability.strongUnforgeabilityBound hash enc complete projection.toComplete
        1 1 (by decide) (by decide) adversary := by
  obtain ⟨hseed, hstart, hretry, _⟩ := projection_laws
  exact PRFDerived.Unforgeability.strong_unforgeability_reduction_bound hash enc
    (PRFScheme.DomainTransport.pullback prf Interval.PRFDerived.Query.ofComplete)
    projection.toComplete 1 1 (by decide) (by decide)
    (enc.noMaximumOutput_of_two_codewords two_codewords) adversary one_signing_request
    hseed hstart hretry

/-- Full-range security applies even though its global filler premise is false. -/
theorem full_range_bad_filler_security :
    SyncSignatureUnforgeability.strongAdvantage
      (Interval.PRFDerived.scheme prf.keygen hash enc prf.eval badFillerProjection 1
        (Interval.full 3)) ProbCompRuntime.probComp adversary ≤
      Interval.PRFDerived.Unforgeability.fullRangeStrongUnforgeabilityBound hash enc prf
        badFillerProjection 1 1 (by decide) (by decide) adversary := by
  obtain ⟨hseed, hstart, hretry, _⟩ := projection_laws
  exact Interval.PRFDerived.Unforgeability.fullRangeStrongReductionBound hash enc prf
    badFillerProjection 1 1 (by decide) (by decide)
    (enc.noMaximumOutput_of_two_codewords two_codewords) adversary one_signing_request
    hseed hstart hretry

/-- Native original-domain and full-range distinguishers have the same eighteen-call count. -/
theorem full_range_query_bounds :
    IsQueryBoundP (Interval.PRFDerived.Unforgeability.randgenPRFReduction hash enc
      badFillerProjection 1 (Interval.full 3) adversary) (fun query => query.isRight = true) 18 ∧
    IsQueryBoundP (PRFDerived.Unforgeability.randgenPRFReduction hash enc
      projection.toComplete 1 adversary) (fun query => query.isRight = true) 18 := by
  constructor
  · simpa [Interval.PRFDerived.Unforgeability.functionQueryCount,
      Interval.PRFDerived.Unforgeability.keyMaterialQueryCount] using
      Interval.PRFDerived.Unforgeability.randgenPRFReduction_functionQuery_bound hash enc
        badFillerProjection 1 1 (Interval.full 3) adversary one_signing_request
  · exact PRFDerived.Unforgeability.randgenPRFReduction_functionQuery_bound hash enc
      projection.toComplete 1 1 adversary one_signing_request

end
end GXMSS.PRFProductResponseTest
