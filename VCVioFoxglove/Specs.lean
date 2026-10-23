/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVioFoxglove.Adequacy
public import VCVio.OracleComp.Constructions.SampleableType.Basic

/-!
# Laws of VCVio's samplers

The leaf specifications Foxglove proofs about VCVio programs start from, each read off VCVio's
measure semantics by `wp_of_evalDist`:

* `wp_uniformSample`: `$ᵗ α` has the uniform law;
* `wp_query_unifSpec`: the uniform oracle's query `$[0..n]` has the uniform law on `Fin (n + 1)`;
* `wp_of_evalDist_eq`: a program with the same output measure as one of known law has that law.
-/

@[expose] public section

namespace Foxglove

open Interp OracleSpec OracleComp

noncomputable section

/-- **The uniform sampler has the uniform law.** -/
theorem wp_uniformSample (α : Type) [SampleableType α] [Fintype α] [Inhabited α] :
    ⊢ wp ($ᵗ α : ProbComp α) ⦃X, X ~ PMF.uniformOfFintype' α⦄ := by
  let : MeasurableSpace α := ⊤
  exact wp_of_evalDist fun a ↦ by
    rw [SampleableType.evalDist_uniformSample, ProbabilityTheory.uniformOn_univ_apply_singleton,
      PMF.uniformOfFintype'_apply]

/-- **The uniform oracle has the uniform law.** -/
theorem wp_query_unifSpec (n : ℕ) :
    ⊢ wp (unifSpec.query n : OracleComp unifSpec (Fin (n + 1)))
      ⦃X, X ~ PMF.uniformOfFintype' (Fin (n + 1))⦄ :=
  wp_of_evalDist fun i ↦ by simp [ProbabilityTheory.uniformOn_univ]

/-- **Every program has its tape law** (`WP_SAMP`). -/
theorem wp_lawPMF {ι α : Type} {oSpec : OracleSpec ι} [BernoulliImpl oSpec] [Inhabited α]
    [Countable α] (oa : OracleComp oSpec α) :
    ⊢ wp oa ⦃X, X ~ lawPMF (BernoulliInterpretable.interp oa)⦄ :=
  Proofs.WP_SAMP (BernoulliInterpretable.interp oa) _ fun a ↦ (lawPMF_apply _ a).symm

/-- **Laws transfer along equal output measures**: VCVio's distributional equalities are
Foxglove law equalities. -/
theorem wp_of_evalDist_eq {ι α : Type} {oSpec : OracleSpec ι} [BernoulliImpl oSpec]
    [oSpec.AnswerMeasure] [LawfulBernoulliImpl oSpec] [Inhabited α] [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {oa ob : OracleComp oSpec α} {ν : PMF α}
    (hab : 𝒟[oa] = 𝒟[ob]) (hb : ⊢ wp ob ⦃X, X ~ ν⦄) : ⊢ wp oa ⦃X, X ~ ν⦄ :=
  wp_of_evalDist fun a ↦ by rw [hab, evalDist_of_wp hb]

end

end Foxglove
