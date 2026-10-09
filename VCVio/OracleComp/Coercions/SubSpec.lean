/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import VCVio.OracleComp.Coercions.SubSpec.Basic
public import VCVio.OracleComp.EvalDist

/-!
# Discrete compatibility laws for oracle-signature inclusions

The signature inclusion and operational API is public through `SubSpec.Basic`. This module adds
uniform discrete probability compatibility equations.
-/

public section

universe u v w

open OracleSpec OracleComp ENNReal
open scoped OracleSpec.PrimitiveQuery

namespace OracleSpec.LawfulSubSpec

variable {ι : Type u} {τ : Type v} {spec : OracleSpec ι} {superSpec : OracleSpec τ}
  [h : spec ⊂ₒ superSpec] [spec ˡ⊂ₒ superSpec]

/-- Pushing the uniform distribution on `superSpec.Range` through the lens's
backward fiber recovers the uniform distribution on `spec.Range`. Load-bearing
for `evalSPMF_liftComp` below. -/
lemma evalSPMF_liftM_query [∀ t, Fintype (superSpec.Range t)]
    [∀ t, Nonempty (superSpec.Range t)] (t : spec.Domain) [Fintype (spec.Range t)]
    [Nonempty (spec.Range t)] :
    (PMF.uniformOfFintype (superSpec.Range
      ((liftM (n := OracleQuery superSpec) (spec.query t)).input))).map
      ((liftM (n := OracleQuery superSpec) (spec.query t)).cont) =
      PMF.uniformOfFintype (spec.Range t) := by
  rw [show (liftM (spec.query t) : OracleQuery superSpec (spec.Range t)) =
      ⟨h.onQuery t, h.onResponse t⟩ from h.liftM_eq_lift _]
  exact PMF.uniformOfFintype_map_of_bijective _ (onResponse_bijective t)


end OracleSpec.LawfulSubSpec

namespace OracleComp

section liftComp_evalSPMF

variable {ι : Type u} {τ : Type v}
  {spec : OracleSpec ι} {superSpec : OracleSpec τ} {α : Type w}
variable [spec.IsUniformSpec] [superSpec.IsUniformSpec] [h : spec ⊂ₒ superSpec]

lemma probFailure_liftComp (mx : OracleComp spec α) :
    Pr[⊥ | liftComp mx superSpec] = Pr[⊥ | mx] := by
  rw [probFailure_eq_zero, probFailure_eq_zero]

variable [spec ˡ⊂ₒ superSpec]

@[grind =] lemma evalSPMF_liftComp (mx : OracleComp spec α) :
    𝒮[liftComp mx superSpec] = 𝒮[mx] := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t mx ih =>
    simp only [liftComp_bind, liftComp_query, OracleQuery.cont_query, id_map,
      OracleQuery.input_query, evalSPMF_bind, ih]
    congr 1
    rw [show (liftM (query t) : OracleComp superSpec (spec.Range t)) =
          liftM (liftM (spec.query t) : OracleQuery superSpec _) from rfl,
      evalSPMF_liftM, evalSPMF_query]
    exact congrArg liftM (LawfulSubSpec.evalSPMF_liftM_query t)

@[grind =] lemma probOutput_liftComp (mx : OracleComp spec α) (x : α) :
    Pr[= x | liftComp mx superSpec] = Pr[= x | mx] := by
  rw [probOutput_def, probOutput_def, evalSPMF_liftComp]

@[grind =] lemma probEvent_liftComp (mx : OracleComp spec α) (p : α → Prop) :
    Pr[ p | liftComp mx superSpec] = Pr[ p | mx] := by
  simp only [probEvent_eq_tsum_indicator, probOutput_liftComp]

end liftComp_evalSPMF

end OracleComp
