/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.Probability
import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery

/-! # Uniform linear-functional collisions

This follows Gurkan's linear-functional proof of BLS security in the algebraic group model
of Fuchsbauer, Kiltz and Loss (CRYPTO 2018). Resampling one nonzero coordinate bounds a
functional of an independent uniform table. Coefficients may be selected by an earlier
computation, provided the table remains independent of it.
-/

public section

open OracleComp Finset

namespace GroupModel.LinearFunctional

/-- A nonzero functional of an independent uniform vector hits a prescribed value with
probability at most the reciprocal field cardinality. -/
theorem prEvent_sum_mul_uniform_le {F ι : Type} [Field F] [Fintype F] [SampleableType F]
    [Fintype ι] [DecidableEq ι] (L : ι → F) (j : ι) (hj : L j ≠ 0) (t : F) :
    Pr{let ρ ← $ᵗ (ι → F)}[∑ i, L i * ρ i = t] ≤ 1 / Fintype.card F := by
  have hsum (g : ι → F) (u : F) :
      ∑ i, L i * Function.update g j u i =
        L j * u + ∑ i ∈ univ.erase j, L i * g i := by
    rw [← Finset.add_sum_erase univ (fun i => L i * Function.update g j u i) (mem_univ j),
      Function.update_self]
    congr 1
    exact Finset.sum_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [prEvent_uniformTable_update j, prEvent_bind_map_swap]
  simp_rw [hsum]
  exact prEvent_affine_uniform_le ($ᵗ (ι → F)) (fun _ => L j)
    (fun g => ∑ i ∈ univ.erase j, L i * g i) (fun _ => t) (fun _ _ => hj)

/-- Adaptive coefficients still obey the collision bound when their entire view is sampled
before the independent uniform vector. -/
theorem prEvent_adaptive_sum_mul_uniform_le {F ι γ : Type}
    [Field F] [Fintype F] [SampleableType F] [Fintype ι] [DecidableEq ι]
    (oa : ProbComp γ) (L : γ → ι → F) (j : γ → ι) (t : γ → F)
    (h : ∀ z ∈ support oa, L z (j z) ≠ 0) :
    Pr{let z ← oa; let ρ ← $ᵗ (ι → F)}[∑ i, L z i * ρ i = t z] ≤
      1 / Fintype.card F := by
  have hb := prEvent_bind_le_of_forall_le_of_support oa
    (fun z => (fun ρ : ι → F => ∑ i, L z i * ρ i = t z) <$> ($ᵗ (ι → F))) id
    (ε := 1 / Fintype.card F) (fun z hz => by
      simpa only [prEvent_norm, id_eq] using
        prEvent_sum_mul_uniform_le (L z) (j z) (h z hz) (t z))
  simpa only [prEvent_norm, id_eq] using hb

end GroupModel.LinearFunctional
