/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/

module

public import VCVio.OracleComp.Constructions.RandomPermutation.Conditioning

/-!
# Uniform permutations extending a finite trace

Sequential swaps retain both programmed edges even when one source is an earlier target.
-/

public section

open OracleComp OracleComp.PermutationConditioning OracleComp.UniformPreimage

namespace VCVioTest.RandomPermutationConditioning

variable {α : Type}

/-- The empty trace is satisfied by every permutation. -/
theorem extensions_nil_nonempty : Nonempty (Extensions ([] : List (α × α))) :=
  ⟨⟨1, by simp⟩⟩

/-- The source `1` of the second edge is the first edge's target. The fresh-program law must
allow this overlap and retain both constraints after sequential swaps. -/
example :
    Pr{let p ← (fun p : Equiv.Perm (Fin 3) => install p [(0, 1), (1, 2)]) <$>
      uniformPermutations [] extensions_nil_nonempty}[p 0 = 1 ∧ p 1 = 2] = 1 := by
  have hfresh : FreshProgram ([] : List (Fin 3 × Fin 3)) [(0, 1), (1, 2)] := by
    constructor <;> simp
  have hdist := map_install_uniformPermutations [] [(0, 1), (1, 2)] hfresh
    extensions_nil_nonempty
  rw [(evalDistEq_iff_evalDist_eq.mpr hdist).prEvent_eq]
  let _ := extensions_append_nonempty [] [(0, 1), (1, 2)] hfresh extensions_nil_nonempty
  let _ := SampleableType.ofFintype (Extensions ([] ++ [(0, 1), (1, 2)] : List (Fin 3 × Fin 3)))
  simp only [uniformPermutations, uniformExtensions, prEvent_map]
  change Pr{let p ← $ᵗ (Extensions ([] ++ [(0, 1), (1, 2)] : List (Fin 3 × Fin 3)))}[
    p.1 0 = 1 ∧ p.1 1 = 2] = 1
  apply (SampleableType.prEvent_uniformSample_eq_one_iff _).mpr
  intro p
  exact ⟨p.2 (0, 1) (by simp), p.2 (1, 2) (by simp)⟩

end VCVioTest.RandomPermutationConditioning
