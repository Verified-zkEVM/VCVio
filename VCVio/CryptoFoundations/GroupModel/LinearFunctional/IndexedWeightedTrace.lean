/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.LinearFunctional.WeightedTrace
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-! # Paired finite tables for message-dependent weighted extraction

Independent uniform tables are equivalent to a uniform table of pairs. Mapping finite-table
entries commutes with extending them to the full label type. The public trace interface exports
the message-dependent execution and coverage theorems.
-/

public section

open OracleComp OracleSpec

namespace GroupModel.LinearFunctional

/-- Independent uniform tables pair to a uniform table of pairs. -/
theorem uniformSample_pair_tables {F I : Type} [SampleableType F] [Fintype I] [DecidableEq I] :
    (do let a ← $ᵗ (I → F); let b ← $ᵗ (I → F); return fun i => (a i, b i)) =ᵈ
      ($ᵗ (I → F × F) : ProbComp _) := by
  apply SampleableType.evalDistEq_uniformSample_pair_of_bijective
  constructor
  · intro ⟨a, b⟩ ⟨c, d⟩ h
    exact Prod.ext (funext fun i => congrArg Prod.fst (congrFun h i))
      (funext fun i => congrArg Prod.snd (congrFun h i))
  · intro ρ
    exact ⟨(fun i => (ρ i).1, fun i => (ρ i).2), rfl⟩

/-- Extending a finite table commutes with mapping both its entries and its fallback. -/
theorem extendTable_map {I R U : Type} [DecidableEq I]
    (S : Finset I) (fallback : R) (table : S → R) (f : R → U) (i : I) :
    extendTable S (f fallback) (fun j => f (table j)) i = f (extendTable S fallback table i) := by
  simp only [GroupModel.LinearFunctional.extendTable]
  split <;> rfl

end GroupModel.LinearFunctional
