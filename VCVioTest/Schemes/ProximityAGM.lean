/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.Schemes.Proximity.Security
public import VCVio.Schemes.Proximity.Extraction
public import Mathlib.Algebra.Field.ZMod

/-! # Proximity fixtures over the field of order 101

Multiplication supplies the pairing and both generators are one. The one-hash adversary
returns its received constant base for a zero-dimensional message. The tests exercise the
ordinary forgetful map and the good reduction's actual lazy-cache computation. Sampling uses
`Fin 101` directly, so importing this module does not enumerate the field.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional
open scoped ENNReal

namespace ProximityAGMTest

/-- Primality of the concrete scalar field. -/
local instance prime101 : Fact (Nat.Prime 101) := ⟨by decide⟩
/-- Uniform sampling without eager field enumeration. -/
local instance sampleField : SampleableType (ZMod 101) :=
  inferInstanceAs (SampleableType (Fin 101))

private abbrev K := ZMod 101
private abbrev Groups := Proximity.AGM.Group K K
private abbrev Spec := explainedSpec K Groups (Proximity.AGM.Query K Bool 0) Proximity.AGM.Reply

private def output (inputs : GroupModel.Interaction.Groups Groups)
    (reply : Message Unit Groups) : Explained K (Proximity.Message K Bool 0) Groups :=
  Explained.ofVectors (extend inputs reply.groups) (0, false) (fun s => match s with
    | false => [fun i => if i.val = (inputs false).length then 1 else 0]
    | true => [])

private def oneHash :
    Proximity.AlgebraicAdversary K Bool K K 0 (LinearMap.mul K K) 1 1 where
  main input := do
    let reply ← Spec.query
      ⟨⟨.inl (.inr (none, false)), Proximity.AGM.groupInputs [] []⟩, fun _ => []⟩
    return output input.groups reply
  algebraic input := by
    constructor
    · exact fun s => by cases s <;> exact .nil
    · intro reply
      exact Explained.valid_ofVectors _ _ _
  protocol input := by
    rw [allPathsSatisfy_query_bind]
    refine ⟨fun s => by cases s <;> rfl, fun reply _ => ?_⟩
    simp [output, Explained.ofVectors]

private theorem oneHash_raw (pk : K) :
    oneHash.toUnforgeableAdversary.main pk = (do
      let h ← (Proximity.AGM.rawSpec K Bool K 0).query (.inl (.inr (none, false)))
      pure ((0, false), h)) := by
  simp [Proximity.AlgebraicAdversary.toUnforgeableAdversary,
    Proximity.AlgebraicAdversary.rawMain, oneHash, Proximity.AGM.oracle,
    output, Explained.ofVectors, Proximity.AGM.forgery, Proximity.AGM.initialInput,
    Proximity.AGM.groupInputs, extend, evaluate]

private theorem oneHash_good (X Y : K) :
    Proximity.goodReduction oneHash 1 X 1 Y = (fun ρ : K => ρ / ρ) <$> ($ᵗ K) := by
  simp only [Proximity.goodReduction, Proximity.AGM.goodProgram, weightedExtractionProgram,
    smul_eq_mul, mul_one, Proximity.AGM.program, Proximity.AGM.oracle, add_apply_inl,
    bind_pure_comp, add_apply_inr, oneHash, output, Explained.ofVectors, Matrix.zero_empty,
    extend, evaluate, List.length_append, List.getElem?_ofFn, Fin.cast_mk,
    Proximity.AGM.initialInput, Proximity.AGM.groupInputs, List.cons_append, List.nil_append,
    List.length_cons, List.length_nil, zero_add, simulateQ_map, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query, Functor.map_map, id_eq, Nat.reduceAdd,
    id_map, StateT.run_map, Proximity.terms, List.ofFn_zero, weightedQuery,
    one_mul, map_pure, add_zero, bind_pure, bind_map_left, Proximity.AGM.coefficients,
    List.isEmpty_iff, List.headD_eq_head?_getD, map_bind, Order.lt_two_iff, List.mapIdx_cons,
    zero_le, ↓reduceDIte, Fin.zero_eta, Fin.isValue, Option.getD_some, add_le_iff_nonpos_left,
    nonpos_iff_eq_zero, Std.le_refl, Fin.mk_one, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    Option.getD_none, zero_mul, List.mapIdx_nil, List.sum_cons, List.sum_nil, List.map_cons,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_ne_one, ↓reduceIte, Nat.mod_succ, List.map_nil,
    List.cons_ne_self, List.ofFn_succ, Fin.val_succ, Fin.val_eq_zero, List.head?_cons,
    simulateQ_bind,
    StateT.run'_eq, StateT.run_bind]
  have hstep :
      (weightedOracle (Proximity.terms (F := K) (dimension := 0)) (fun ρ : K => ρ) (fun ρ => ρ * X)
        (fun ρ => (ρ, (0 : K))) (fun ρ => ((0 : K), ρ))
        (.inl (.inr (none, false)))).run [(1, 0)] =
      (fun ρ : K => (ρ, [(1, 0), (ρ, 0)])) <$>
        ((Proximity.Index Bool 0 →ₒ K).query (none, false) :
          OracleComp (unifSpec + (Proximity.Index Bool 0 →ₒ K)) K) := rfl
  rw [hstep]
  have hquery :
      (liftM (liftM ((Proximity.Index Bool 0 →ₒ K).query (none, false)) :
        OracleComp (Proximity.Index Bool 0 →ₒ K) K) :
        OracleComp (unifSpec + (Proximity.Index Bool 0 →ₒ K)) K) =
      ((Proximity.Index Bool 0 →ₒ K).query (none, false) :
        OracleComp (unifSpec + (Proximity.Index Bool 0 →ₒ K)) K) :=
    OracleComp.liftComp_liftM_query _ _
  simp [hquery]

/-- The direct scheme is perfectly complete over `ZMod 101`, for every dimension and for
arbitrary natural-number slots, using the standard shared random-oracle runtime. -/
theorem perfectlyComplete (dimension : ℕ) :
    (Proximity.scheme (Slot := ℕ) (dimension := dimension)
      (LinearMap.mul (ZMod 101) (ZMod 101)) 1).PerfectlyComplete
        (ProbCompRuntime.rom (Proximity.Index ℕ dimension →ₒ ZMod 101)) :=
  Proximity.perfectlyComplete _ _

/-- A certified one-hash fixture forgets to the literal hash-and-return program; its good
reduction samples one scalar and returns that scalar divided by itself, reusing the cache. -/
theorem one_hash_adversary_exists :
    ∃ A : Proximity.AlgebraicAdversary (ZMod 101) Bool (ZMod 101) (ZMod 101) 0
      (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1,
      (∀ pk, A.toUnforgeableAdversary.main pk = (do
        let h ← (Proximity.AGM.rawSpec (ZMod 101) Bool (ZMod 101) 0).query
          (.inl (.inr (none, false)))
        pure ((0, false), h))) ∧
      (∀ X Y, Proximity.goodReduction A 1 X 1 Y =
        (fun ρ : ZMod 101 => ρ / ρ) <$> ($ᵗ (ZMod 101))) :=
  ⟨oneHash, oneHash_raw, oneHash_good⟩

/-- The source collision predicate can hold with no replies: the zero vector equals the
empty signing combination, independently of the signature and the random-oracle values. -/
theorem freshCollision_empty_zero :
    Proximity.AGM.FreshCollision
      (⟨⟨((0 : Fin 1 → ZMod 101), false), Proximity.AGM.groupInputs [0] ([] : List (ZMod 101))⟩,
        fun s => if s then [] else [[0]]⟩ :
        Explained (ZMod 101) (Proximity.Message (ZMod 101) Bool 1)
          (Proximity.AGM.Group (ZMod 101) (ZMod 101))) [] := by
  simp [Proximity.AGM.FreshCollision, Proximity.AGM.signedMessages]

/-- The full algebraic security theorem specializes to the field of order 101, arbitrary
natural-number slots and dimension, and explicit pathwise hash and signing budgets. -/
theorem security (dimension : ℕ)
    (A : Proximity.AlgebraicAdversary (ZMod 101) ℕ (ZMod 101) (ZMod 101) dimension
      (LinearMap.mul (ZMod 101) (ZMod 101)) 1 1) (qh qs : ℕ)
    (hqueries : A.QueryBound qh qs) :
    SignatureAlg.unforgeableAdvantage
      (ProbCompRuntime.rom (Proximity.Index ℕ dimension →ₒ ZMod 101))
      A.toUnforgeableAdversary ≤
      Pr{let b ← DLog11.experiment 1 1 (Proximity.goodReduction A)}[b = true] +
      Pr{let b ← DLog11.experiment 1 1 (Proximity.badReduction A)}[b = true] +
      1 / 101 + Proximity.freshCollisionProbability A qh qs := by
  have hg : Function.Bijective (· • (1 : ZMod 101) : ZMod 101 → ZMod 101) := by
    constructor
    · intro x y h
      simpa only [smul_eq_mul, mul_one] using h
    · intro y
      exact ⟨y, by simp⟩
  have he : LinearMap.mul (ZMod 101) (ZMod 101) 1 1 ≠ 0 := by simp
  simpa using Proximity.unforgeableAdvantage_le_of_algebraic A qh qs hqueries hg he

end ProximityAGMTest
