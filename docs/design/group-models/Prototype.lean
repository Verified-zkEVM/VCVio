/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.QueryTracking.QueryBound.Basic
import VCVio.OracleComp.QueryTracking.CostModel
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# One-group prototype for the group-model design note

Definitions and statements for `docs/design/group-models.md`, Sections 4 and 5. Definitions are
meant to elaborate; theorems whose proofs are `sorry` are statements only. The file is not part
of any Lake library, so it uses plain imports.
-/

open OracleComp OracleSpec ENNReal

/-! Verbatim copy of two definitions from `VCVio/CryptoFoundations/HardnessAssumptions/
DiffieHellman.lean`; that module is not among the compiled modules available to this probe. -/
namespace DiffieHellman

variable {F : Type} [Field F] {G : Type} [AddCommGroup G] [Module F G]

def DLogAdversary (F G : Type) := G → G → ProbComp F

def dlogExperiment [DecidableEq F] [SampleableType F] (g : G) (adversary : DLogAdversary F G) :
    ProbComp Bool := do
  let x ← $ᵗ F
  let x' ← adversary g (x • g)
  return decide (x' = x)

end DiffieHellman

namespace GroupModel

/-- A handle is a position in the table of group elements made available so far. -/
abbrev Handle := ℕ

/-- Queries to a group oracle with scalars in `F`. -/
inductive Query (F : Type) : Type
  | add (a b : Handle)
  | smul (c : F) (a : Handle)
  | eq (a b : Handle)

/-- `add` and `smul` return the handle of the new table entry; `eq` returns a bit. -/
def spec (F : Type) : OracleSpec (Query F)
  | .add _ _ => Handle
  | .smul _ _ => Handle
  | .eq _ _ => Bool

/-- Whether a query appends a table entry. -/
def Query.isOp {F : Type} : Query F → Bool
  | .add _ _ => true
  | .smul _ _ => true
  | .eq _ _ => false

section Handler

variable {F V W : Type}

/-- Out-of-range handles denote zero, so the handler is total. -/
def lookup [Zero V] (tbl : List V) (h : Handle) : V := tbl.getD h 0

/-- Append an entry and return its handle. Game oracles that hand out group elements use this. -/
def push {m : Type → Type} [Monad m] (v : V) : StateT (List V) m Handle :=
  modifyGet fun tbl => (tbl.length, tbl ++ [v])

/-- The one handler: table entries live in `V`, equality is decided on their image under `obs`. -/
def impl [Zero V] [Add V] [SMul F V] [DecidableEq W] (obs : V → W)
    (m : Type → Type) [Monad m] : QueryImpl (spec F) (StateT (List V) m)
  | .add a b => modifyGet fun tbl => (tbl.length, tbl ++ [lookup tbl a + lookup tbl b])
  | .smul c a => modifyGet fun tbl => (tbl.length, tbl ++ [c • lookup tbl a])
  | .eq a b => do
      let tbl ← get
      pure (decide (obs (lookup tbl a) = obs (lookup tbl b)))

/-- A generic computation: private coins and the group oracle, nothing else. -/
abbrev genSpec (F : Type) := unifSpec + spec F

/-- The queries of a generic computation that append a table entry. -/
def isGroupOp : ℕ ⊕ Query F → Bool
  | .inl _ => false
  | .inr t => t.isOp

/-- Run a generic computation on a table. -/
def run [Zero V] [Add V] [SMul F V] [DecidableEq W] (obs : V → W) {α : Type}
    (oa : OracleComp (genSpec F) α) (tbl : List V) : ProbComp (α × List V) :=
  (simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (List V) ProbComp) +
    impl (F := F) obs ProbComp) oa).run tbl

end Handler

/-! ## The three instances -/

section Instances

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-- Real: entries are group elements, equality is equality. -/
abbrev runReal [DecidableEq G] {α : Type} (oa : OracleComp (genSpec F) α) (tbl : List G) :=
  run (F := F) (id : G → G) oa tbl

/-- A representation of a table entry: a coefficient for each handle. Only handles of pushed
entries carry nonzero coefficients. -/
abbrev Repr (F : Type) := Handle → F

/-- Tracking: entries are pairs of a representation and the element; equality sees the element. -/
abbrev runTracking [DecidableEq G] {α : Type} (oa : OracleComp (genSpec F) α)
    (tbl : List (Repr F × G)) :=
  run (F := F) (Prod.snd : Repr F × G → G) oa tbl

/-- The tracking table for inputs `xs`: input `i` is the `i`-th basis element. -/
def trackInputs (xs : List G) : List (Repr F × G) :=
  xs.mapIdx fun i x => (Pi.single i 1, x)

/-- Evaluate a representation on a table. -/
def Repr.eval (r : Repr F) (tbl : List (Repr F × G)) : G :=
  ((List.range tbl.length).map fun h => r h • (lookup tbl h).2).sum

/-- The table invariant, relative to the set `given` of handles whose entries were handed to the
adversary and not computed by it. Every given handle is in the table and its entry is its own
basis element, every representation is supported on given handles, and every entry is the value
of its representation. -/
structure Explains (given : Set Handle) (tbl : List (Repr F × G)) : Prop where
  given_lt : ∀ h ∈ given, h < tbl.length
  repr_given : ∀ h ∈ given, (lookup tbl h).1 = Pi.single h 1
  support_subset : ∀ e ∈ tbl, ∀ h, e.1 h ≠ 0 → h ∈ given
  eq_eval : ∀ e ∈ tbl, e.2 = e.1.eval tbl

/-- Symbolic: entries are polynomials in the unknown logarithms, equality is formal. -/
noncomputable abbrev runSymbolic {σ α : Type} [DecidableEq σ] [DecidableEq F]
    (oa : OracleComp (genSpec F) α) (tbl : List (MvPolynomial σ F)) :=
  run (F := F) (id : MvPolynomial σ F → MvPolynomial σ F) oa tbl

/-- Hidden-real: entries are polynomials, equality is decided after evaluating at `x`. -/
noncomputable abbrev runEval {σ α : Type} [DecidableEq F] (x : σ → F)
    (oa : OracleComp (genSpec F) α) (tbl : List (MvPolynomial σ F)) :=
  run (F := F) (fun P : MvPolynomial σ F => MvPolynomial.eval x P) oa tbl

end Instances

/-! ## Statements -/

section Statements

variable {F : Type} [Field F]

/-- L1 (projection). Along a linear map the observed handler is the plain handler on the image
table. Tracking and real runs therefore have the same output distribution, and so do the
hidden-real run on polynomials and the real run on their values. -/
theorem lookup_map {V W : Type} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (φ : V →ₗ[F] W) (tbl : List V) (h : Handle) :
    lookup (tbl.map φ) h = φ (lookup tbl h) := by
  simp only [lookup, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases tbl[h]? <;> simp

theorem run_map {V W U : Type} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [DecidableEq U] (φ : V →ₗ[F] W) (obs : W → U) {α : Type}
    (oa : OracleComp (genSpec F) α) (tbl : List V) :
    Prod.map id (List.map φ) <$> run (F := F) (obs ∘ φ) oa tbl =
      run (F := F) obs oa (tbl.map φ) := by
  unfold run
  refine OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ (List.map φ) ?_ oa tbl
  intro t s
  rcases t with n | (⟨a, b⟩ | ⟨c, a⟩ | ⟨a, b⟩)
  · simp
  · simp [impl, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run, lookup_map,
      Prod.map]
    rfl
  · simp [impl, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run, lookup_map,
      Prod.map]
    rfl
  · simp only [QueryImpl.add_apply_inr, impl, Function.comp_apply, StateT.run_bind,
      StateT.run_get, pure_bind, lookup_map]
    erw [StateT.run_pure, StateT.run_pure]
    simp
    rfl

/-- T2, distribution part. The tracking run projects exactly onto the real run. -/
theorem runTracking_map_snd {G : Type} [AddCommGroup G] [Module F G] [DecidableEq G] {α : Type}
    (oa : OracleComp (genSpec F) α) (tbl : List (Repr F × G)) :
    Prod.map id (List.map Prod.snd) <$> runTracking oa tbl = runReal oa (tbl.map Prod.snd) :=
  run_map (LinearMap.snd F (Repr F) G) id oa tbl

theorem map_snd_trackInputs {G : Type} (xs : List G) :
    (trackInputs (F := F) xs).map Prod.snd = xs := by
  apply List.ext_getElem <;> simp [trackInputs]

/-- The hidden-real run on polynomials projects exactly onto the real run on their values. -/
theorem runEval_map_eval {σ α : Type} [DecidableEq F] (x : σ → F)
    (oa : OracleComp (genSpec F) α) (tbl : List (MvPolynomial σ F)) :
    Prod.map id (List.map (MvPolynomial.eval x)) <$> runEval x oa tbl =
      runReal oa (tbl.map (MvPolynomial.eval x)) :=
  run_map (MvPolynomial.aeval x : MvPolynomial σ F →ₐ[F] F).toLinearMap id oa tbl

/-- T2 (generic ⊆ algebraic). The tracking run preserves the invariant, so every handle a
generic computation returns comes with a representation over its inputs, which are the entries at
the handles below `xs.length`. -/
theorem explains_of_mem_support_runTracking {G : Type} [AddCommGroup G] [Module F G]
    [DecidableEq G] {α : Type} (oa : OracleComp (genSpec F) α) (xs : List G)
    (z : α × List (Repr F × G)) (hz : z ∈ support (runTracking oa (trackInputs (F := F) xs))) :
    Explains {h | h < xs.length} z.2 := by
  sorry

/-- A generic DLog solver reads `g` at handle `0` and `x • g` at handle `1`. -/
def DLogAdversary.ofGeneric {G : Type} [AddCommGroup G] [Module F G] [DecidableEq G]
    (A : OracleComp (genSpec F) F) : DiffieHellman.DLogAdversary F G :=
  fun g X => Prod.fst <$> runReal A [g, X]

/-- T4 (generic DLog). `q` bounds the number of `add` and `smul` queries; equality queries are
not counted. The table then holds at most `q + 2` entries. An out-of-range handle denotes zero, so
an equality query compares two of at most `q + 3` values, hence at most `(q + 3).choose 2` pairs. -/
theorem dlogExperiment_ofGeneric_le {G : Type} [AddCommGroup G] [Module F G] [DecidableEq G]
    [Fintype F] [DecidableEq F] [SampleableType F] (g : G) (hg : g ≠ 0)
    (A : OracleComp (genSpec F) F) (q : ℕ)
    (hq : IsQueryBoundP A (fun i => isGroupOp i = true) q) :
    𝒟[DiffieHellman.dlogExperiment g (DLogAdversary.ofGeneric (G := G) A)] {true} ≤
      (((q + 3).choose 2 + 1 : ℕ) : ℝ≥0∞) / Fintype.card F := by
  sorry

/-- Default prices: one unit per table entry created, equality tests free. -/
def unitCost : CostModel (spec F) ℕ where
  queryCost t := if t.isOp then 1 else 0

end Statements

end GroupModel
