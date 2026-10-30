/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Signature
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.SimSemantics.Append

/-!
# Table semantics for sorted group queries
-/

public section

open OracleComp OracleSpec

namespace GroupModel

section Handler

variable {F : Type} {S : Type} {σ : Sig S} {V W U : S → Type}

/-- One table per sort. -/
abbrev Tbl (V : S → Type) := (s : S) → List (V s)

/-- Read a handle, returning zero for an out-of-range index. -/
@[expose] def lookup [∀ s, Zero (V s)] (tbl : Tbl V) (s : S) (h : Handle) : V s := (tbl s).getD h 0

/-- Append a value to the table of its sort. -/
@[expose] def append [DecidableEq S] (tbl : Tbl V) (s : S) (v : V s) : Tbl V :=
  Function.update tbl s (tbl s ++ [v])

/-- Apply a sort-indexed map to every table entry. -/
@[expose] def mapTbl (φ : (s : S) → V s → W s) (tbl : Tbl V) : Tbl W := fun s => (tbl s).map (φ s)

/-- Mapping table entries commutes with appending a value. -/
theorem mapTbl_append [DecidableEq S] (φ : (s : S) → V s → W s) (tbl : Tbl V) (s : S) (v : V s) :
    mapTbl φ (append tbl s v) = append (mapTbl φ tbl) s (φ s v) := by
  funext t
  by_cases h : t = s
  · subst h
    simp [mapTbl, append]
  · simp [mapTbl, append, Function.update_of_ne h]

/-- Linear maps commute with lookup, including its zero default. -/
theorem lookup_mapTbl [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    [∀ s, AddCommMonoid (W s)] [∀ s, Module F (W s)]
    (φ : (s : S) → V s →ₗ[F] W s) (tbl : Tbl V) (s : S) (h : Handle) :
    lookup (mapTbl (fun s => φ s) tbl) s h = φ s (lookup tbl s h) := by
  simp only [lookup, mapTbl, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (tbl s)[h]? <;> simp

/-- Append a value and return its fresh handle in that sort. -/
@[expose] def push [DecidableEq S] {m : Type → Type} [Monad m]
    (s : S) (v : V s) : StateT (Tbl V) m Handle :=
  modifyGet fun tbl => ((tbl s).length, append tbl s v)

/-- The table handler, with equality determined by the observation. -/
@[expose] def impl [DecidableEq S] [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    [∀ s, DecidableEq (U s)] (M : Model F σ V) (obs : (s : S) → V s → U s)
    (m : Type → Type) [Monad m] : QueryImpl (spec F σ) (StateT (Tbl V) m)
  | .add s a b => fun tbl =>
      (push s (lookup tbl s a + lookup tbl s b)).run tbl
  | .smul s c a => fun tbl =>
      (push s (c • lookup tbl s a)).run tbl
  | .eq s a b => do
      let tbl ← get
      pure (decide (obs s (lookup tbl s a) = obs s (lookup tbl s b)))
  | .lin o a => fun tbl =>
      (push (σ.ltgt o) (M.lin o (lookup tbl (σ.lsrc o) a))).run tbl
  | .bil o a b => fun tbl =>
      (push (σ.tgt o) (M.bil o (lookup tbl (σ.src₁ o) a)
        (lookup tbl (σ.src₂ o) b))).run tbl

/-- Execute group queries and an extra game oracle on a shared table. -/
@[expose] def run [DecidableEq S] [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    [∀ s, DecidableEq (U s)] (M : Model F σ V) (obs : (s : S) → V s → U s)
    {m : Type → Type} [Monad m] {ι : Type} {Γ : OracleSpec ι}
    (game : QueryImpl Γ (StateT (Tbl V) m)) {α : Type}
    (oa : OracleComp (spec F σ + Γ) α) (tbl : Tbl V) : m (α × Tbl V) :=
  (simulateQ (impl M obs m + game) oa).run tbl

/-- Group queries followed by uniform sampling queries. -/
abbrev genSpec (F : Type) (σ : Sig S) := spec F σ + unifSpec

/-- Execute a generic computation with uniform sampling that leaves the table unchanged. -/
@[expose] def runGen [DecidableEq S] [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    [∀ s, DecidableEq (U s)] (M : Model F σ V) (obs : (s : S) → V s → U s) {α : Type}
    (oa : OracleComp (genSpec F σ) α) (tbl : Tbl V) : ProbComp (α × Tbl V) :=
  run M obs ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Tbl V) ProbComp)) oa tbl

end Handler

end GroupModel
