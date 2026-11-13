/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.Signature
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.SimSemantics.Append
import Mathlib.Data.List.GetD
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Table semantics for sorted group queries

The handler `impl` keeps one table of values per sort. Operations append their result and return
its handle, and equality queries compare the two values through an observation. A handle out of
range in its sort reads as zero (`lookup`), so bounds that count table entries count that zero.
`run` executes group queries together with a game oracle on the same table, and `runGen` adds
uniform sampling that leaves the table unchanged. `Tbl.Extends` is the prefix order on tables.
Every group reply extends the table (`impl_extends`), and so does every generic run
(`runGen_extends`) and every run whose game extends it (`run_extends`); the lookup lemmas say
which values the order preserves.
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

/-- Every sort's list in `tbl` is a prefix of its list in `tbl'`. -/
@[expose] def Tbl.Extends (tbl tbl' : Tbl V) : Prop := ∀ s, tbl s <+: tbl' s

theorem Tbl.Extends.refl (tbl : Tbl V) : Tbl.Extends tbl tbl := fun s => List.prefix_refl (tbl s)

theorem Tbl.Extends.trans {tbl₁ tbl₂ tbl₃ : Tbl V} (h₁₂ : Tbl.Extends tbl₁ tbl₂)
    (h₂₃ : Tbl.Extends tbl₂ tbl₃) : Tbl.Extends tbl₁ tbl₃ := fun s => (h₁₂ s).trans (h₂₃ s)

/-- Appending a value extends the table. -/
theorem extends_append [DecidableEq S] (tbl : Tbl V) (s : S) (v : V s) :
    Tbl.Extends tbl (append tbl s v) := by
  intro t
  by_cases h : t = s
  · subst h
    simp [append]
  · simp [append, Function.update_of_ne h]

/-- A lookup at or past the end of its sort's table returns zero. -/
theorem lookup_eq_zero [∀ s, Zero (V s)] (tbl : Tbl V) (s : S) (h : Handle)
    (hh : (tbl s).length ≤ h) : lookup tbl s h = 0 := List.getD_eq_default _ _ hh

/-- Extending a sort's table preserves the value of every handle already in range. -/
theorem lookup_eq_of_prefix [∀ s, Zero (V s)] {tbl tbl' : Tbl V} (s : S)
    (hp : tbl s <+: tbl' s) (h : Handle) (hh : h < (tbl s).length) :
    lookup tbl' s h = lookup tbl s h := by
  obtain ⟨tail, he⟩ := hp
  simp only [lookup, ← he, List.getD_append _ _ _ _ hh]

/-- Appending preserves lookups at every existing handle. -/
theorem lookup_append_old [DecidableEq S] [∀ s, Zero (V s)] (tbl : Tbl V) (s : S) (v : V s)
    (t : S) (h : Handle) (hh : h < (tbl t).length) :
    lookup (append tbl s v) t h = lookup tbl t h :=
  lookup_eq_of_prefix t (extends_append tbl s v t) h hh

/-- Appending places the new value at the fresh handle. -/
theorem lookup_append_fresh [DecidableEq S] [∀ s, Zero (V s)] (tbl : Tbl V) (s : S) (v : V s) :
    lookup (append tbl s v) s (tbl s).length = v := by
  simp [lookup, append]

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
  (simulateQ (impl M obs m +ₛ game) oa).run tbl

/-- Group queries followed by uniform sampling queries. -/
abbrev genSpec (F : Type) (σ : Sig S) := spec F σ + unifSpec

/-- Execute a generic computation with uniform sampling that leaves the table unchanged. -/
@[expose] def runGen [DecidableEq S] [CommSemiring F]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)]
    [∀ s, DecidableEq (U s)] (M : Model F σ V) (obs : (s : S) → V s → U s) {α : Type}
    (oa : OracleComp (genSpec F σ) α) (tbl : Tbl V) : ProbComp (α × Tbl V) :=
  run M obs ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT (Tbl V) ProbComp)) oa tbl

end Handler

/-! ## Run equations -/

section Run

variable {F : Type} {S : Type} {σ : Sig S} {V U : S → Type} [DecidableEq S] [CommSemiring F]
  [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)] [∀ s, DecidableEq (U s)]
  (M : Model F σ V) (obs : (s : S) → V s → U s)

theorem runGen_pure {α : Type} (a : α) (tbl : Tbl V) :
    runGen M obs (pure a) tbl = pure (a, tbl) := rfl

theorem runGen_bind {α β : Type} (oa : OracleComp (genSpec F σ) α)
    (k : α → OracleComp (genSpec F σ) β) (tbl : Tbl V) :
    runGen M obs (oa >>= k) tbl =
      (runGen M obs oa tbl >>= fun r => runGen M obs (k r.1) r.2) := by
  simp only [runGen, run, simulateQ_bind, StateT.run_bind]

/-- An addition query appends the sum of its two operands and returns the fresh handle. -/
theorem runGen_add (s : S) (a b : Handle) (tbl : Tbl V) :
    runGen M obs (OracleComp.lift ((genSpec F σ).query (.inl (.add s a b)))) tbl =
      pure ((tbl s).length, append tbl s (lookup tbl s a + lookup tbl s b)) := rfl

/-- A scaling query appends the scaled operand and returns the fresh handle. -/
theorem runGen_smul (s : S) (c : F) (a : Handle) (tbl : Tbl V) :
    runGen M obs (OracleComp.lift ((genSpec F σ).query (.inl (.smul s c a)))) tbl =
      pure ((tbl s).length, append tbl s (c • lookup tbl s a)) := rfl

end Run

/-! ## Table growth -/

section Extends

variable {F : Type} {S : Type} {σ : Sig S} {V U : S → Type} [DecidableEq S] [CommSemiring F]
  [∀ s, AddCommMonoid (V s)] [∀ s, Module F (V s)] [∀ s, DecidableEq (U s)]
  (M : Model F σ V) (obs : (s : S) → V s → U s)

/-- Every reachable reply of the group handler extends the table. The handler may run in any
lawful monad whose support is lawful. -/
theorem impl_extends {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m]
    [LawfulMonadAttach m] (t : Query F σ) (tbl : Tbl V) (z : spec F σ t × Tbl V)
    (hz : z ∈ support ((impl M obs m t).run tbl)) : Tbl.Extends tbl z.2 := by
  cases t <;>
    simp only [impl, push, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_modifyGet,
      MonadAttach.mem_support] at hz <;>
    obtain rfl := LawfulMonadAttach.eq_of_canReturn_pure hz
  all_goals first | exact Tbl.Extends.refl tbl | exact extends_append _ _ _

/-- A run extends its input table when every reachable step of the game does. The monad is any
lawful monad whose support is lawful. -/
theorem run_extends {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m]
    [LawfulMonadAttach m] {ι : Type} {Γ : OracleSpec ι} (game : QueryImpl Γ (StateT (Tbl V) m))
    (hg : ∀ t tbl z, z ∈ support ((game t).run tbl) → Tbl.Extends tbl z.2)
    {α : Type} (oa : OracleComp (spec F σ + Γ) α) (tbl : Tbl V) (z : α × Tbl V)
    (hz : z ∈ support (run M obs game oa tbl)) : Tbl.Extends tbl z.2 := by
  refine simulateQ_run_preservesInv (impl M obs m +ₛ game) (Tbl.Extends tbl) ?_ oa tbl
    (Tbl.Extends.refl tbl) z hz
  rintro (t | t) tbl' htbl' w hw
  · exact htbl'.trans (impl_extends M obs t tbl' w hw)
  · exact htbl'.trans (hg t tbl' w hw)

/-- A generic run extends its input table: uniform sampling leaves the table unchanged. -/
theorem runGen_extends {α : Type} (oa : OracleComp (genSpec F σ) α) (tbl : Tbl V)
    (z : α × Tbl V) (hz : z ∈ support (runGen M obs oa tbl)) : Tbl.Extends tbl z.2 := by
  refine run_extends M obs _ ?_ oa tbl z hz
  intro t tbl' w hw
  obtain ⟨y, rfl⟩ : ∃ y, (y, tbl') = w := by simpa using hw
  exact Tbl.Extends.refl tbl'

end Extends

end GroupModel
