/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

/-!
# Independent dependent-effect replay model

This comparison model has no imports. Prefix restoration, arbitrary nested
branching, output observation, and work observation use ordinary dependent
request/continuation syntax. It is not an implementation of another framework.
-/

public section

namespace PlainReplay

universe u

/-- Conventional dependent request/continuation syntax. -/
inductive Program (I : Type u) (R : I → Type u) (A : Type u) where
  | ret (value : A) : Program I R A
  | call (request : I) (next : R request → Program I R A) : Program I R A

variable {I : Type u} {R : I → Type u} {A : Type u}

/-- Typed responses selecting a completed source execution. -/
@[expose]
def Path : Program I R A → Type u
  | .ret _ => PUnit
  | .call i next => (answer : R i) × Path (next answer)

/-- Output of a completed source execution. -/
@[expose]
def output : (p : Program I R A) → Path p → A
  | .ret a, _ => a
  | .call _ next, ⟨answer, tail⟩ => output (next answer) tail

/-- All requests and answers of a completed execution. -/
@[expose]
def trace : (p : Program I R A) → Path p → List ((i : I) × R i)
  | .ret _, _ => []
  | .call i next, ⟨answer, tail⟩ => ⟨i, answer⟩ :: trace (next answer) tail

/-- Interpret a program in any monad. -/
@[expose]
def run {m : Type u → Type u} [Monad m] (handler : (i : I) → m (R i)) :
    Program I R A → m A
  | .ret a => pure a
  | .call i next => handler i >>= fun answer => run handler (next answer)

/-- A typed source saved ending at a residual program. -/
inductive Prefix : Program I R A → Program I R A → Type u where
  | root (p : Program I R A) : Prefix p p
  | down {i : I} {next : R i → Program I R A} {rest : Program I R A}
      (answer : R i) (tail : Prefix (next answer) rest) : Prefix (.call i next) rest

/-- Complete a source execution from its saved saved and a residual path. -/
@[expose]
def Prefix.plug : {p rest : Program I R A} → Prefix p rest → Path rest → Path p
  | _, _, .root _, path => path
  | _, _, .down answer tail, path => ⟨answer, tail.plug path⟩

/-- Events retained in a saved. -/
@[expose]
def Prefix.events : {p rest : Program I R A} → Prefix p rest → List ((i : I) × R i)
  | _, _, .root _ => []
  | _, _, .down (i := i) answer tail => ⟨i, answer⟩ :: tail.events

/-- Reconstructing a source execution preserves the residual output. -/
theorem Prefix.output_plug {p rest : Program I R A} (saved : Prefix p rest)
    (path : Path rest) : output p (saved.plug path) = output rest path := by
  induction saved with
  | root => rfl
  | down answer tail ih => exact ih path

/-- Reconstruction appends the residual events to the saved events. -/
theorem Prefix.trace_plug {p rest : Program I R A} (saved : Prefix p rest)
    (path : Path rest) : trace p (saved.plug path) = saved.events ++ trace rest path := by
  induction saved with
  | root => rfl
  | down answer tail ih => exact congrArg (List.cons _) (ih path)

/-- Nested branching at arbitrary saved request continuations. -/
inductive Tree : Program I R A → Type u where
  | leaf {p} (path : Path p) : Tree p
  | branch {p} {i : I} {next : R i → Program I R A}
      (saved : Prefix p (.call i next)) (arity : Nat)
      (answers : Fin arity → R i) (children : (j : Fin arity) → Tree (next (answers j))) : Tree p

/-- A selected replay leaf. -/
inductive Leaf : {p : Program I R A} → Tree p → Type u where
  | leaf {p} {path : Path p} : Leaf (.leaf path)
  | branch {p} {i : I} {next : R i → Program I R A}
      {saved : Prefix p (.call i next)} {arity : Nat}
      {answers : Fin arity → R i} {children : (j : Fin arity) → Tree (next (answers j))}
      (j : Fin arity) (tail : Leaf (children j)) : Leaf (.branch saved arity answers children)

/-- Reconstruct the source execution of a selected leaf. -/
@[expose]
def Leaf.path : {p : Program I R A} → {tree : Tree p} → Leaf tree → Path p
  | _, .leaf path, .leaf => path
  | _, .branch saved _ answers _, .branch j tail => saved.plug ⟨answers j, tail.path⟩

/-- A property of source executions holds at every reconstructed replay leaf. -/
theorem leaf_property {p : Program I R A} (tree : Tree p)
    (property : Path p → Prop) (valid : ∀ path, property path) (leaf : Leaf tree) :
    property leaf.path := valid leaf.path

/-- Observe arbitrary nonnegative request/answer charges on a source execution. -/
@[expose]
def work (charge : ((i : I) × R i) → Nat) (events : List ((i : I) × R i)) : Nat :=
  (events.map charge).sum

/-- Prefix and residual work both contribute to a reconstructed execution. -/
theorem Prefix.work_plug {p rest : Program I R A} (saved : Prefix p rest)
    (path : Path rest) (charge : ((i : I) × R i) → Nat) :
    work charge (trace p (saved.plug path)) =
      work charge saved.events + work charge (trace rest path) := by
  rw [saved.trace_plug]
  simp [work, List.map_append, List.sum_append]

end PlainReplay
