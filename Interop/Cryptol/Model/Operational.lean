/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Primitives
public import PolyFun.ITree.Transition

/-!
# Call-by-name abstract machine

The machine stores suspended closed expressions and an explicit typed stack.
Substitution closes lexical environments when a binder is entered; it does
not evaluate the argument. Values retain suspended fields and sequence
generators. Each transition is total, and unbounded execution exposes one
ITree silent step per machine transition.
-/

public section

namespace Interop.Cryptol

/-- An outer value, with every lazy component retained as syntax. -/
inductive RuntimeValue : ClosedTy → Type where
  | bit (value : Bool) : RuntimeValue .bit
  | integer (value : Int) : RuntimeValue .integer
  | unit : RuntimeValue .unit
  | function {a b} (body : Expr [a] b) : RuntimeValue (.arrow a b)
  | pair {a b} (left : Expr [] a) (right : Expr [] b) : RuntimeValue (.prod a b)
  | sequence {a} (length : Length) (body : Expr [.integer] a) :
      RuntimeValue (.seq length a)

/-- A single demand on an outer value. -/
inductive Frame : ClosedTy → ClosedTy → Type where
  | force {a b} (next : Expr [] b) : Frame a b
  | app {a b} (argument : Expr [] a) : Frame (.arrow a b) b
  | fst {a b} : Frame (.prod a b) a
  | snd {a b} : Frame (.prod a b) b
  | index {l a} (index : ClosedExpr [] .integer) : Frame (.seq l a) a
  | indexInto {a} (length : Length) (body : Expr [.integer] a) : Frame .integer a
  | branch {a} (yes no : Expr [] a) : Frame .bit a
  | bitNot : Frame .bit .bit
  | bitLeft (op : BitOp) (right : ClosedExpr [] .bit) : Frame .bit .bit
  | bitRight (op : BitOp) (left : Bool) : Frame .bit .bit
  | intLeft (op : IntOp) (right : ClosedExpr [] .integer) : Frame .integer .integer
  | intRight (op : IntOp) (left : Int) : Frame .integer .integer
  | eqLeft (right : ClosedExpr [] .integer) : Frame .integer .bit
  | eqRight (left : Int) : Frame .integer .bit
  | ltLeft (right : ClosedExpr [] .integer) : Frame .integer .bit
  | ltRight (left : Int) : Frame .integer .bit

/-- A finite typed evaluation stack. -/
inductive Stack : ClosedTy → ClosedTy → Type where
  | done {a} : Stack a a
  | push {a b r} (frame : Frame a b) (rest : Stack b r) : Stack a r

/-- A machine configuration. Errors discard all strict evaluation frames. -/
inductive MachineState (result : ClosedTy) where
  | eval {a} (expression : Expr [] a) (stack : Stack a result)
  | value {a} (value : RuntimeValue a) (stack : Stack a result)
  | error (error : EvalError)

/-- Terminated execution can return an outer value or an explicit error. -/
abbrev Outcome (a : ClosedTy) := Except EvalError (RuntimeValue a)

namespace MachineState

/-- Continue one evaluation frame with a returned outer value. -/
@[expose] def resume {a b r : ClosedTy} : Frame a b → RuntimeValue a → Stack b r → MachineState r
  | .force next, _, rest => .eval next rest
  | .app argument, .function body, rest => .eval (body.substOne argument) rest
  | .fst, .pair left _, rest => .eval left rest
  | .snd, .pair _ right, rest => .eval right rest
  | .index index, .sequence length body, rest =>
      .eval index (.push (.indexInto length body) rest)
  | .indexInto length body, .integer index, rest =>
      match length.checkIndex index with
      | none => .error (.invalidIndex index)
      | some _ => .eval (body.substOne (.integer index)) rest
  | .branch yes no, .bit b, rest => .eval (if b then yes else no) rest
  | .bitNot, .bit b, rest => .value (.bit (!b)) rest
  | .bitLeft op right, .bit left, rest => .eval right (.push (.bitRight op left) rest)
  | .bitRight op left, .bit right, rest => .value (.bit (op.eval left right)) rest
  | .intLeft op right, .integer left, rest => .eval right (.push (.intRight op left) rest)
  | .intRight op left, .integer right, rest =>
      match op.eval left right with
      | .ok result => .value (.integer result) rest
      | .error e => .error e
  | .eqLeft right, .integer left, rest => .eval right (.push (.eqRight left) rest)
  | .eqRight left, .integer right, rest => .value (.bit (left == right)) rest
  | .ltLeft right, .integer left, rest => .eval right (.push (.ltRight left) rest)
  | .ltRight left, .integer right, rest => .value (.bit (decide (left < right))) rest

/-- Execute one total transition. The right branch is an exact residual. -/
@[expose] def step {r : ClosedTy} : MachineState r → Outcome r ⊕ MachineState r
  | .error e => .inl (.error e)
  | .value v .done => .inl (.ok v)
  | .value v (.push frame rest) => .inr (resume frame v rest)
  | .eval expression stack => .inr (match expression with
    | .var v => nomatch v
    | .bit x => .value (.bit x) stack
    | .integer x => .value (.integer x) stack
    | .unit => .value .unit stack
    | .error e => .error e
    | .lam body => .value (.function body) stack
    | .app f x => .eval f (.push (.app x) stack)
    | .letE x body => .eval (body.substOne x) stack
    | .force x next => .eval x (.push (.force next) stack)
    | .pair x y => .value (.pair x y) stack
    | .fst x => .eval x (.push .fst stack)
    | .snd x => .eval x (.push .snd stack)
    | .generate length body => .value (.sequence length body) stack
    | .index xs i => .eval xs (.push (.index i) stack)
    | .ite p x y => .eval p (.push (.branch x y) stack)
    | .fix body => .eval (body.substOne (.fix body)) stack
    | .bitNot x => .eval x (.push .bitNot stack)
    | .bitOp op x y => .eval x (.push (.bitLeft op y) stack)
    | .intOp op x y => .eval x (.push (.intLeft op y) stack)
    | .intEq x y => .eval x (.push (.eqLeft y) stack)
    | .intLt x y => .eval x (.push (.ltLeft y) stack))

/-- An execution chunk either finishes or retains the exact paused state. -/
abbrev run {r : ClosedTy} : Nat → MachineState r → Outcome r ⊕ MachineState r :=
  Control.Transition.run step

/-- Continue a paused chunk; a completed chunk is already final. -/
abbrev continueRun {r : ClosedTy} (fuel : Nat) :
    Outcome r ⊕ MachineState r → Outcome r ⊕ MachineState r :=
  Control.Transition.continueRun step fuel

/-- Splitting the fuel budget preserves the exact result or residual state. -/
theorem run_add {r : ClosedTy} (n m : Nat) (state : MachineState r) :
    run (n + m) state = continueRun m (run n state) :=
  Control.Transition.run_add step n m state

/-- The language is pure: its evaluator has no externally answered events. -/
abbrev events : PFunctor.{0, 0} := Control.Transition.events

/-- Unbounded evaluation as a guarded interaction tree. -/
abbrev tree {r : ClosedTy} : MachineState r → ITree events (Outcome r) :=
  Control.Transition.tree step

/-- A finite successful execution, without fixing any fuel bound. -/
abbrev Terminates {r : ClosedTy} (state : MachineState r) (result : Outcome r) : Prop :=
  Control.Transition.Terminates step state result

end MachineState

/-- Initial evaluator configuration for a closed expression. -/
@[expose] def Expr.start {a : ClosedTy} (expression : Expr [] a) : MachineState a :=
  .eval expression .done

end Interop.Cryptol
