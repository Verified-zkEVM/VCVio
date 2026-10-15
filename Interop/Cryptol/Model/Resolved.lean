/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.NativePrimitives
public import PolyFun.IPFunctor.Scoped.Substitution

/-!
# Resolved syntax as an indexed polynomial

An index records the variable context and result type. Constructor heads carry
no recursive children; directions select children in their own context and
type, including under binders. The resulting indexed free tree is a resolved
AST boundary. Native primitive constants retain operator identity and let
bindings retain sharing. Direct source denotation and core lowering are separate
folds, related by a preservation theorem. No parser or Haskell decoder is modeled.
-/

public section

open OmegaCompletePartialOrder

namespace Interop.Cryptol.Resolved

/-- The typing judgment attached to each syntax node. -/
abbrev Scope := List ClosedTy × ClosedTy

/-- Constructor heads, with binders and implicit type arguments retained. -/
inductive Op : ClosedTy → Type where
  | sequence {a : ClosedTy} (n : Nat) : Op (.seq (.finite n) a)
  | primitive {a : ClosedTy} (p : Primitive a) : Op a
  | bit (value : Bool) : Op .bit
  | integer (value : Int) : Op .integer
  | unit : Op .unit
  | error {a : ClosedTy} (error : EvalError) : Op a
  | lam {a b : ClosedTy} : Op (.arrow a b)
  | app {a b : ClosedTy} : Op b
  | letE {a b : ClosedTy} : Op b
  | pair {a b : ClosedTy} : Op (.prod a b)
  | fst {a b : ClosedTy} : Op a
  | snd {a b : ClosedTy} : Op b
  | generate {a : ClosedTy} (length : Length) : Op (.seq length a)
  | index {a : ClosedTy} {length : Length} : Op a
  | ite {a : ClosedTy} : Op a
  | fix {a : ClosedTy} : Op a
  | bitNot : Op .bit
  | bitOp (op : BitOp) : Op .bit
  | intOp (op : IntOp) : Op .integer
  | intEq : Op .bit
  | intLt : Op .bit


/-- The finite number of recursive positions at a source node. -/
@[expose, reducible] def Op.arity : {a : ClosedTy} → Op a → Nat
  | _, .sequence n => n
  | _, .primitive _ | _, .bit _ | _, .integer _ | _, .unit | _, .error _ => 0
  | _, .lam | _, .fst | _, .snd | _, .generate _ | _, .fix | _, .bitNot => 1
  | _, .app | _, .letE | _, .pair | _, .index | _, .bitOp _ | _, .intOp _ |
      _, .intEq | _, .intLt => 2
  | _, .ite => 3

/-- Each child has its own context and result type; array elements share one scope. -/
@[expose, reducible] def Op.child : {a : ClosedTy} → (head : Op a) → Fin head.arity → Scope
  | _, @Op.sequence a _, _ => ([], a)
  | _, .primitive _, i | _, .bit _, i | _, .integer _, i |
      _, .unit, i | _, .error _, i => nomatch i
  | _, @Op.lam a b, _ => (a :: [], b)
  | _, @Op.app a b, i => Fin.cases ([], .arrow a b) (fun _ => ([], a)) i
  | _, @Op.letE a b, i => Fin.cases ([], a) (fun _ => (a :: [], b)) i
  | _, @Op.pair a b, i => Fin.cases ([], a) (fun _ => ([], b)) i
  | _, @Op.fst a b, _ | _, @Op.snd a b, _ => ([], .prod a b)
  | _, @Op.generate a _, _ => (.integer :: [], a)
  | _, @Op.index a l, i => Fin.cases ([], .seq l a) (fun _ => ([], .integer)) i
  | _, @Op.ite a, i => Fin.cases ([], .bit) (fun _ => ([], a)) i
  | _, @Op.fix a, _ => (a :: [], a)
  | _, @Op.bitNot, _ | _, @Op.bitOp _, _ => ([], .bit)
  | _, @Op.intOp _, _ | _, @Op.intEq, _ | _, @Op.intLt, _ => ([], .integer)

/-- Binding structure shared with other scoped polynomial languages. -/
@[expose, reducible] def syntaxSignature : IPFunctor.ScopedSignature ClosedTy where
  Op := Op
  Arg op := Fin op.arity
  binders op p := (op.child p).1
  sort op p := (op.child p).2

/-- Constructor heads at a complete typing judgment. -/
abbrev Head (s : Scope) := Op s.2

/-- The underlying indexed polynomial. -/
@[expose, reducible] def signature := syntaxSignature.polynomial

/-- Variables are leaves; all binding operations use the shared scoped carrier. -/
abbrev Term := syntaxSignature.Term

/-- Interpret one constructor in the operational core. -/
@[expose] def lowerOp (Γ : List ClosedTy) : {a : ClosedTy} → (op : Op a) →
    ((p : Fin op.arity) → Expr ((op.child p).1 ++ Γ) (op.child p).2) → Expr Γ a
  | _, @Op.sequence a n, next => .generate (.finite n) (.select
        ((List.finRange n).map (fun i => (next i).weaken)) (.var .zero))
  | _, .primitive p, _ => p.lower
  | _, .bit value, _ => .bit value
  | _, .integer value, _ => .integer value
  | _, .unit, _ => .unit
  | _, .error error, _ => .error error
  | _, .lam, next => .lam (next 0)
  | _, .app, next => .app (next 0) (next 1)
  | _, @Op.letE a _, next => .letE (a := a) (next 0) (next 1)
  | _, .pair, next => .pair (next 0) (next 1)
  | _, .fst, next => .fst (next 0)
  | _, .snd, next => .snd (next 0)
  | _, .generate length, next => .generate length (next 0)
  | _, .index, next => .index (next 0) (next 1)
  | _, .ite, next => .ite (next 0) (next 1) (next 2)
  | _, .fix, next => .fix (next 0)
  | _, .bitNot, next => .bitNot (next 0)
  | _, .bitOp op, next => .bitOp op (next 0) (next 1)
  | _, .intOp op, next => .intOp op (next 0) (next 1)
  | _, .intEq, next => .intEq (next 0) (next 1)
  | _, .intLt, next => .intLt (next 0) (next 1)

/-- Lower instantiated source syntax through the generic indexed fold. -/
@[expose] def lower {s : Scope}
    (t : IPFunctor.IFreeM signature (fun j => Var j.1 j.2) s) : Expr s.1 s.2 :=
  t.fold (D := fun j : Scope => Expr j.1 j.2) (fun _ v => .var v)
    (fun j op next => lowerOp j.1 op next)

/-- Interpret one constructor in continuous, lazy environment functions. -/
@[expose] noncomputable def denoteOp (Γ : List ClosedTy) : {a : ClosedTy} → (op : Op a) →
    ((p : Fin op.arity) → Environment ((op.child p).1 ++ Γ) →𝒄 Computation (op.child p).2) →
      Environment Γ →𝒄 Computation a
  | _, .sequence _, next => .ofFun (fun ρ => DomainResult.valueContinuous (fun i => next i ρ))
  | _, .primitive p, _ => .const p.denote
  | _, .bit b, _ => .const (.value ⟨b⟩)
  | _, .integer i, _ => .const (.value ⟨i⟩)
  | _, .unit, _ => .const (.value ⟨()⟩)
  | _, .error e, _ => .const (.error e)
  | _, .lam, next => DomainResult.valueContinuous.comp
        (ContinuousHom.curry ((next 0).comp Environment.extendContinuous))
  | _, .app, next => .ofFun (fun ρ => DomainResult.applyContinuous (next 0 ρ)
        (next 1 ρ))
  | _, .letE, next => .ofFun (fun ρ => next 1
        (Environment.extendContinuous (ρ, next 0 ρ)))
  | _, .pair, next => .ofFun (fun ρ => DomainResult.valueContinuous
        (next 0 ρ, next 1 ρ))
  | _, .fst, next => (DomainResult.bind (.ofFun Prod.fst)).comp (next 0)
  | _, .snd, next => (DomainResult.bind (.ofFun Prod.snd)).comp (next 0)
  | _, .generate l, next => .ofFun (fun ρ => DomainResult.valueContinuous (fun i : l.Index =>
        next 0 (Environment.extendContinuous
          (ρ, DomainResult.value ⟨(Length.indexNat i : Int)⟩))))
  | _, .index, next => .ofFun (fun ρ => Semantics.index (next 0 ρ) (next 1 ρ))
  | _, .ite, next => .ofFun (fun ρ => Semantics.conditional
        (next 1 ρ, next 2 ρ) (next 0 ρ))
  | _, .fix, next => ContinuousHom.fixContinuous.comp
        (ContinuousHom.curry ((next 0).comp Environment.extendContinuous))
  | _, .bitNot, next => Semantics.bitNot.comp (next 0)
  | _, .bitOp op, next => .ofFun (fun ρ => Semantics.binary (fun a b => .ok (op.eval a b))
        (next 0 ρ) (next 1 ρ))
  | _, .intOp op, next => .ofFun (fun ρ => Semantics.binary op.eval
        (next 0 ρ) (next 1 ρ))
  | _, .intEq, next => .ofFun (fun ρ => Semantics.binary (fun a b : Int => .ok (a == b))
        (next 0 ρ) (next 1 ρ))
  | _, .intLt, next => .ofFun (fun ρ => Semantics.binary (fun a b : Int => .ok (decide (a < b)))
        (next 0 ρ) (next 1 ρ))

/-- Source meaning is an independent fold into continuous maps. -/
@[expose] noncomputable def denote {s : Scope}
    (t : IPFunctor.IFreeM signature (fun j => Var j.1 j.2) s) :
    Environment s.1 →𝒄 Computation s.2 :=
  t.fold (D := fun j : Scope => Environment j.1 →𝒄 Computation j.2)
    (fun _ v => .ofFun (fun ρ => ρ _ v)) (fun j op next => denoteOp j.1 op next)

@[simp] theorem lower_node {Γ : List ClosedTy} {a : ClosedTy} (op : Op a)
    (args : (p : Fin op.arity) → Term ((op.child p).1 ++ Γ) (op.child p).2) :
    lower (IPFunctor.IFreeM.liftBind (s := (Γ, a)) op args) =
      lowerOp Γ op (fun p => lower (args p)) := rfl

@[simp] theorem denote_node {Γ : List ClosedTy} {a : ClosedTy} (op : Op a)
    (args : (p : Fin op.arity) → Term ((op.child p).1 ++ Γ) (op.child p).2) :
    denote (IPFunctor.IFreeM.liftBind (s := (Γ, a)) op args) =
      denoteOp Γ op (fun p => denote (args p)) := rfl

/-- Lowering preserves source meaning, including higher-order partial values. -/
theorem lower_correct {s : Scope} (term : IPFunctor.IFreeM signature (fun j => Var j.1 j.2) s) :
    (lower term).denote = denote term := by
  induction term with
  | pure v => rfl
  | @liftBind s head next ih =>
      rcases s with ⟨Γ, a⟩
      cases head with
      | sequence n =>
          apply DFunLike.ext
          intro η
          apply congrArg DomainResult.value
          funext i
          change (Expr.select _ (.var .zero)).denote
            (η.extend (.value ⟨(i.val : Int)⟩)) = _
          rw [Expr.denote_select _ _ i.val (by simp) _ rfl]
          simp only [List.getElem_map, Expr.denote_weaken]
          erw [List.getElem_finRange]
          exact DFunLike.congr_fun (ih i) η
      | primitive p =>
          apply DFunLike.ext
          intro η
          exact p.lower_correct η
      | _ =>
          simp only [lower_node, denote_node, lowerOp, denoteOp, Expr.denote]
          all_goals
            repeat erw [ih 0]
            all_goals first
            | rfl
            | apply DFunLike.ext
              intro η
              dsimp only [ContinuousHom.ofFun, ContinuousHom.coe_mk, OrderHom.coe_mk]
              repeat first | erw [ih 0] | erw [ih 1] | erw [ih 2]
              all_goals rfl

/-- Number of retained source nodes, without expanding primitive implementations. -/
@[expose] def nodeCount : {s : Scope} → IPFunctor.IFreeM signature (fun j => Var j.1 j.2) s → Nat
  | _, .pure _ => 1
  | _, .liftBind head next =>
      1 + ((List.finRange head.arity).map (fun i => nodeCount (next i))).sum

/-- Convert bare core descriptions when every constructor has a source spelling.
Native primitive lowerings contain force and must retain their source AST for export. -/
@[expose] def ofCore? {Γ : List (ClosedTy)} {a : ClosedTy} : Expr Γ a → Except String (Term Γ a)
  | .var index => do
      return .pure index
  | .bit value => do
      return .liftBind (.bit value) (fun impossible => nomatch impossible)
  | .integer value => do
      return .liftBind (.integer value) (fun impossible => nomatch impossible)
  | .unit => do
      return .liftBind (.unit) (fun impossible => nomatch impossible)
  | .error error => do
      return .liftBind (.error error) (fun impossible => nomatch impossible)
  | .lam e0 => do
      return .liftBind (.lam)
        (Fin.cases (← ofCore? e0) (fun impossible => nomatch impossible))
  | @Expr.app _ _ Γ a b e0 e1 => do
      return .liftBind (Op.app (a := a))
        (Fin.cases (← ofCore? e0)
        (Fin.cases (← ofCore? e1) (fun impossible => nomatch impossible)))
  | @Expr.letE _ _ Γ a b e0 e1 => do
      return .liftBind (Op.letE (a := a))
        (Fin.cases (← ofCore? e0)
        (Fin.cases (← ofCore? e1) (fun impossible => nomatch impossible)))
  | .pair e0 e1 => do
      return .liftBind (.pair)
        (Fin.cases (← ofCore? e0)
        (Fin.cases (← ofCore? e1) (fun impossible => nomatch impossible)))
  | @Expr.fst _ _ Γ a b e0 => do
      return .liftBind (Op.fst (b := b))
        (Fin.cases (← ofCore? e0) (fun impossible => nomatch impossible))
  | @Expr.snd _ _ Γ a b e0 => do
      return .liftBind (Op.snd (a := a))
        (Fin.cases (← ofCore? e0) (fun impossible => nomatch impossible))
  | .generate length e0 => do
      return .liftBind (.generate length)
        (Fin.cases (← ofCore? e0) (fun impossible => nomatch impossible))
  | @Expr.index _ _ Γ a length e0 e1 => do
      return .liftBind (Op.index (length := length))
        (Fin.cases (← ofCore? e0)
        (Fin.cases (← ofCore? e1) (fun impossible => nomatch impossible)))
  | .ite e0 e1 e2 => do
      return .liftBind (.ite)
        (Fin.cases (← ofCore? e0)
        (Fin.cases (← ofCore? e1)
          (Fin.cases (← ofCore? e2) (fun impossible => nomatch impossible))))
  | .fix e0 => do
      return .liftBind (.fix)
        (Fin.cases (← ofCore? e0) (fun impossible => nomatch impossible))
  | .bitNot e0 => do
      return .liftBind (.bitNot)
        (Fin.cases (← ofCore? e0) (fun impossible => nomatch impossible))
  | .bitOp op e0 e1 => do
      return .liftBind (.bitOp op)
        (Fin.cases (← ofCore? e0)
        (Fin.cases (← ofCore? e1) (fun impossible => nomatch impossible)))
  | .intOp op e0 e1 => do
      return .liftBind (.intOp op)
        (Fin.cases (← ofCore? e0)
        (Fin.cases (← ofCore? e1) (fun impossible => nomatch impossible)))
  | .intEq e0 e1 => do
      return .liftBind (.intEq)
        (Fin.cases (← ofCore? e0)
        (Fin.cases (← ofCore? e1) (fun impossible => nomatch impossible)))
  | .intLt e0 e1 => do
      return .liftBind (.intLt)
        (Fin.cases (← ofCore? e0)
        (Fin.cases (← ofCore? e1) (fun impossible => nomatch impossible)))
  | .force _ _ => .error "The internal force constructor has no Cryptol source operator"

/-- An explicitly checked conversion for statically known supported core syntax. -/
@[expose] def ofCore {Γ : List ClosedTy} {a : ClosedTy} (e : Expr Γ a)
    (supported : (ofCore? e).toOption.isSome = true) : Term Γ a :=
  (ofCore? e).toOption.get supported

namespace Term

variable {Γ : List ClosedTy} {a b : ClosedTy}

/-- An instantiated native primitive constant. -/
@[expose] def primitive (p : Primitive a) : Term Γ a :=
  .liftBind (.primitive p) (fun i => nomatch i)

/-- A typed variable. -/
@[expose] def var (v : Var Γ a) : Term Γ a :=
  .pure v

/-- A Boolean literal. -/
@[expose] def bit (b : Bool) : Term Γ .bit :=
  .liftBind (.bit b) (fun i => nomatch i)

/-- An integer literal. -/
@[expose] def integer (i : Int) : Term Γ .integer :=
  .liftBind (.integer i) (fun i => nomatch i)

/-- A finite word literal remains compact until lowering. -/
@[expose] def word {n : Nat} (x : BitVec n) : Term Γ (wordTy n) := primitive (.word x)

/-- An explicit source error. -/
@[expose] def error (e : EvalError) : Term Γ a :=
  .liftBind (.error e) (fun i => nomatch i)

/-- A source lambda binding a suspended argument. -/
@[expose] def lam (body : Term (a :: Γ) b) : Term Γ (.arrow a b) :=
  .liftBind .lam (Fin.cases body (fun i => nomatch i))

/-- Source application. -/
@[expose] def app (f : Term Γ (.arrow a b)) (x : Term Γ a) : Term Γ b :=
  .liftBind (.app (a := a)) (Fin.cases f (Fin.cases x (fun i => nomatch i)))

/-- A let binding preserves syntactic sharing through export. -/
@[expose] def letE (x : Term Γ a) (body : Term (a :: Γ) b) : Term Γ b :=
  .liftBind (.letE (a := a)) (Fin.cases x (Fin.cases body (fun i => nomatch i)))

/-- Lazy source pairing. -/
@[expose] def pair (x : Term Γ a) (y : Term Γ b) : Term Γ (.prod a b) :=
  .liftBind .pair (Fin.cases x (Fin.cases y (fun i => nomatch i)))

/-- A finite literal with suspended elements and no generated index-selection tree. -/
@[expose] def sequence (n : Nat) (items : Fin n → Term Γ a) : Term Γ (.seq (.finite n) a) :=
  .liftBind (.sequence n) items

/-- A source sequence generator. -/
@[expose] def generate (l : Length) (body : Term (.integer :: Γ) a) : Term Γ (.seq l a) :=
  .liftBind (.generate l) (Fin.cases body (fun i => nomatch i))

/-- Source indexing uses an integer index. Word indices compose with conversion. -/
@[expose] def index {l : Length} (xs : Term Γ (.seq l a)) (i : Term Γ .integer) : Term Γ a :=
  .liftBind (.index (length := l)) (Fin.cases xs (Fin.cases i (fun i => nomatch i)))

/-- A conditional demands just the chosen branch. -/
@[expose] def ite (p : Term Γ .bit) (x y : Term Γ a) : Term Γ a :=
  .liftBind .ite (Fin.cases p (Fin.cases x (Fin.cases y (fun i => nomatch i))))

/-- A recursive binding. -/
@[expose] def fix (body : Term (a :: Γ) a) : Term Γ a :=
  .liftBind .fix (Fin.cases body (fun i => nomatch i))

/-- First projection of a suspended pair. -/
@[expose] def fst (x : Term Γ (.prod a b)) : Term Γ a :=
  .liftBind (.fst (b := b)) (Fin.cases x (fun i => nomatch i))

/-- Second projection of a suspended pair. -/
@[expose] def snd (x : Term Γ (.prod a b)) : Term Γ b :=
  .liftBind (.snd (a := a)) (Fin.cases x (fun i => nomatch i))

/-- Scalar complement. -/
@[expose] def bitNot (x : Term Γ .bit) : Term Γ .bit :=
  .liftBind .bitNot (Fin.cases x (fun i => nomatch i))

/-- Strict scalar logic. -/
@[expose] def bitOp (op : BitOp) (x y : Term Γ .bit) : Term Γ .bit :=
  .liftBind (.bitOp op) (Fin.cases x (Fin.cases y (fun i => nomatch i)))

/-- Scalar integer arithmetic. -/
@[expose] def intOp (op : IntOp) (x y : Term Γ .integer) : Term Γ .integer :=
  .liftBind (.intOp op) (Fin.cases x (Fin.cases y (fun i => nomatch i)))

/-- Integer equality. -/
@[expose] def intEq (x y : Term Γ .integer) : Term Γ .bit :=
  .liftBind .intEq (Fin.cases x (Fin.cases y (fun i => nomatch i)))

/-- Integer comparison. -/
@[expose] def intLt (x y : Term Γ .integer) : Term Γ .bit :=
  .liftBind .intLt (Fin.cases x (Fin.cases y (fun i => nomatch i)))

/-- Unsigned word conversion. -/
@[expose] def toInteger {n : Nat} (x : Term Γ (wordTy n)) : Term Γ .integer :=
  app (primitive (.toInteger n)) x

/-- Modular integer conversion. -/
@[expose] def fromInteger (n : Nat) (x : Term Γ .integer) : Term Γ (wordTy n) :=
  app (primitive (.fromInteger n)) x

/-- Native word logic application. -/
@[expose] def wordLogic {n : Nat} (op : BitOp) (x y : Term Γ (wordTy n)) : Term Γ (wordTy n) :=
  app (app (primitive (.wordLogic n op)) x) y

/-- Native word arithmetic application. -/
@[expose] def wordArithmetic {n : Nat} (op : IntOp) (x y : Term Γ (wordTy n)) : Term Γ (wordTy n) :=
  app (app (primitive (.wordArithmetic n op)) x) y

/-- Dynamic source shift or rotation. -/
@[expose] def shift {n : Nat} (op : ShiftOp) (x : Term Γ (wordTy n))
    (k : Term Γ .integer) : Term Γ (wordTy n) := app (app (primitive (.shift n op)) x) k

/-- Word-valued amounts use unsigned conversion and demand every amount bit first. -/
@[expose] def shiftWord {n m : Nat} (op : ShiftOp) (x : Term Γ (wordTy n))
    (k : Term Γ (wordTy m)) : Term Γ (wordTy n) := shift op x (toInteger k)

/-- Modular negation expressed by the native subtraction primitive. -/
@[expose] def wordNeg {n : Nat} (x : Term Γ (wordTy n)) : Term Γ (wordTy n) :=
  wordArithmetic .sub (word 0) x

end Term

end Interop.Cryptol.Resolved
