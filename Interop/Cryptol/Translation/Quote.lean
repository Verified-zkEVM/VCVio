/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Translation.FiniteSource
public meta import Lean

/-!
# Named quotation of finite descriptions

`[cryptol| fun x => let y := rotr x 7; y ^ x]` builds a typed finite
description. Names are resolved lexically, including shadowing; unbound names
are rejected. The expected `Finite.Term` type supplies word widths. This is
a small Lean quotation language, not a parser for Cryptol source files.
-/

public meta section

namespace Interop.Cryptol

open Lean

/-- A finite description with lexical term binders. -/
declare_syntax_cat cryptolTerm
/-- A reference to the nearest enclosing binder with this name. -/
syntax ident : cryptolTerm
/-- A word literal whose width comes from the expected type. -/
syntax num : cryptolTerm
/-- Parenthesized finite quotation. -/
syntax "(" cryptolTerm ")" : cryptolTerm
/-- A named lambda in the finite description. -/
syntax "fun " ident " => " cryptolTerm : cryptolTerm
/-- A lazy source let, retained as a binding during export. -/
syntax "let " ident " := " cryptolTerm "; " cryptolTerm : cryptolTerm
/-- Modular word addition. -/
syntax:65 cryptolTerm:65 " + " cryptolTerm:66 : cryptolTerm
/-- Modular word subtraction. -/
syntax:65 cryptolTerm:65 " - " cryptolTerm:66 : cryptolTerm
/-- Modular word multiplication. -/
syntax:70 cryptolTerm:70 " * " cryptolTerm:71 : cryptolTerm
/-- Word exclusive-or. -/
syntax:60 cryptolTerm:60 " ^ " cryptolTerm:61 : cryptolTerm
/-- Word conjunction. -/
syntax:70 cryptolTerm:70 " &&& " cryptolTerm:71 : cryptolTerm
/-- Word disjunction. -/
syntax:65 cryptolTerm:65 " ||| " cryptolTerm:66 : cryptolTerm
/-- Word complement. -/
syntax:80 "~~~" cryptolTerm:80 : cryptolTerm
/-- Fixed right rotation. -/
syntax:80 "rotr " cryptolTerm:81 num : cryptolTerm
/-- Fixed left rotation. -/
syntax:80 "rotl " cryptolTerm:81 num : cryptolTerm
/-- Fixed logical right shift. -/
syntax:80 "shr " cryptolTerm:81 num : cryptolTerm
/-- Fixed logical left shift. -/
syntax:80 "shl " cryptolTerm:81 num : cryptolTerm
/-- Quote a finite description using lexical names. -/
syntax "[cryptol| " cryptolTerm "]" : term

private def quoteVar : Nat → MacroM (TSyntax `term)
  | 0 => `(Var.zero)
  | n + 1 => do `(Var.succ $(← quoteVar n))

private partial def quoteTerm (names : List Name) (stx : TSyntax `cryptolTerm) :
    MacroM (TSyntax `term) := do
  match stx with
  | `(cryptolTerm| $x:ident) =>
      match names.idxOf? x.getId with
      | some i => `(Finite.Term.var $(← quoteVar i))
      | none => Macro.throwErrorAt x "unbound quoted variable"
  | `(cryptolTerm| $n:num) => `(Finite.Term.word (BitVec.ofNat _ $n))
  | `(cryptolTerm| ($x)) => quoteTerm names x
  | `(cryptolTerm| fun $x:ident => $body) =>
      `(Finite.Term.lam $(← quoteTerm (x.getId :: names) body))
  | `(cryptolTerm| let $x:ident := $rhs; $body) =>
      `(Finite.Term.letE $(← quoteTerm names rhs) $(← quoteTerm (x.getId :: names) body))
  | `(cryptolTerm| $x + $y) =>
      `(Finite.Term.arithmetic .add $(← quoteTerm names x) $(← quoteTerm names y))
  | `(cryptolTerm| $x - $y) =>
      `(Finite.Term.arithmetic .sub $(← quoteTerm names x) $(← quoteTerm names y))
  | `(cryptolTerm| $x * $y) =>
      `(Finite.Term.arithmetic .mul $(← quoteTerm names x) $(← quoteTerm names y))
  | `(cryptolTerm| $x ^ $y) =>
      `(Finite.Term.wordOp .xor $(← quoteTerm names x) $(← quoteTerm names y))
  | `(cryptolTerm| $x &&& $y) =>
      `(Finite.Term.wordOp .and $(← quoteTerm names x) $(← quoteTerm names y))
  | `(cryptolTerm| $x ||| $y) =>
      `(Finite.Term.wordOp .or $(← quoteTerm names x) $(← quoteTerm names y))
  | `(cryptolTerm| ~~~$x) => `(Finite.Term.wordNot $(← quoteTerm names x))
  | `(cryptolTerm| rotr $x $k:num) => `(Finite.Term.rotateRight $k $(← quoteTerm names x))
  | `(cryptolTerm| rotl $x $k:num) => `(Finite.Term.rotateLeft $k $(← quoteTerm names x))
  | `(cryptolTerm| shr $x $k:num) => `(Finite.Term.shiftRight $k $(← quoteTerm names x))
  | `(cryptolTerm| shl $x $k:num) => `(Finite.Term.shiftLeft $k $(← quoteTerm names x))
  | _ => Macro.throwUnsupported

macro_rules
  | `([cryptol| $body]) => quoteTerm [] body

end Interop.Cryptol
