/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Expectation
public import VCVio.Prelude.Core
public meta import Lean.PrettyPrinter.Formatter
public meta import Lean.Elab.PatternVar

/-!
# Elaboration of the event and expectation notations

`Pr{items}[t]` and `𝔼{items}[b]` translate a `do`-style sequence of draws into nested core
weakest preconditions under the expectation interpretation of each draw's monad:

| item | term |
|---|---|
| `let x ← e` (also `let x : τ ← e`, `let _ ← e`, a bare action `e`) | `wp⟦e⟧ fun x => K` |
| `let pat ← e` | `wp⟦e⟧ fun z => match z with \| pat => K` |
| `let x := v`, `have h : p := v` | `let x := v; K`, `have h : p := v; K` |
| `let x ← do …`, `let x ← if …`, … (a nested `do` element) | the draw `let x ← (do …)` |
| a right-hand side with a nested action `(← g)` | the draw `let x ← (do e)` |
| an imperative tail (`let mut`, `for`, a do-level `if`, …) | `wp⟦do tail; pure tup⟧ fun pat => V` |

`K` is the translation of the remaining items and `V` the innermost observation: `predInd p` for
an event `[p xₙ]`, and the value for an expectation, folded to `predInd` when it is an indicator
`propInd t`. Nothing is rewritten at elaboration: the term is the translation, and the normal
form of `simp only [expect_norm]` is a proof-time notion. An imperative tail is one program whose
result is the tuple of the variables it binds, observed from outside, so no `return` reaches the
observation; a `return` at the top level of the braces is rejected.

Each draw is read in the expectation interpretation of its own monad, so a sequence may draw from
several monads (an `OptionT ProbComp` adversary inside a `ProbComp` game), and the failure of a
draw contributes nothing to the event. A draw whose monad its own term does not determine is
elaborated in the monad of the first draw that determined one.
-/

public section

open MeasureTheory
open scoped ENNReal

/-- Probability of a successful event after a `do`-style sequence of draws, as in
`Pr{let x ← mx; let y ← my x}[p y]`: the expectation `𝔼{let x ← mx; let y ← my x}[𝟙⟦p y⟧]` of
the event's indicator. -/
syntax (name := prEventStx) "Pr{" doSeq "}[" term "]" : term

/-- Expectation of a nonnegative value after a `do`-style sequence of draws, as in
`𝔼{let x ← mx; let y ← my x}[f x y]`: the nested core weakest preconditions of the draws under
the expectation interpretation. -/
syntax (name := expectStx) "𝔼{" doSeq "}[" term "]" : term

public meta section Formatting

open Lean PrettyPrinter Formatter Syntax.MonadTraverser

/-- Format a `do` sequence directly after its opening delimiter `opening`, its statements
separated by `; ` and soft line breaks, so that a short sequence stays on one line. Explicitly
braced sequences keep the ordinary Lean formatter, and explicit line breaks after the opening
delimiter are preserved. -/
def seqFormatter (opening : String) : Formatter := do
  let stx ← getCur
  let multiline := match stx[0].getTailInfo with
    | .original _ _ trailing _ => trailing.contains '\n'
    | _ => false
  visitArgs do
    symbolNoAntiquot.formatter "]"
    categoryParser.formatter `term
    symbolNoAntiquot.formatter "}["
    let seq ← getCur
    if seq.isOfKind ``Lean.Parser.Term.doSeqIndent then
      let n := seq[0].getArgs.size
      group <| indent <| visitArgs <| visitArgs do
        for i in [:n] do
          visitArgs do
            optionalNoAntiquot.formatter (symbolNoAntiquot.formatter "; ")
            categoryParser.formatter `doElem
          if i + 1 < n then pushLine
    else
      formatterForKind seq.getKind
    if multiline then
      pushWhitespace "\n"
    symbolNoAntiquot.formatter opening

/-- Format an event as its `do` sequence and event. -/
@[formatter prEventStx]
def prEventFormatter : Formatter := seqFormatter "Pr{"

/-- Format an expectation as its `do` sequence and observed value. -/
@[formatter expectStx]
def expectFormatter : Formatter := seqFormatter "𝔼{"

end Formatting

public meta section Elaboration

open Lean Elab Term Meta

namespace ProbabilityNotation

/-- Internal form of the expectation notation, with the monad of the sequence once a draw has
determined it. -/
syntax (name := expectElabStx) "expect% " (atomic("(" &"m" " := ") term ")")?
  "{" doSeq "}[" term "]" : term

/-- Internal form of the event notation, with the monad of the sequence once a draw has
determined it. -/
syntax (name := prEventElabStx) "prEvent% " (atomic("(" &"m" " := ") term ")")?
  "{" doSeq "}[" term "]" : term

/-- The binder of a draw. -/
inductive Binder where
  /-- `let x ← e`, with an optional type ascription. -/
  | ident (x : Ident) (ty? : Option Term)
  /-- `let _ ← e`, or a bare action. -/
  | hole
  /-- `let pat ← e`: the value is matched on `pat`. -/
  | pat (p : Term) (ty? : Option Term)

/-- One item of the sequence, classified. -/
inductive Item where
  /-- A draw, with its right-hand side as a term. -/
  | draw (b : Binder) (rhs : Term)
  /-- `let x := v`, as its `letDecl`. -/
  | letDecl (decl : TSyntax ``Lean.Parser.Term.letDecl)
  /-- `have …`, as its `letDecl`. -/
  | have (decl : TSyntax ``Lean.Parser.Term.letDecl)
  /-- Anything else: the start of an imperative tail. -/
  | tail
  deriving Inhabited

/-- The syntax kinds out of which `do` does not lift a nested action. -/
def nestedActionDelimiter (k : SyntaxNodeKind) : Bool :=
  k == ``Lean.Parser.Term.do || k == ``Lean.Parser.Term.doSeqIndent ||
    k == ``Lean.Parser.Term.doSeqBracketed || k == ``Lean.Parser.Term.termReturn ||
    k == ``Lean.Parser.Term.termUnless || k == ``Lean.Parser.Term.termTry ||
    k == ``Lean.Parser.Term.termFor

/-- Whether `stx` contains a nested action `(← e)` that `do` would lift out of it. -/
partial def hasNestedAction (stx : Syntax) : Bool :=
  if nestedActionDelimiter stx.getKind then false
  else if stx.isOfKind ``Lean.Parser.Term.nestedAction then true
  else stx.getArgs.any hasNestedAction

/-- The right-hand side of a draw as a term: a plain term; a term with a nested action wrapped in
`do`, so that Lean lifts the action inside the draw; and any other `do` element (a nested `do`,
an `if`, a `match`, a loop) as one nested program. -/
def rhsTerm (action : Syntax) : MacroM Term := do
  if action.isOfKind ``Lean.Parser.Term.doExpr then
    let t : Term := ⟨action[0]⟩
    if hasNestedAction t.raw then `((do $t:term)) else pure t
  else if action.isOfKind ``Lean.Parser.Term.doNested then
    `((do $(⟨action[1]⟩):doSeq))
  else
    `((do $(⟨action⟩):doElem))

/-- Classify a `doSeqItem`. -/
def classify (item : TSyntax ``Lean.Parser.Term.doSeqItem) : MacroM Item := do
  let elem := item.raw[0]
  if elem.isOfKind ``Lean.Parser.Term.doLetArrow then
    unless elem[1].isNone do return .tail
    let decl := elem[3]
    let ty? : Option Term := if decl[1].isNone then none else some ⟨decl[1][0][1]⟩
    if decl.isOfKind ``Lean.Parser.Term.doIdDecl then
      return .draw (.ident ⟨decl[0]⟩ ty?) (← rhsTerm decl[3])
    if decl.isOfKind ``Lean.Parser.Term.doPatDecl then
      unless decl[4].isNone do return .tail
      let pat : Term := ⟨decl[0]⟩
      let rhs ← rhsTerm decl[3]
      if pat.raw.isOfKind ``Lean.Parser.Term.hole then return .draw .hole rhs
      return .draw (.pat pat ty?) rhs
    return .tail
  if elem.isOfKind ``Lean.Parser.Term.doLet then
    unless elem[1].isNone do return .tail
    return .letDecl ⟨elem[3]⟩
  if elem.isOfKind ``Lean.Parser.Term.doHave then
    return .have ⟨elem[2]⟩
  if elem.isOfKind ``Lean.Parser.Term.doExpr then
    return .draw .hole (← rhsTerm elem)
  if elem.isOfKind ``Lean.Parser.Term.doNested then
    return .draw .hole (← rhsTerm elem)
  return .tail

/-- Whether an item is a pure `let` or `have`. -/
def Item.isPure : Item → Bool
  | .letDecl _ | .have _ => true
  | _ => false

/-- A `return` in `stx` that would exit the braces: one not inside a nested term-level `do`. -/
partial def hasTopLevelReturn (stx : Syntax) : Bool :=
  if stx.isOfKind ``Lean.Parser.Term.doReturn || stx.isOfKind ``Lean.Parser.Term.termReturn then
    true
  else if stx.isOfKind ``Lean.Parser.Term.do then false
  else stx.getArgs.any hasTopLevelReturn

/-- The variables an imperative tail binds at its top level, in order. -/
def tailBinders (items : Array (TSyntax ``Lean.Parser.Term.doSeqItem)) :
    TermElabM (Array Ident) := do
  let mut vars : Array Ident := #[]
  for item in items do
    let elem := item.raw[0]
    let mut new : Array Ident := #[]
    if elem.isOfKind ``Lean.Parser.Term.doLet then
      let decl := elem[3][0]
      if decl.isOfKind ``Lean.Parser.Term.letIdDecl then
        let id := if decl[0].isOfKind ``Lean.Parser.Term.letId then decl[0][0] else decl[0]
        if id.isIdent then new := #[⟨id⟩]
      else if decl.isOfKind ``Lean.Parser.Term.letPatDecl then
        new := (← getPatternVarNames <$> getPatternVars decl[0]).map mkIdent
    else if elem.isOfKind ``Lean.Parser.Term.doLetArrow then
      let decl := elem[3]
      if decl.isOfKind ``Lean.Parser.Term.doIdDecl then
        new := #[⟨decl[0]⟩]
      else if decl.isOfKind ``Lean.Parser.Term.doPatDecl then
        unless decl[0].isOfKind ``Lean.Parser.Term.hole do
          new := (← getPatternVarNames <$> getPatternVars decl[0]).map mkIdent
    else if elem.isOfKind ``Lean.Parser.Term.doLetElse then
      new := (← getPatternVarNames <$> getPatternVars elem[3]).map mkIdent
    for v in new do
      vars := (vars.filter (·.getId != v.getId)).push v
  return vars

/-- The tuple of the variables and the pattern that matches it. -/
def mkTuple (vars : Array Ident) : MacroM (Term × Term) := do
  match vars.toList with
  | [] => return (← `(()), ← `(_))
  | [v] => return (v, v)
  | vs =>
    let rec go : List Ident → MacroM Term
      | [] => `(())
      | [v] => pure v
      | v :: vs => do `(($v, $(← go vs)))
    let t ← go vs
    return (t, t)

/-- The predicate of an indicator observation, eta-reduced: `fun x => p x` for an observation
`fun x => propInd (p x)`, and `fun b => b` for `propInd`. -/
def indicatorPred? (g : Expr) : Option Expr :=
  match g.cleanupAnnotations with
  | .lam n ty b bi =>
    let b := b.cleanupAnnotations
    if b.isAppOfArity ``propInd 1 then some (Expr.lam n ty b.appArg! bi).eta else none
  | .const ``propInd _ => some (.lam `b (.sort .zero) (.bvar 0) .default)
  | _ => none

/-- The expectation interpretation of the monad of a draw (`ExpectationWP`), or a postponement
while the monad cannot be determined, or an error naming what is missing. The interpretation is
elaborated as the `wp⟦ ⟧` macro elaborates it, and the state is restored afterwards. -/
def checkMeasureSemantics (m : Expr) : TermElabM Unit := do
  let found ← if (← instantiateMVars m).hasExprMVar then pure false else do
    let s ← saveState
    try
      let e ← withSynthesize (postpone := .no) <|
        elabTerm (← `(ExpectationWP.toWPMonad (m := $(← exprToSyntax m)))) none
      let ok := !(← instantiateMVars e).hasExprMVar
      s.restore
      pure ok
    catch _ =>
      s.restore
      pure false
  unless found do
    if (← instantiateMVars m).hasMVar then tryPostpone
    throwError m!"an expectation needs an expectation interpretation of its monad \
      (`ExpectationWP`): lawful measure semantics (`EvalDistSemantics`, \
      `LawfulEvalDistSemantics`, `LawfulMonad`), or `OptionT` / `ExceptT` over such a monad; \
      none for{indentExpr m}"

/-- The monad and result type of a draw `a`, when its type determines them: the head of the type
as written, never unfolded. -/
def determined? (a : Expr) : TermElabM (Option (Expr × Expr × Expr)) := do
  let ty ← instantiateMVars (← inferType (← instantiateMVars a))
  let ty ← if ty.isApp then pure ty else whnfR ty
  unless ty.isApp && !ty.appFn!.hasExprMVar do return none
  return some (a, ty.appFn!, ty.appArg!)

/-- Elaborate the right-hand side of a draw: on its own first, reading its monad off its type as
written; then, when that leaves the monad undetermined, in the monad of the sequence; then
without postponing, which lets a nested `do`, `if` or `match` fix its monad from its own binds.
Returns the draw, its monad and its result type, or postpones. -/
def elabDraw (hint? : Option Expr) (rhs : Term) (ty? : Option Term) :
    TermElabM (Expr × Expr × Expr) := do
  let s ← saveState
  let a ← withSynthesize (postpone := .yes) <| elabTerm rhs none
  if let some r ← determined? a then return r
  if let some m₀ := hint? then
    s.restore
    let α ← match ty? with
      | some ty => elabType ty
      | none => mkFreshTypeMVar
    let a ← withSynthesize (postpone := .yes) <| elabTerm rhs (some (mkApp m₀ α))
    if let some r ← determined? a then return r
  -- The surrounding term may still determine the draw, as a `let`-bound `do` block whose monad
  -- its own binds fix does once that block is forced; the draw's own binds are forced only when
  -- nothing outside can postpone any longer.
  s.restore
  tryPostpone
  let a ← withSynthesize (postpone := .yes) <| withoutPostponing <| elabTerm rhs none
  if let some r ← determined? a then return r
  throwErrorAt rhs m!"cannot determine the monad of the draw{indentD rhs}\n\
    ascribe it, as in `(… : ProbComp _)`, or draw first from a computation whose monad is known"

/-- The expectation of `g` over the draw `a`: core's `wp` under the expectation interpretation
of `a`'s monad, spelled as the `wp⟦ ⟧` macro spells it. -/
def mkExpectation (a g : Expr) : TermElabM Expr := do
  let ennreal := Lean.mkConst ``ENNReal
  withSynthesize <| elabTermEnsuringType
    (← `(wp⟦$(← exprToSyntax a)⟧ $(← exprToSyntax g))) ennreal

/-- The innermost observation as a function of the last binder: for an event, `predInd` of the
predicate, eta-reduced; for an expectation, the value, folded to `predInd` when it is an
indicator. `pureItems` are pure `let`s and `have`s that scope over the value. -/
def mkInnermost (binderStx : Term) (α : Expr) (pureItems : Array Item) (val : Term)
    (event : Bool) : TermElabM Expr := do
  let body ← pureItems.foldrM (init := val) fun item acc => do
    match item with
    | .letDecl decl => `(let $decl:letDecl; $acc)
    | .have decl => `(have $decl:letDecl; $acc)
    | _ => pure acc
  if event then
    let p ← elabTermEnsuringType (← `(fun $binderStx => ($body : Prop)))
      (← mkArrow α (mkSort .zero))
    mkAppM ``predInd #[(← instantiateMVars p).eta]
  else
    let g ← elabTermEnsuringType (← `(fun $binderStx => ($body : ENNReal)))
      (← mkArrow α (Lean.mkConst ``ENNReal))
    let g := (← instantiateMVars g).eta
    match indicatorPred? g with
    | some p => mkAppM ``predInd #[p]
    | none => pure g

/-- The binder syntax of a draw for a `fun`. -/
def Binder.funBinder : Binder → MacroM Term
  | .ident x none => pure x
  | .ident x (some ty) => `(($x : $ty))
  | .hole => `(_)
  | .pat _ _ => `(z)

/-- Elaborate the sequence `items` observed by `val`. -/
partial def elabSeq (hint? : Option Expr) (items : Array (TSyntax ``Lean.Parser.Term.doSeqItem))
    (val : Term) (event : Bool) : TermElabM Expr := do
  let classified ← items.mapM fun i => liftMacroM (classify i)
  let hintStx? ← hint?.mapM exprToSyntax
  let reenter (rest : Array (TSyntax ``Lean.Parser.Term.doSeqItem)) : TermElabM Term := do
    if event then `(prEvent% $[(m := $hintStx?)]? {$rest*}[$val])
    else `(expect% $[(m := $hintStx?)]? {$rest*}[$val])
  let ennreal := Lean.mkConst ``ENNReal
  -- Leading pure items scope over the rest of the sequence.
  let k := classified.findIdx? (!·.isPure) |>.getD classified.size
  if k == classified.size then
    throwError "an event needs a draw: the braces hold only `let`s"
  if k > 0 then
    let inner ← reenter items[k:]
    let body ← (classified[:k]).toArray.foldrM (init := inner) fun item acc => do
      match item with
      | .letDecl decl => `(let $decl:letDecl; $acc)
      | .have decl => `(have $decl:letDecl; $acc)
      | _ => pure acc
    return ← elabTermEnsuringType body ennreal
  match classified[0]! with
  | .draw b rhs =>
    let ty? := match b with
      | .ident _ ty? | .pat _ ty? => ty?
      | .hole => none
    let (a, m, α) ← elabDraw hint? rhs ty?
    checkMeasureSemantics m
    let hint := hint?.getD m
    let rest := items[1:].toArray
    let restC := classified[1:].toArray
    let binderStx ← liftMacroM b.funBinder
    let g ← if restC.all (·.isPure) then
        match b with
        | .pat pat _ =>
          -- The value is matched on the pattern: the observation is a function of the draw.
          let inner ← mkInnermostPat pat restC
          elabTermEnsuringType inner (← mkArrow α ennreal)
        | _ => mkInnermost binderStx α restC val event
      else
        let hintStx ← exprToSyntax hint
        let inner ← if event then `(prEvent% (m := $hintStx) {$rest*}[$val])
          else `(expect% (m := $hintStx) {$rest*}[$val])
        let cont ← match b with
          | .pat pat _ => `(fun z => match z with | $pat:term => $inner)
          | _ => `(fun $binderStx => $inner)
        elabTermEnsuringType cont (← mkArrow α ennreal)
    mkExpectation a g
  | .tail =>
    if items.any (hasTopLevelReturn ·.raw) then
      throwError "`return` is not allowed at the top level of the braces: the sequence's \
        bindings are what the event observes; bind a computation that returns early as \
        `let x ← (do …)`"
    let vars ← tailBinders items
    let (tup, tupPat) ← liftMacroM (mkTuple vars)
    let prog ← `((do $items:doSeqItem* pure $tup))
    let (a, m, β) ← elabDraw hint? prog none
    checkMeasureSemantics m
    let body ← if event then `(propInd ($val : Prop)) else pure val
    let g ← elabTermEnsuringType (← `(fun $tupPat => ($body : ENNReal))) (← mkArrow β ennreal)
    let g := (← instantiateMVars g).eta
    let g ← match indicatorPred? g with
      | some p => mkAppM ``predInd #[p]
      | none => pure g
    mkExpectation a g
  | _ => unreachable!
where
  /-- The observation after a final pattern draw: a `match` on the drawn value. -/
  mkInnermostPat (pat : Term) (pureItems : Array Item) : TermElabM Term := do
    let body ← pureItems.foldrM (init := val) fun item acc => do
      match item with
      | .letDecl decl => `(let $decl:letDecl; $acc)
      | .have decl => `(have $decl:letDecl; $acc)
      | _ => pure acc
    if event then `(predInd fun z => match z with | $pat:term => ($body : Prop))
    else `(fun z => match z with | $pat:term => ($body : ENNReal))

end ProbabilityNotation

elab_rules : term
  | `(expect% $[(m := $h)]? {$items*}[$b]) => do
    ProbabilityNotation.elabSeq (← h.mapM (elabTerm · none)) items b (event := false)
  | `(prEvent% $[(m := $h)]? {$items*}[$t]) => do
    ProbabilityNotation.elabSeq (← h.mapM (elabTerm · none)) items t (event := true)

end Elaboration

macro_rules (kind := prEventStx)
  | `(Pr{{$items*}}[$t]) => `((prEvent% {$items*}[$t] : ENNReal))
  | `(Pr{$items*}[$t]) => `((prEvent% {$items*}[$t] : ENNReal))

macro_rules (kind := expectStx)
  | `(𝔼{{$items*}}[$b]) => `((expect% {$items*}[$b] : ENNReal))
  | `(𝔼{$items*}[$b]) => `((expect% {$items*}[$b] : ENNReal))
