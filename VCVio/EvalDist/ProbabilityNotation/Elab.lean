/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Expectation
public import VCVio.Prelude.Core
public meta import Lean.PrettyPrinter.Formatter

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
`Pr{let x ← mx; let y ← my x}[p y]`: the expectation `𝔼{let x ← mx; let y ← my x}[propInd (p y)]` of
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

namespace VCVio.ProbabilityNotation

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
  /-- `let _ ← e`, with an optional type ascription, or a bare action. -/
  | hole (ty? : Option Term)
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
      if pat.raw.isOfKind ``Lean.Parser.Term.hole then return .draw (.hole ty?) rhs
      return .draw (.pat pat ty?) rhs
    return .tail
  if elem.isOfKind ``Lean.Parser.Term.doLet then
    unless elem[1].isNone do return .tail
    return .letDecl ⟨elem[3]⟩
  if elem.isOfKind ``Lean.Parser.Term.doHave then
    return .have ⟨elem[2]⟩
  if elem.isOfKind ``Lean.Parser.Term.doExpr then
    return .draw (.hole none) (← rhsTerm elem)
  if elem.isOfKind ``Lean.Parser.Term.doNested then
    return .draw (.hole none) (← rhsTerm elem)
  return .tail

/-- Whether an item is a pure `let` or `have`. -/
def Item.isPure : Item → Bool
  | .letDecl _ | .have _ => true
  | _ => false

/-- A `return` in `stx` that would exit the braces: one not inside a nested term-level `do`. -/
partial def hasTopLevelReturn (stx : Syntax) : MacroM Bool := do
  if stx.isOfKind ``Lean.Parser.Term.doReturn || stx.isOfKind ``Lean.Parser.Term.termReturn then
    return true
  if stx.isOfKind ``Lean.Parser.Term.do then return false
  if let some expanded ← expandMacro? stx then return ← hasTopLevelReturn expanded
  stx.getArgs.anyM hasTopLevelReturn

/-- The end of an imperative tail, `tailScope% n observing obs`: the tuple of the variables the
tail binds, read off the local context at the end of the tail. A variable is one of local-context
index at least `n` (the size of the context before the tail) under its innermost binding, so
`have`, shadowing, reassignment and macro-produced binders are seen as ordinary `do` sees them. A
binding with macro scopes is returned when the observation names it, so a hygienic binding of a
macro is observed by that macro's own event. A proof, a type, or a value whose type mentions
another tail variable cannot be returned, and the observation is resolved here, at the end of the
tail, under its expected type (`obs` is ascribed `Prop` or `ℝ≥0∞`), to check it reads none. The
tuple is annotated with the names; `obs` is carried for this, for its identifiers and for source
positions. -/
syntax (name := tailScopeStx) "tailScope% " num " observing " term : term

/-- The metadata key of the names returned by `tailScope%`. -/
def tailScopeKey : Name := `VCVio.ProbabilityNotation.tailScope

/-- An identifier in `obs` naming `n`, or a field of it: the same macro scopes and a name
extending `n`'s. -/
def findMention? (obs : Syntax) (n : Name) : Option Syntax :=
  let v := extractMacroScopes n
  obs.find? fun s =>
    s.isIdent &&
      let w := extractMacroScopes s.getId
      w.scopes == v.scopes && w.ctx == v.ctx && w.imported == v.imported &&
        v.name.isPrefixOf w.name

/-- Elaborate `tailScope% n observing obs`. -/
def elabTailScope (n : Nat) (obs : Term) : TermElabM Expr := do
  let lctx ← getLCtx
  let isTailVar (f : FVarId) : Bool := (lctx.find? f).any (·.index ≥ n)
  let mut seen : NameSet := {}
  let mut vars : Array LocalDecl := #[]
  -- The index of the first binding of each name: reassigning a mutable variable rebinds it,
  -- and the tuple keeps the variables in the order they were introduced.
  let mut first : Std.HashMap Name Nat := {}
  let mut i := lctx.numIndices
  while i > n do
    i := i - 1
    let some decl := lctx.getAt? i | continue
    if decl.isImplementationDetail then continue
    if decl.userName.hasMacroScopes && (findMention? obs decl.userName).isNone then continue
    first := first.insert decl.userName i
    if seen.contains decl.userName then continue
    seen := seen.insert decl.userName
    let ty ← instantiateMVars decl.type
    unless (← isProp ty) || (← whnfD ty).isSort || ty.hasAnyFVar isTailVar do
      vars := vars.push decl
  let observed := vars.qsort fun a b => first[a.userName]! < first[b.userName]!
  -- The observation is elaborated outside, over the returned variables. Resolving it here, where
  -- ordinary `do` would, shows which bindings it reads; a tail binding it reads that is not
  -- returned would be seen outside as an outer variable or a constant of the same name. `obs`
  -- carries its expected type and its elaboration is completed, so it resolves here as it will
  -- outside; a resolution that fails is reported, never passed over.
  let hidden (d : LocalDecl) : Bool :=
    d.index ≥ n && !d.isImplementationDetail && !observed.any (·.fvarId == d.fvarId)
  let reject (d : LocalDecl) : TermElabM Unit := do
    let (what, ty) := if d.userName.hasMacroScopes
      then (m!"an unnamed binding", m!", here{indentExpr d.type}")
      else (m!"`{d.userName}`", m!"")
    throwErrorAt ((findMention? obs d.userName).getD obs) m!"the event reads {what}, which the \
      imperative code binds but cannot return to it: a proof, a type, a local instance, or a \
      value whose type depends on another of its bindings{ty}\n\nRename it, or bind what the \
      event needs to a value"
  -- When the event does not resolve here, a hidden binding it names is the likely cause.
  let rejectNamed : TermElabM Unit := do
    for d in lctx do
      if hidden d && (lctx.findFromUserName? d.userName).any (·.fvarId == d.fvarId) &&
          (findMention? obs d.userName).isSome then
        reject d
  let s ← saveState
  let read : Sum MessageLog Expr ← try
      modifyThe Core.State ({ · with messages := {} })
      let e ← withoutErrToSorry <| withSynthesize (postpone := .no) <| elabTerm obs none
      let e ← instantiateMVars e
      let log ← Core.getMessageLog
      pure <| if log.hasErrors then .inl log else .inr e
    catch ex =>
      s.restore (restoreInfo := true)
      rejectNamed
      throw ex
  s.restore (restoreInfo := true)
  let e ← match read with
    | .inl log =>
      rejectNamed
      modifyThe Core.State fun st => { st with messages := st.messages ++ log }
      throwAbortTerm
    | .inr e => pure e
  for f in (collectFVars {} e).fvarIds do
    if let some d := lctx.find? f then
      if hidden d then reject d
  -- The tail returns its variables to the observation: record each the observation names as used
  -- there, at that identifier, for the unused-variables linter, which then warns as it does in
  -- `do` on a variable neither the tail nor the observation reads.
  for d in observed do
    if let some m := findMention? obs d.userName then
      addTermInfo' m d.toExpr
  let mut tup := Lean.mkConst ``Unit.unit
  if let some last := observed.back? then
    tup := last.toExpr
    for d in observed.pop.reverse do
      tup ← mkAppM ``Prod.mk #[d.toExpr, tup]
  let names : DataValue :=
    .ofSyntax (mkNullNode (observed.map fun d => (mkIdent d.userName).raw))
  return mkMData (({} : KVMap).insert tailScopeKey names) tup

/-- The names annotated by `tailScope%` in the elaborated tail `a`, and `a` without the
annotation. -/
def tailScopeNames (a : Expr) : TermElabM (Array Name × Expr) := do
  let a ← instantiateMVars a
  let some (.mdata d _) := a.find? fun
      | .mdata d _ => d.contains tailScopeKey
      | _ => false
    | throwError "internal error: the end of the imperative tail was not elaborated"
  let names := match d.find tailScopeKey with
    | some (.ofSyntax s) => s.getArgs.map (·.getId)
    | _ => #[]
  let a := a.replace fun
    | .mdata d e => if d.contains tailScopeKey then some e else none
    | _ => none
  return (names, a)

/-- The trailing body of a `do` element, as its items and a function rebuilding the element
around new items: `let pat ← e | alt` and `let pat := e | alt` (and `let_expr`) take the rest of
the block, when it is indented below them, as their own body. An element written last has no
body; its bindings scope over nothing after it, so the body is empty. -/
def trailingBody? (elem : Syntax) : Option (Array Syntax × (Array Syntax → Syntax)) := do
  let (opt, setOpt) ← if elem.isOfKind ``Lean.Parser.Term.doLetArrow then
      let decl := elem[3]
      guard <| decl.isOfKind ``Lean.Parser.Term.doPatDecl && !decl[4].isNone
      let alt := decl[4]
      let k := alt.getNumArgs - 1
      pure (alt[k], fun o => elem.setArg 3 (decl.setArg 4 (alt.setArg k o)))
    else if elem.isOfKind ``Lean.Parser.Term.doLetElse ||
        elem.isOfKind ``Lean.Parser.Term.doLetExpr ||
        elem.isOfKind ``Lean.Parser.Term.doLetMetaExpr then
      let k := elem.getNumArgs - 1
      pure (elem[k], fun o => elem.setArg k o)
    else none
  let mkBody (items : Array Syntax) :=
    setOpt (mkNullNode #[mkNode ``Lean.Parser.Term.doSeqIndent #[mkNullNode items]])
  if opt.isNone then return (#[], mkBody)
  let body := opt[0]
  guard <| body.isOfKind ``Lean.Parser.Term.doSeqIndent
  return (body[0].getArgs, mkBody)

/-- Append `last` to the sequence `items` where ordinary `do` would put a final element written
after them: inside the innermost trailing body. -/
partial def appendAtEnd (items : Array Syntax) (last : Syntax) : Array Syntax :=
  match items.back? with
  | some item =>
    match trailingBody? item[0] with
    | some (body, rebuild) => items.pop.push (item.setArg 0 (rebuild (appendAtEnd body last)))
    | none => items.push last
  | none => #[last]

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

/-- `e` eta-reduced, unless it holds a metavariable: `fun x => ?m x` is how a pending tactic block
under the binder is written, and reducing it to `?m` would lose the binder its proof is given. -/
def etaObs (e : Expr) : Expr :=
  if e.hasExprMVar then e else e.eta

/-- The predicate of an indicator observation, eta-reduced: `fun x => p x` for an observation
`fun x => propInd (p x)`, and `fun b => b` for `propInd`. -/
def indicatorPred? (g : Expr) : Option Expr :=
  match g.cleanupAnnotations with
  | .lam n ty b bi =>
    let b := b.cleanupAnnotations
    if b.isAppOfArity ``propInd 1 then some (etaObs (Expr.lam n ty b.appArg! bi)) else none
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

/-- Elaborate a draw with its annotated result type before elaborating the body of an outer
ascription. The ascription's result hole must not default independently of the draw annotation. -/
def elabAnnotatedDraw (rhs : Term) (expected? : Option Expr) (α? : Option Expr) :
    TermElabM Expr := do
  let mut rhs := rhs
  while rhs.raw.isOfKind ``Lean.Parser.Term.paren do
    rhs := ⟨rhs.raw[1]⟩
  if α?.isSome && rhs.raw.isOfKind ``Lean.Parser.Term.typeAscription then
    let ty ← elabType rhs.raw[3][0]
    let ty ← instantiateMVars ty
    if ty.isApp then
      unless ← isDefEq ty.appArg! α?.get! do
        throwErrorAt rhs m!"the draw's result type{indentExpr ty.appArg!}\n\
          disagrees with its annotation{indentExpr α?.get!}"
    if let some expected := expected? then
      unless ← isDefEq ty expected do
        throwErrorAt rhs m!"the draw's type{indentExpr ty}\n\
          disagrees with the expected type{indentExpr expected}"
    return ← elabTermEnsuringType rhs.raw[1] ty
  elabTerm rhs expected?

/-- Elaborate the right-hand side of a draw: on its own first, reading its monad off its type as
written; then, when that leaves the monad undetermined, in the monad of the sequence; then
without postponing, which lets a nested `do`, `if` or `match` fix its monad from its own binds.
An annotation supplies the expected result type throughout elaboration. Default instances are not
applied: as in ordinary `do`, the rest of the sequence and the event can still fix a result type
that a numeral leaves open. Returns the draw, its monad and its result type, or postpones. -/
def elabDraw (hint? : Option Expr) (rhs : Term) (ty? : Option Term) :
    TermElabM (Expr × Expr × Expr) := do
  let α? ← ty?.mapM elabType
  let elabRhs (m : Expr) : TermElabM Expr := do
    let α ← match α? with
      | some α => pure α
      | none => mkFreshTypeMVar
    elabAnnotatedDraw rhs (some (mkApp m α)) α?
  let result? (a : Expr) : TermElabM (Option (Expr × Expr × Expr)) := do
    let r? ← determined? a
    if let some (_, _, β) := r? then
      if let some α := α? then
        unless ← isDefEq α β do
          throwErrorAt rhs m!"the draw's result type{indentExpr β}\n\
            disagrees with its annotation{indentExpr α}"
    return r?
  let s ← saveState
  let a ← withSynthesizeLight <| elabAnnotatedDraw rhs none α?
  if let some r@(_, m, _) ← determined? a then
    if α?.isNone then return r
    unless m.hasMVar do
      s.restore
      let a ← withSynthesizeLight <| elabRhs m
      if let some r ← result? a then return r
  if let some m₀ := hint? then
    s.restore
    let a ← withSynthesizeLight <| elabRhs m₀
    if let some r ← result? a then return r
  -- The surrounding term may still determine the draw, as a `let`-bound `do` block whose monad
  -- its own binds fix does once that block is forced; the draw's own binds are forced only when
  -- nothing outside can postpone any longer.
  s.restore
  tryPostpone
  let a ← withSynthesizeLight <| withoutPostponing do
    let a ← elabAnnotatedDraw rhs none α?
    if let some (_, m, _) ← determined? a then
      if α?.isSome then return ← elabRhs m
    return a
  if let some r ← result? a then return r
  throwErrorAt rhs m!"cannot determine the monad of the draw{indentD rhs}\n\
    ascribe it, as in `(… : ProbComp _)`, or draw first from a computation whose monad is known"

/-- A draw in an imperative tail preserves its written monad before ordinary `do` elaboration
checks its expected type. -/
syntax (name := tailDrawStx) "probabilityDraw% " term : term

/-- Protect the draws of an imperative tail, leaving nested term-level `do` programs intact. -/
partial def protectTailDraws (stx : Syntax) : MacroM Syntax := do
  if stx.isOfKind ``Lean.Parser.Term.do then return stx
  -- `let_expr` and the like keep their trailing body, where the end of the tail goes; expanding
  -- them first would leave the end outside it.
  if !stx.isOfKind ``Lean.Parser.Term.doLetArrow then
    if let some (body, rebuild) := trailingBody? stx then
      if body.isEmpty then return stx
      return rebuild (← body.mapM protectTailDraws)
  if let some expanded ← expandMacro? stx then return ← protectTailDraws expanded
  if stx.isOfKind ``Lean.Parser.Term.doLetArrow then
    let decl := stx[3]
    let rhs ← rhsTerm decl[3]
    let action ← `(doElem| probabilityDraw% $rhs)
    let stx := stx.setArg 3 (decl.setArg 3 action.raw)
    -- The rest of the block may be the trailing body of `let pat ← e | alt`.
    let some (body, rebuild) := trailingBody? stx | return stx
    if body.isEmpty then return stx
    return rebuild (← body.mapM protectTailDraws)
  if stx.isOfKind ``Lean.Parser.Term.doExpr then
    let rhs ← rhsTerm stx
    return (← `(doElem| probabilityDraw% $rhs)).raw
  match stx with
  | .node info kind args => return .node info kind (← args.mapM protectTailDraws)
  | _ => return stx

/-- Elaborate a tail draw in its written monad, using a genuine monad lift when the surrounding
program expects another monad. Comparing the unapplied monads prevents a transformer from
unifying with its base monad at a different result type. -/
def elabTailDraw (rhs : Term) (expected? : Option Expr) : TermElabM Expr := do
  let expected? ← expected?.mapM instantiateMVars
  let hint? := expected?.filter (·.isApp) |>.map (·.appFn!)
  let ty? ← (expected?.filter (fun ty => ty.isApp && !ty.appArg!.hasMVar)).mapM
    (fun ty => exprToSyntax ty.appArg!)
  let (a, m, _) ← elabDraw hint? rhs ty?
  if let some n := hint? then
    unless ← isDefEq m n do
      let lift? ← synthInstance? (← mkAppM ``MonadLiftT #[m, n])
      if lift?.isNone then
        throwErrorAt rhs "a draw in an imperative tail has a different monad; lift the draw \
          or ascribe the tail's monad explicitly"
      return ← elabTermEnsuringType (← `(liftM $(← exprToSyntax a))) expected?.get!
  ensureHasType expected? a

/-- Infer an imperative tail from its own draws before using the preceding sequence's monad
as a fallback for tails without a determined draw. -/
def elabTail (hint? : Option Expr) (prog : Term) : TermElabM (Expr × Expr × Expr) :=
    withoutErrToSorry do
  let s ← saveState
  let r? ← try
      let a ← withSynthesizeLight <| withoutPostponing <| elabTerm prog none
      determined? a
    catch _ => pure none
  if let some r := r? then return r
  s.restore
  elabDraw hint? prog none

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
    mkAppM ``predInd #[etaObs (← instantiateMVars p)]
  else
    let g ← elabTermEnsuringType (← `(fun $binderStx => ($body : ENNReal)))
      (← mkArrow α (Lean.mkConst ``ENNReal))
    let g := etaObs (← instantiateMVars g)
    match indicatorPred? g with
    | some p => mkAppM ``predInd #[p]
    | none => pure g

/-- The binder syntax of a draw for a `fun`. -/
def Binder.funBinder : Binder → MacroM Term
  | .ident x none => pure x
  | .ident x (some ty) => `(($x : $ty))
  | .hole _ => `(_)
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
      | .ident _ ty? | .pat _ ty? | .hole ty? => ty?
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
    if ← items.anyM (fun item => liftMacroM (hasTopLevelReturn item.raw)) then
      throwError "`return` is not allowed at the top level of the braces: the sequence's \
        bindings are what the event observes; bind a computation that returns early as \
        `let x ← (do …)`"
    let guardedItems ← items.mapM fun item => do
      return (⟨← liftMacroM (protectTailDraws item.raw)⟩ : TSyntax ``Lean.Parser.Term.doSeqItem)
    let scope := Syntax.mkNumLit (toString (← getLCtx).numIndices)
    let obs ← if event then `(($val : Prop)) else `(($val : ENNReal))
    let endItem ← `(Lean.Parser.Term.doSeqItem| pure (tailScope% $scope observing $obs))
    let progItems := appendAtEnd (guardedItems.map (·.raw)) endItem.raw
    let prog ← `((do $(progItems.map (⟨·⟩)):doSeqItem*))
    let (a, m, β) ← elabTail hint? prog
    let (vars, a) ← tailScopeNames a
    let (_, tupPat) ← liftMacroM (mkTuple (vars.map mkIdent))
    checkMeasureSemantics m
    let body ← if event then `(propInd ($val : Prop)) else pure val
    let g ← elabTermEnsuringType (← `(fun $tupPat => ($body : ENNReal))) (← mkArrow β ennreal)
    let g := etaObs (← instantiateMVars g)
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

end VCVio.ProbabilityNotation

elab_rules : term <= expected?
  | `(VCVio.ProbabilityNotation.tailDrawStx| probabilityDraw% $rhs) =>
    VCVio.ProbabilityNotation.elabTailDraw rhs expected?

elab_rules : term
  | `(VCVio.ProbabilityNotation.tailScopeStx| tailScope% $n observing $obs) =>
    VCVio.ProbabilityNotation.elabTailScope n.getNat obs

elab_rules : term
  | `(expect% $[(m := $h)]? {$items*}[$b]) => do
    VCVio.ProbabilityNotation.elabSeq (← h.mapM (elabTerm · none)) items b (event := false)
  | `(prEvent% $[(m := $h)]? {$items*}[$t]) => do
    VCVio.ProbabilityNotation.elabSeq (← h.mapM (elabTerm · none)) items t (event := true)

end Elaboration

macro_rules (kind := prEventStx)
  | `(Pr{{$items*}}[$t]) => `((prEvent% {$items*}[$t] : ENNReal))
  | `(Pr{$items*}[$t]) => `((prEvent% {$items*}[$t] : ENNReal))

macro_rules (kind := expectStx)
  | `(𝔼{{$items*}}[$b]) => `((expect% {$items*}[$b] : ENNReal))
  | `(𝔼{$items*}[$b]) => `((expect% {$items*}[$b] : ENNReal))
