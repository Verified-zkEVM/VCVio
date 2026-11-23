/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import PolyFun.Control.Monad.Measure.Event
public import VCVio.EvalDist.Defs.Measure.Core
public import VCVio.EvalDist.ProbabilityNotation.Attr
public meta import Lean.PrettyPrinter.Formatter
public meta import Lean.PrettyPrinter.Delaborator.Basic

/-!
# Event-probability notation

`prEvent mx`, the mass that the successful-output measure of `mx : m Prop` puts on `True`, and
`prFail mx`, the mass that measure is missing, live in PolyFun's
`PolyFun.Control.Monad.Measure.Event` together with their laws.

`Pr{…}[…]` is VCVio's notation for `prEvent`. The braces hold an ordinary Lean `do` sequence, such
as `let x ← mx; let y ← my x`, laid out as in a `do` block, and the brackets the event over its
bindings; `Pr{let x ← mx}[x = a]` is the probability that `mx` returns `a`. The notation elaborates
to the form `simp` maintains: the final draw becomes a map,
`Pr{let x ← mx}[p x] = prEvent (p <$> mx)`, so event laws keyed on `prEvent` apply to derived
programs.
-/

public section

attribute [prEvent_norm] map_bind bind_pure_comp Functor.map_map Function.comp_def map_pure
  bind_assoc pure_bind bind_map_left id_map'

/-- Probability of a successful event after an ordinary Lean `do` sequence, as in
`Pr{let x ← mx; let y ← my x}[p y]`. -/
syntax (name := prEventStx) "Pr{" doSeq "}[" term "]" : term

public meta section Formatting

open Lean PrettyPrinter Formatter Syntax.MonadTraverser

/-- Format an event sequence directly after its opening delimiter, its statements separated by
`; ` and soft line breaks, so that a short sequence stays on one line. Explicitly braced sequences
keep the ordinary Lean formatter, and explicit line breaks after the opening delimiter are
preserved. -/
@[formatter prEventStx]
def prEventFormatter : Formatter := do
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
    symbolNoAntiquot.formatter "Pr{"

end Formatting

public meta section Elaboration

open Lean Elab Term Meta

/-- Rewrite the final `a >>= fun x => pure b` of a chain of binds to `(fun x => b) <$> a`, the form
that `simp` maintains: the selector is eta-reduced and an identity selector is dropped. Other
shapes are returned unchanged. Instances are left to later synthesis, so elaboration problems
inside the computation may still be pending. -/
partial def prEventNormalize (e : Expr) : TermElabM Expr := do
  -- `do` binds the continuation of an `if` as a join point before pushing it into both branches.
  let e := zetaHead (← instantiateMVars e)
  if e.isAppOfArity ``ite 5 then
    let yes ← prEventNormalize (e.getArg! 3)
    let no ← prEventNormalize (e.getArg! 4)
    return mkAppN e.getAppFn (e.getAppArgs.set! 3 yes |>.set! 4 no)
  if e.isAppOfArity ``dite 5 then
    let branch (f : Expr) : TermElabM Expr := do
      let .lam n ty body bi := f.cleanupAnnotations | return f
      withLocalDecl n bi ty fun h => do
        mkLambdaFVars #[h] (← prEventNormalize (body.instantiate1 h))
    return mkAppN e.getAppFn (e.getAppArgs.set! 3 (← branch (e.getArg! 3))
      |>.set! 4 (← branch (e.getArg! 4)))
  let some (m, α, β, a, k) := bindParts? e | return e
  let .lam n ty body bi := k.cleanupAnnotations | return e
  let body := zetaHead body
  if let some b := pureArg? body then
    if b == .bvar 0 then return a
    -- Take the functor from the monad, as `simp`'s `bind_pure_comp` does.
    let monad ← mkInstMVar (← mkAppM ``Monad #[m])
    let inst ← mkAppOptM ``Applicative.toFunctor
      #[m, ← mkAppOptM ``Monad.toApplicative #[m, monad]]
    return ← mkAppOptM ``Functor.map #[m, inst, α, β, (Expr.lam n ty b bi).eta, a]
  withLocalDecl n bi ty fun x => do
    let rest ← prEventNormalize (body.instantiate1 x)
    let k' ← mkLambdaFVars #[x] rest
    return mkAppN e.getAppFn (e.getAppArgs.set! 5 k')
where
  /-- Local definitions of the sequence are substituted into what follows them. -/
  zetaHead (e : Expr) : Expr :=
    match e.cleanupAnnotations.headBeta with
    | .letE _ _ value body _ => zetaHead (body.instantiate1 value)
    | e => e
  bindParts? (e : Expr) : Option (Expr × Expr × Expr × Expr × Expr) :=
    if e.isAppOfArity ``Bind.bind 6 then
      let args := e.getAppArgs
      some (args[0]!, args[2]!, args[3]!, args[4]!, args[5]!)
    else none
  pureArg? (e : Expr) : Option Expr :=
    if e.isAppOfArity ``Pure.pure 4 then some e.appArg! else none

/-- Internal form of the event notation: the computation's `do` sequence and its final event. -/
syntax (name := prEventElabStx) "prEvent% " "{" doSeq "}[" term "]" : term

/-- The monad of an event sequence, when its own terms determine it: the type of the first draw
`let x ← e` or, failing that, of the whole sequence elaborated on its own. The probe's elaboration
is discarded. -/
def prEventMonad? (items : Array (TSyntax ``Lean.Parser.Term.doSeqItem)) (body : Term) :
    TermElabM (Option Expr) := do
  let firstDraw? : Option Syntax := do
    let elem := (← items[0]?).raw[0]
    guard <| elem.isOfKind ``Lean.Parser.Term.doLetArrow
    let action := elem[3][3]
    guard <| action.isOfKind ``Lean.Parser.Term.doExpr
    return action[0]
  let saved ← saveState
  let m? ← try
      let m? ← if let some action := firstDraw? then
          let ty ← instantiateMVars (← whnfR (← inferType (← elabTerm action none)))
          pure <| if ty.isApp && !ty.appFn!.hasExprMVar then some ty.appFn! else none
        else
          -- `do` infers its monad from the sequence when the expected type leaves it open.
          let m ← mkFreshExprMVar (← mkArrow (mkSort Level.one) (mkSort (← mkFreshLevelMVar).succ))
          discard <| elabTerm body (mkApp m (mkSort .zero))
          synthesizeSyntheticMVarsNoPostponing
          let m ← instantiateMVars m
          pure <| if m.hasExprMVar then none else some m
      m?.mapM fun m => (abstractMVars m : MetaM _)
    catch _ => pure none
  saved.restore
  -- Universe metavariables of the discarded probe are reopened as fresh ones.
  m?.mapM fun m => return (← openAbstractMVarsResult m).2.2

/-- A final destructuring draw `let pat ← e` becomes a plain draw whose event matches on `pat`,
so the event still ends in a map of its selector. -/
def splitFinalPattern (items : Array (TSyntax ``Lean.Parser.Term.doSeqItem)) (t : Term) :
    TermElabM (Array (TSyntax ``Lean.Parser.Term.doSeqItem) × Term) := do
  let some item := items.back? | return (items, t)
  let elem := item.raw[0]
  unless elem.isOfKind ``Lean.Parser.Term.doLetArrow && elem[1].isNone do return (items, t)
  let decl := elem[3]
  unless decl.isOfKind ``Lean.Parser.Term.doPatDecl && decl[4].isNone && decl[1].isNone do
    return (items, t)
  let action := decl[3]
  -- The draw is a term, or a nested `do` block that is kept as one.
  let e : Term ← if action.isOfKind ``Lean.Parser.Term.doExpr then pure ⟨action[0]⟩
    else if action.isOfKind ``Lean.Parser.Term.doNested then `((do $(⟨action[1]⟩):doSeq))
    else return (items, t)
  let pat : Term := ⟨decl[0]⟩
  let last ← `(Lean.Parser.Term.doSeqItem| let z ← $e:term)
  -- A discarded result binds nothing the event could mention.
  if pat.raw.isOfKind ``Lean.Parser.Term.hole then return (items.pop.push last, t)
  return (items.pop.push last, ← `(match z with | $pat => $t))

/-- Elaborate the event of a `do` sequence as `prEvent` in normal form. The sequence is elaborated
against the monad of its first draw when that is known; otherwise elaboration is postponed, and
the notation ascribes `ℝ≥0∞` so the placeholder keeps that type. -/
def elabPrEventDo (items : Array (TSyntax ``Lean.Parser.Term.doSeqItem)) (t : Term) :
    TermElabM Expr := do
  let (items, t) ← splitFinalPattern items t
  let body ← `(do $items:doSeqItem* return ($t : Prop))
  let expected? := (← prEventMonad? items body).map (mkApp · (mkSort .zero))
  let e ← instantiateMVars (← elabTerm body expected?)
  if e.getAppFn.isMVar then tryPostpone
  let e ← prEventNormalize e
  let ty ← whnfR (← inferType e)
  unless ty.isApp do
    throwError m!"an event expects a computation in a monad, got{indentExpr ty}"
  let inst ← mkInstMVar (← mkAppM ``EvalDistSemantics #[ty.appFn!])
  mkAppOptM ``prEvent #[ty.appFn!, inst, e]

elab_rules : term
  | `(prEvent% {$items*}[$t]) => elabPrEventDo items t

end Elaboration

macro_rules (kind := prEventStx)
  | `(Pr{{$items*}}[$t]) => `((prEvent% {$items*}[$t] : ENNReal))
  | `(Pr{$items*}[$t]) => `((prEvent% {$items*}[$t] : ENNReal))

public meta section Delaboration

open Lean Meta PrettyPrinter Delaborator SubExpr

/-- The draws of a normalized event, as `let x ← a` statements: a chain of binds ending in a map
of the final selector. An eta-reduced selector `f` is displayed applied to the first of `x`, `y`,
`z`, `w` that no enclosing draw binds, so that `Membership.mem S` reads `x ∈ S`. -/
partial def delabPrEventDraws :
    DelabM (Array (TSyntax ``Lean.Parser.Term.doSeqItem) × Term) := do
  let e ← getExpr
  if e.isAppOfArity ``Bind.bind 6 then
    let a ← withNaryArg 4 delab
    withNaryArg 5 do
      unless (← getExpr).isLambda do failure
      withBindingBodyUnusedName fun x => do
        let (draws, t) ← delabPrEventDraws
        return (#[← `(Lean.Parser.Term.doSeqItem| let $(⟨x⟩):ident ← $a:term;)] ++ draws, t)
  else if e.isAppOfArity ``Functor.map 6 then
    let a ← withNaryArg 5 delab
    withNaryArg 4 do
      let f ← getExpr
      if f.isLambda then
        withBindingBodyUnusedName fun x => do
          return (#[← `(Lean.Parser.Term.doSeqItem| let $(⟨x⟩):ident ← $a:term)], ← delab)
      else
        let .forallE _ dom _ _ ← whnf (← inferType f) | failure
        let lctx ← getLCtx
        let name := ([`x, `y, `z, `w].find? fun n => (lctx.findFromUserName? n).isNone).getD
          (lctx.getUnusedName `x)
        withLocalDeclD name dom fun x => do
          let t ← withTheReader SubExpr (fun sub => { sub with expr := mkApp f x }) delab
          return (#[← `(Lean.Parser.Term.doSeqItem| let $(mkIdent name):ident ← $a:term)], t)
  else failure

/-- Display `prEvent` in the notation it elaborates from. -/
@[delab app.prEvent]
def delabPrEvent : Delab := whenPPOption getPPNotation <| withOverApp 3 do
  withNaryArg 2 do
    let (draws, t) ← delabPrEventDraws
    `(Pr{$draws*}[$t])

end Delaboration

/-! ## Events of two-step computations -/

universe v

/-- Rewrite the event of a two-step computation pointwise in its first draw: if every inner
event has the same probability, so has the whole event. -/
theorem prEvent_bind_congr_of_forall
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β γ : Type} (mx : m α) (f : α → m β) (g : α → m γ)
    (p : α → β → Prop) (q : α → γ → Prop)
    (h : ∀ x, Pr{let y ← f x}[p x y] = Pr{let z ← g x}[q x z]) :
    Pr{let x ← mx; let y ← f x}[p x y] = Pr{let x ← mx; let z ← g x}[q x z] := by
  have key := prEvent_bind_congr mx (fun x => do let y ← f x; return p x y)
    (fun x => do let z ← g x; return q x z) id id (fun x => by
      simpa only [prEvent_norm, bind_assoc, pure_bind, id] using h x)
  simpa only [prEvent_norm, bind_assoc, pure_bind, id] using key
