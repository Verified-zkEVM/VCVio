/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Expectation
public import VCVio.EvalDist.ProbabilityNotation.Attr
public meta import Lean.PrettyPrinter.Formatter
public meta import Lean.PrettyPrinter.Delaborator.Basic

/-!
# Event probabilities of computations

`prEvent mx p` is the probability that the output of `mx` satisfies `p`: the mass the
successful-output measure of `p <$> mx` puts on `True`. It needs no measurable structure on the
outputs. `Pr{…}[…]` is its notation. The braces hold an ordinary Lean `do` sequence, such as
`let x ← mx; let y ← my x`, laid out as in a `do` block, and the brackets the event over its
bindings; `Pr{let x ← mx}[x = a]` is the probability that `mx` returns `a`.

## Normal form

The notation elaborates to nested expectations: every draw but the last becomes an expectation
`wp⟦a⟧ fun x => …` (`VCVio.EvalDist.Expectation`), and the last draw an event,
```
Pr{let x ← mx; let y ← my x}[p x y] = wp⟦mx⟧ fun x => prEvent (my x) fun y => p x y
```
Binds inside draws are reassociated, maps are fused into the event, a returned value is
substituted, a single-constructor destructuring becomes projections, and `if` is pulled outward.
The default `simp` set brings any event to the same form: `prEvent_bind`, `prEvent_map`,
`prEvent_pure`, `prEvent_ite`, and `prEvent_dite` push events through program structure, core's
exact `wp` equations (`ExactWPMonad.wp_bind`, …) do the same for expectations, and `wp_propInd`
folds an indicator observation back into an event. `simp only [prEvent_norm]` applies exactly
these rules. Rewriting keeps the binder names of the program.

The display inverts the elaboration: a nest of expectations ending in an event prints as the
`Pr{…}[…]` it elaborates from, and any other expectation as `wp⟦a⟧ g`.

`prFail mx` is the probability that `mx` fails or does not terminate: the mass its
successful-output measure is missing.
-/

public section

open MeasureTheory
open scoped ENNReal

universe v

/-- The probability that the output of a computation satisfies a predicate: the mass its
successful-output measure puts on the outputs satisfying it. -/
@[expose] noncomputable def prEvent {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) : ℝ≥0∞ :=
  𝒟[p <$> mx] {True}

theorem prEvent_def {m : Type → Type v} [Monad m] [EvalDistSemantics m] {α : Type} (mx : m α)
    (p : α → Prop) : prEvent mx p = 𝒟[p <$> mx] {True} := rfl

/-- The mass a proposition-valued computation puts on `True` is the event that it returns a true
proposition. -/
@[simp, grind norm]
theorem evalDist_singleton_true {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] (mx : m Prop) : 𝒟[mx] {True} = prEvent mx fun b => b := by
  rw [prEvent_def, id_map']

/-- The probability that a computation fails or does not terminate: the mass its successful-output
measure is missing. -/
@[expose] noncomputable def prFail {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {α : Type} (mx : m α) : ℝ≥0∞ :=
  1 - prEvent mx fun _ ↦ True

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

namespace ProbabilityNotation

/-- Rewrite an event into normal form with the `prEvent_norm` rules and their binder-preserving
simprocs. Every rule is an equation, and the proof that the result equals the event is
type-checked, so the normal form denotes the same probability as the event it came from. -/
def normalize (e : Expr) : MetaM Expr := do
  let some ext ← getSimpExtension? `prEvent_norm | return e
  let procs ← match ← Simp.getSimprocExtension? `prEvent_norm with
    | some procExt => pure #[← procExt.getSimprocs]
    | none => pure #[]
  let ctx ← Simp.mkContext (simpTheorems := #[← ext.getTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← withNewMCtxDepth <| simp e ctx procs
  if let some pf := r.proof? then
    -- Metavariables the surrounding term has yet to solve can leave the proof's instances
    -- unresolved; the proof is checked once the event is closed.
    unless (← instantiateMVars pf).hasExprMVar do check pf
    unless ← isDefEq (← inferType pf) (← mkEq e r.expr) do
      throwError m!"the normal form{indentExpr r.expr}\nis not proved equal to the event\
        {indentExpr e}"
  instantiateMVars r.expr

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
          let ty ← instantiateMVars (← inferType (← elabTerm action none))
          -- The monad is read off as written, so `OracleComp spec` is not unfolded.
          let ty ← if ty.isApp then pure ty else whnfR ty
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
  m?.mapM fun m => do atProp (← openAbstractMVarsResult m).2.2
where
  /-- The monad at a proposition result: the universe levels of its head constant are
  re-solved against `m Prop`, since a draw fixes the monad at the universe of its own result
  (`OracleComp spec` carries its result universe as a parameter). -/
  atProp (m : Expr) : MetaM Expr := do
    let .const c ls := m.getAppFn | return m
    let m' := mkAppN (mkConst c (← ls.mapM fun _ ↦ mkFreshLevelMVar)) m.getAppArgs
    if ← isTypeCorrect (mkApp m' (mkSort .zero)) then instantiateMVars m' else return m

/-- A final destructuring draw `let pat ← e` becomes a plain draw whose event matches on `pat`,
so the event is a predicate on the draw. -/
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

/-- Elaborate the event of a `do` sequence: the probability that the sequence returns a true
proposition, `prEvent (do items; return t) fun b => b`, rewritten into normal form by
`normalize`. The sequence is elaborated against the monad of its first draw when that is known.
Elaboration is postponed while the monad or its instances are undetermined, for example on a
universe the rest of the statement fixes; the notation ascribes `ℝ≥0∞` so the placeholder keeps
that type. -/
def elabPrEventDo (items : Array (TSyntax ``Lean.Parser.Term.doSeqItem)) (t : Term) :
    TermElabM Expr := do
  let (items, t) ← splitFinalPattern items t
  let body ← `(do $items:doSeqItem* return ($t : Prop))
  let expected? := (← prEventMonad? items body).map (mkApp · (mkSort .zero))
  -- The sequence's own elaboration problems are solved as far as they can be before normalizing
  -- it; those of the surrounding term are left alone. While the sequence still depends on
  -- unsolved problems, for example a binder whose type the enclosing term fixes later, the
  -- event waits.
  let e ← withSynthesize (postpone := .yes) do
    let e ← instantiateMVars (← elabTerm body expected?)
    if e.getAppFn.isMVar then tryPostpone
    pure e
  let e ← instantiateMVars e
  if e.hasExprMVar then tryPostpone
  let ty ← instantiateMVars (← inferType e)
  let ty ← if ty.isApp then pure ty else whnfR ty
  unless ty.isApp do
    throwError m!"an event expects a computation in a monad, got{indentExpr ty}"
  let m := ty.appFn!
  let pred ← withLocalDeclD `b (mkSort .zero) fun b => mkLambdaFVars #[b] b
  match ← synthInstance? (← mkAppM ``Monad #[m]),
      ← synthInstance? (← mkAppM ``EvalDistSemantics #[m]) with
  | some monad, some evalDist =>
    normalize (← mkAppOptM ``prEvent #[m, monad, evalDist, none, e, pred])
  | _, _ =>
    if (← instantiateMVars m).hasMVar then tryPostpone
    mkAppOptM ``prEvent #[m, ← mkInstMVar (← mkAppM ``Monad #[m]),
      ← mkInstMVar (← mkAppM ``EvalDistSemantics #[m]), none, e, pred]

end ProbabilityNotation

elab_rules : term
  | `(prEvent% {$items*}[$t]) => ProbabilityNotation.elabPrEventDo items t

end Elaboration

macro_rules (kind := prEventStx)
  | `(Pr{{$items*}}[$t]) => `((prEvent% {$items*}[$t] : ENNReal))
  | `(Pr{$items*}[$t]) => `((prEvent% {$items*}[$t] : ENNReal))

public meta section Delaboration

open Lean Meta PrettyPrinter Delaborator SubExpr

namespace ProbabilityNotation

/-- Whether an ordered algebra is the expectation algebra of successful-output measures. -/
partial def isMeasureAlgebra (a : Expr) : MetaM Bool := do
  let a := a.cleanupAnnotations
  if a.isAppOf ``MeasureProgramLogic.toMAlgOrdered then return true
  match ← withReducibleAndInstances (unfoldDefinition? a) with
  | some a' => isMeasureAlgebra a'
  | none => return false

/-- Whether a weakest-precondition interpretation is the measure interpretation. -/
partial def isMeasureInterpretation (w : Expr) : MetaM Bool := do
  let w := w.cleanupAnnotations
  if w.isAppOf ``MeasureProgramLogic.measureWP then return true
  if w.isAppOfArity ``MAlgOrdered.toWPMonad 6 then return ← isMeasureAlgebra (w.getArg! 4)
  match ← withReducibleAndInstances (unfoldDefinition? w) with
  | some w' => isMeasureInterpretation w'
  | none => return false

/-- Whether `e` is an expectation `wp⟦a⟧ g`: core's `wp` under the measure interpretation. -/
def isExpectation (e : Expr) : MetaM Bool := do
  unless e.isAppOfArity ``Std.Internal.Do.WP.wp 10 do return false
  let inst := e.getArg! 6
  unless inst.isAppOfArity ``Std.Internal.Do.instWPOfWPMonad 8 do return false
  isMeasureInterpretation (inst.getArg! 7)

/-- The statement `let x ← a` for a draw bound by the `fun` `f`, or `let _ ← a` when `f` ignores
its argument. -/
def drawItem (f : Expr) (x : Syntax) (a : Term) (sep : Bool) :
    DelabM (TSyntax ``Lean.Parser.Term.doSeqItem) := do
  let x : Term ← if f.bindingBody!.hasLooseBVars then pure ⟨x⟩ else `(_)
  if sep then `(Lean.Parser.Term.doSeqItem| let $x:term ← $a:term;)
  else `(Lean.Parser.Term.doSeqItem| let $x:term ← $a:term)

/-- The draws of an event in normal form, as `let x ← a` statements: a nest of expectations
ending in an event. A predicate that is not a `fun` is displayed applied to the first of `x`, `y`,
`z`, `w` that no enclosing draw binds, so that `Membership.mem S` reads `x ∈ S`. -/
partial def delabDraws : DelabM (Array (TSyntax ``Lean.Parser.Term.doSeqItem) × Term) := do
  let e ← getExpr
  if ← isExpectation e then
    let a ← withNaryArg 7 delab
    withNaryArg 8 do
      let g ← getExpr
      unless g.isLambda do failure
      withBindingBodyUnusedName fun x => do
        let (draws, t) ← delabDraws
        return (#[← drawItem g x a true] ++ draws, t)
  else if e.isAppOfArity ``prEvent 6 then
    let a ← withNaryArg 4 delab
    withNaryArg 5 do
      let p ← getExpr
      if p.isLambda then
        withBindingBodyUnusedName fun x => do
          return (#[← drawItem p x a false], ← delab)
      else
        let .forallE _ dom _ _ ← whnf (← inferType p) | failure
        let lctx ← getLCtx
        let name := ([`x, `y, `z, `w].find? fun n => (lctx.findFromUserName? n).isNone).getD
          (lctx.getUnusedName `x)
        withLocalDeclD name dom fun x => do
          let t ← withTheReader SubExpr (fun sub => { sub with expr := mkApp p x }) delab
          return (#[← `(Lean.Parser.Term.doSeqItem| let $(mkIdent name):ident ← $a:term)], t)
  else failure

/-- Display an event in the notation it elaborates from. -/
@[delab app.prEvent]
def delabPrEvent : Delab := whenPPOption getPPNotation <| withOverApp 6 do
  let (draws, t) ← delabDraws
  `(Pr{$draws*}[$t])

/-- Display a nest of expectations ending in an event as that event, and any other expectation
under the measure interpretation as `wp⟦a⟧ g`. -/
@[delab app.Std.Internal.Do.WP.wp]
def delabExpectation : Delab := whenPPOption getPPNotation <| withOverApp 10 do
  unless ← isExpectation (← getExpr) do failure
  (do
    let (draws, t) ← delabDraws
    `(Pr{$draws*}[$t])) <|> (do
    let a ← withNaryArg 7 delab
    let g ← withNaryArg 8 delab
    `(wp⟦$a⟧ $g))

end ProbabilityNotation

end Delaboration

/-! ## Laws of the normal form -/

section NormalForm

variable {m : Type → Type v} [Monad m] [EvalDistSemantics m] {α β : Type}

/-- An event after a bind is the expectation of the event after each continuation. -/
@[simp, prEvent_norm, grind norm]
theorem prEvent_bind [LawfulMonad m] [LawfulEvalDistSemantics m] (mx : m α) (f : α → m β)
    (p : β → Prop) : prEvent (mx >>= f) p = wp⟦mx⟧ fun a => prEvent (f a) p := by
  let obs : α → Measure Prop := fun a => 𝒟[p <$> f a]
  let : MeasurableSpace α := MeasurableSpace.comap obs inferInstance
  have hobs : Measurable obs := comap_measurable obs
  have hmeas : Measurable fun a => prEvent (f a) p :=
    (Measure.measurable_coe (measurableSet_singleton True)).comp hobs
  rw [MeasureProgramLogic.wp_eq_lintegral mx _ hmeas, prEvent_def, map_bind, evalDist_bind _ _ hobs,
    Measure.bind_apply (measurableSet_singleton True) hobs.aemeasurable]
  rfl

/-- An event of mapped outputs is the event of the composed predicate. -/
@[simp, prEvent_norm, grind norm]
theorem prEvent_map [LawfulMonad m] (mx : m α) (f : α → β) (p : β → Prop) :
    prEvent (f <$> mx) p = prEvent mx fun a => p (f a) := by
  simp only [prEvent_def, Functor.map_map]

/-- An event of a computation that returns a function of its draw is the event of the composed
predicate. Only the monad laws are needed, so the final draw of an event normalizes under any
semantics. `simp` reaches it through `bind_pure_comp` and `prEvent_map`. -/
@[prEvent_norm]
theorem prEvent_bind_pure [LawfulMonad m] (mx : m α) (f : α → β) (p : β → Prop) :
    prEvent (mx >>= fun a => pure (f a)) p = prEvent mx fun a => p (f a) := by
  rw [show (mx >>= fun a => pure (f a)) = f <$> mx from (map_eq_bind_pure_comp (m := m) f mx).symm,
    prEvent_map]

/-- An event of a returned value is the indicator of the predicate at that value. -/
@[simp, prEvent_norm, grind =]
theorem prEvent_pure [LawfulMonad m] [LawfulPureEvalDistSemantics m] (a : α) (p : α → Prop) :
    prEvent (pure a : m α) p = propInd (p a) := by
  classical
  rw [prEvent_def, map_pure, evalDist_pure, propInd]
  by_cases h : p a <;> simp [h]

/-- An event of a conditional computation is the conditional event. -/
@[simp, prEvent_norm]
theorem prEvent_ite (c : Prop) [Decidable c] (mx my : m α) (p : α → Prop) :
    prEvent (if c then mx else my) p = if c then prEvent mx p else prEvent my p := by
  split <;> rfl

/-- An event of a dependent conditional computation is the dependent conditional event. -/
@[simp, prEvent_norm]
theorem prEvent_dite (c : Prop) [Decidable c] (mx : c → m α) (my : ¬c → m α) (p : α → Prop) :
    prEvent (if h : c then mx h else my h) p =
      if h : c then prEvent (mx h) p else prEvent (my h) p := by
  split <;> rfl

variable [LawfulMonad m] [LawfulEvalDistSemantics m]

/-- Every event is the expectation of its indicator. -/
theorem prEvent_eq_wp (mx : m α) (p : α → Prop) :
    prEvent mx p = wp⟦mx⟧ fun a => propInd (p a) := by
  simpa only [bind_pure, prEvent_pure] using prEvent_bind mx (fun a => (pure a : m α)) p

/-- The expectation of an indicator is the event it indicates. `simp` applies it through the
simproc `wp_propInd_named`, which keeps the binder name. -/
@[grind norm]
theorem wp_propInd (mx : m α) (p : α → Prop) :
    wp⟦mx⟧ (fun a => propInd (p a)) = prEvent mx p :=
  (prEvent_eq_wp mx p).symm

end NormalForm

/-! ### Binder names

`simp` rewrites with the laws above by the following pre-procedures, which name each new binder
after the program's own. -/

public meta section Rewriting

open Lean Meta

namespace ProbabilityNotation

/-- Rewrite `e` with the equation `thm`, whose instance arguments not determined by unification
are synthesized. Returns the right side and the proof. -/
def rewriteWith? (thm : Name) (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let pf ← mkConstWithFreshMVarLevels thm
  let (xs, bis, ty) ← forallMetaTelescopeReducing (← inferType pf)
  let some (_, lhs, rhs) := ty.eq? | return none
  unless ← isDefEq lhs e do return none
  for x in xs, bi in bis do
    if bi.isInstImplicit && !(← x.mvarId!.isAssigned) then
      let some inst ← synthInstance? (← inferType x) | return none
      unless ← isDefEq x inst do return none
  return some (← instantiateMVars rhs, ← instantiateMVars (mkAppN pf xs))

/-- Name the binder of the `i`-th argument of `e`, a `fun`, after `n`. -/
def renameArg (e : Expr) (i : Nat) (n : Name) : Expr :=
  let args := e.getAppArgs
  match args[i]? with
  | some (.lam _ ty b bi) => mkAppN e.getAppFn (args.set! i (.lam n ty b bi))
  | _ => e

/-- The binder name of `f`, when it is a `fun`. Names that `do` generates, such as the
discriminant of a destructuring draw or a lifted action, become `x`. -/
def lamName? (f : Expr) : Option Name :=
  match f.cleanupAnnotations with
  | .lam n .. => some (if n.eraseMacroScopes.toString.startsWith "__" then `x else n)
  | _ => none

/-- Rewrite `e` with `thm` and name the binder of the `i`-th argument of the result, a `fun`, after
the first binder among `src`, or `x` when none of them is a `fun`. -/
def namedStep (thm : Name) (e : Expr) (i : Nat) (src : Array Expr) : SimpM Simp.Step := do
  let some (rhs, pf) ← rewriteWith? thm e | return .continue
  let rhs := renameArg rhs i ((src.findSome? lamName?).getD `x)
  return .visit { expr := ← Core.betaReduce rhs, proof? := pf }

end ProbabilityNotation

end Rewriting

open Lean Meta Simp ProbabilityNotation in
/-- `prEvent_bind`, naming the new draw after the continuation's binder; without lawful measure
semantics, `prEvent_bind_pure` for a final returned value. -/
simproc ↓ [simp, prEvent_norm] prEvent_bind_named (@prEvent _ _ ?_ _ (_ >>= _) _) := fun e => do
  unless e.isAppOfArity ``prEvent 6 do return .continue
  let mb := e.getArg! 4
  unless mb.isAppOfArity ``Bind.bind 6 do return .continue
  match ← namedStep ``prEvent_bind e 8 #[mb.getArg! 5] with
  | .continue none => namedStep ``prEvent_bind_pure e 5 #[mb.getArg! 5]
  | step => return step

open Lean Meta Simp ProbabilityNotation in
/-- `prEvent_map`, naming the predicate's binder after the map's. -/
simproc ↓ [simp, prEvent_norm] prEvent_map_named (@prEvent _ _ ?_ _ (_ <$> _) _) := fun e => do
  unless e.isAppOfArity ``prEvent 6 do return .continue
  let mb := e.getArg! 4
  unless mb.isAppOfArity ``Functor.map 6 do return .continue
  namedStep ``prEvent_map e 5 #[mb.getArg! 4, e.getArg! 5]

open Lean Meta Simp ProbabilityNotation in
/-- `ExactWPMonad.wp_bind`, naming the new binder after the continuation's. -/
simproc ↓ [simp, prEvent_norm] wp_bind_named
    (@Std.Internal.Do.WP.wp _ _ _ _ _ _ ?_ (_ >>= _) _ _) := fun e => do
  unless e.isAppOfArity ``Std.Internal.Do.WP.wp 10 do return .continue
  let mb := e.getArg! 7
  unless mb.isAppOfArity ``Bind.bind 6 do return .continue
  namedStep ``ExactWPMonad.wp_bind e 8 #[mb.getArg! 5]

open Lean Meta Simp ProbabilityNotation in
/-- `ExactWPMonad.wp_map`, naming the observation's binder after the map's. -/
simproc ↓ [simp, prEvent_norm] wp_map_named
    (@Std.Internal.Do.WP.wp _ _ _ _ _ _ ?_ (_ <$> _) _ _) := fun e => do
  unless e.isAppOfArity ``Std.Internal.Do.WP.wp 10 do return .continue
  let mb := e.getArg! 7
  unless mb.isAppOfArity ``Functor.map 6 do return .continue
  namedStep ``ExactWPMonad.wp_map e 8 #[mb.getArg! 4, e.getArg! 8]

open Lean Meta Simp ProbabilityNotation in
/-- `wp_propInd`, keeping the name the observation binds. It runs after the observation is
simplified, when the indicator has appeared. -/
simproc [simp, prEvent_norm] wp_propInd_named
    (@Std.Internal.Do.WP.wp _ _ _ _ _ _ ?_ _ (fun _ => propInd _) _) := fun e => do
  unless e.isAppOfArity ``Std.Internal.Do.WP.wp 10 do return .continue
  namedStep ``wp_propInd e 5 #[e.getArg! 8]

attribute [prEvent_norm] ExactWPMonad.wp_pure ExactWPMonad.wp_bind ExactWPMonad.wp_map
  ExactWPMonad.wp_ite ExactWPMonad.wp_dite

/-! ## Constants and indicators -/

section Indicators

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α : Type}

/-- A constant observation has the expectation of the constant times the success mass. -/
@[simp]
theorem wp_const (mx : m α) (c : ℝ≥0∞) : wp⟦mx⟧ (fun _ => c) = c * Pr{let _ ← mx}[True] := by
  simpa only [propInd_true, mul_one] using MeasureProgramLogic.wp_const_mul mx c
    (fun _ => propInd True) |>.trans (congrArg (c * ·) (wp_propInd mx fun _ => True))

/-- An indicator observation scaled on the right is the scaled event. -/
@[simp]
theorem wp_propInd_mul (mx : m α) (p : α → Prop) (c : ℝ≥0∞) :
    wp⟦mx⟧ (fun a => propInd (p a) * c) = prEvent mx p * c := by
  rw [MeasureProgramLogic.wp_mul_const, wp_propInd]

/-- An indicator observation scaled on the left is the scaled event. -/
@[simp]
theorem wp_mul_propInd (mx : m α) (p : α → Prop) (c : ℝ≥0∞) :
    wp⟦mx⟧ (fun a => c * propInd (p a)) = c * prEvent mx p := by
  rw [MeasureProgramLogic.wp_const_mul, wp_propInd]

end Indicators

/-! ## Events as measures -/

section Measures

variable {m : Type → Type v} [Monad m] [EvalDistSemantics m] {α β : Type}

/-- An event is the true mass of its propositional selector. -/
theorem prEvent_eq_evalDist_map (mx : m α) (p : α → Prop) :
    prEvent mx p = 𝒟[p <$> mx] {True} := rfl

variable [LawfulMonad m] [LawfulEvalDistSemantics m]

/-- A measurable predicate returned by a computation has the probability of its event. -/
theorem prEvent_eq_evalDist [MeasurableSpace α] (mx : m α) (p : α → Prop) (hp : Measurable p) :
    Pr{let x ← mx}[p x] = 𝒟[mx] {x | p x} := by
  rw [prEvent_eq_evalDist_map, evalDist_map_apply mx hp (measurableSet_singleton True)]
  simp

/-- On a discrete output space every predicate is a measurable event. -/
theorem prEvent_eq_evalDist_of_discrete [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : m α) (p : α → Prop) : Pr{let x ← mx}[p x] = 𝒟[mx] {x | p x} :=
  prEvent_eq_evalDist mx p Measurable.of_discrete

/-- Equality to one output has its singleton mass whenever singletons are measurable. -/
theorem prEvent_eq_evalDist_singleton [MeasurableSpace α] [MeasurableSingletonClass α]
    (mx : m α) (a : α) : Pr{let x ← mx}[x = a] = 𝒟[mx] {a} := by
  simpa only [Set.ofPred_eq_eq_singleton] using
    prEvent_eq_evalDist mx (fun x ↦ x = a) (measurableSet_singleton a).mem

/-- A final decidable event has the same success mass whether it is returned as a proposition
or decided to a Boolean; no measurable structure on intermediate values is needed. -/
theorem prEvent_eq_evalDist_decide (mx : m α) (p : α → Prop) [DecidablePred p] :
    Pr{let x ← mx}[p x] = 𝒟[do let x ← mx; return decide (p x)] {true} := by
  classical
  calc
    _ = 𝒟[p <$> mx] {True} := prEvent_eq_evalDist_map mx p
    _ = 𝒟[(fun b : Prop ↦ decide b) <$> (p <$> mx)] {true} := by
      rw [evalDist_map_apply (p <$> mx)
        (Measurable.of_discrete : Measurable fun b : Prop ↦ decide b)
        (measurableSet_singleton true)]
      congr 1
      ext b
      simp
    _ = _ := by
      congr 1
      congr 1
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      apply bind_congr
      intro x
      by_cases hx : p x <;> simp [hx]

/-- The trivially true event is the successful mass of the computation, in any measurable
structure on its outputs. -/
theorem prEvent_true_eq_evalDist_apply_univ [MeasurableSpace α] (mx : m α) :
    Pr{let _ ← mx}[True] = 𝒟[mx] Set.univ := by
  rw [prEvent_eq_evalDist_map,
    evalDist_map_apply mx measurable_const (measurableSet_singleton True)]
  simp

end Measures

/-! ## Order and bounds -/

section Bounds

variable {m : Type → Type v} [Monad m] [EvalDistSemantics m] {α β γ : Type}

/-- Every event probability is at most one. -/
@[simp]
theorem prEvent_le_one (mx : m α) {p : α → Prop} : prEvent mx p ≤ 1 :=
  evalDist_apply_le_one _ _

/-- Every event probability is finite. -/
@[simp, aesop (rule_sets := [finiteness]) safe apply]
theorem prEvent_ne_top (mx : m α) {p : α → Prop} : prEvent mx p ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one mx)

/-- Every event probability is finite. -/
@[simp]
theorem prEvent_lt_top (mx : m α) {p : α → Prop} : prEvent mx p < ⊤ :=
  (prEvent_ne_top mx).lt_top

/-- Pointwise equivalent predicates have the same probability after a common computation. -/
theorem prEvent_congr (mx : m α) (p q : α → Prop) (h : ∀ x, p x ↔ q x) :
    prEvent mx p = prEvent mx q := by
  rw [show p = q from funext fun x ↦ propext (h x)]

/-- A true constant event after a lossless draw has probability one. -/
theorem prEvent_const_of_lossless (mx : m α) (hmx : prEvent mx (fun _ ↦ True) = 1) {c : Prop}
    (hc : c) : prEvent mx (fun _ ↦ c) = 1 := by
  rw [← hmx]
  exact prEvent_congr mx _ _ fun _ ↦ by simp [hc]

variable [LawfulMonad m] [LawfulEvalDistSemantics m]

/-- Measurable predicates agreeing almost everywhere have equal event probabilities. -/
theorem prEvent_congr_ae [MeasurableSpace α] (mx : m α) (p q : α → Prop)
    (hp : Measurable p) (hq : Measurable q) (h : ∀ᵐ x ∂𝒟[mx], p x ↔ q x) :
    Pr{let x ← mx}[p x] = Pr{let x ← mx}[q x] := by
  rw [prEvent_eq_evalDist mx p hp, prEvent_eq_evalDist mx q hq]
  exact measure_congr (h.mono fun _ hx ↦ propext hx)

/-- An event that never occurs has probability zero. -/
theorem prEvent_eq_zero_of_forall_not (mx : m α) (p : α → Prop) (h : ∀ x, ¬p x) :
    Pr{let x ← mx}[p x] = 0 := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete]
  simp [h]

/-- An impossible final observation has zero mass, including after a failed computation. -/
@[simp↓ high, grind norm↓]
theorem prEvent_false (mx : m α) : Pr{let _ ← mx}[False] = 0 :=
  prEvent_eq_zero_of_forall_not mx (fun _ ↦ False) (fun _ ↦ id)

/-- A false constant event has probability zero. -/
theorem prEvent_const_of_not (mx : m α) {c : Prop} (hc : ¬ c) : Pr{let _ ← mx}[c] = 0 :=
  prEvent_eq_zero_of_forall_not mx _ fun _ ↦ hc

/-- Almost-everywhere implication bounds probabilities of measurable events. -/
theorem prEvent_mono_ae [MeasurableSpace α] (mx : m α) (p q : α → Prop)
    (hp : Measurable p) (hq : Measurable q) (hpq : ∀ᵐ x ∂𝒟[mx], p x → q x) :
    Pr{let x ← mx}[p x] ≤ Pr{let x ← mx}[q x] := by
  rw [prEvent_eq_evalDist mx p hp, prEvent_eq_evalDist mx q hq]
  exact measure_mono_ae hpq

/-- Implication between events bounds their probabilities. -/
theorem prEvent_mono (mx : m α) (p q : α → Prop) (hpq : ∀ x, p x → q x) :
    Pr{let x ← mx}[p x] ≤ Pr{let x ← mx}[q x] := by
  rw [prEvent_eq_wp, prEvent_eq_wp]
  exact MeasureProgramLogic.wp_mono mx fun x ↦ propInd_mono (hpq x)

/-- A constant event conjoined on the left factors out as its indicator. -/
theorem prEvent_const_and_left (mx : m α) (P : Prop) (q : α → Prop) :
    Pr{let x ← mx}[P ∧ q x] = propInd P * Pr{let x ← mx}[q x] := by
  classical
  by_cases hP : P
  · simp [hP]
  · simp [hP, prEvent_const_of_not]

/-- A constant event conjoined on the right factors out as its indicator. -/
theorem prEvent_const_and_right (mx : m α) (P : Prop) (q : α → Prop) :
    Pr{let x ← mx}[q x ∧ P] = Pr{let x ← mx}[q x] * propInd P := by
  rw [mul_comm, ← prEvent_const_and_left]
  exact prEvent_congr mx _ _ fun _ ↦ and_comm

/-- Events of independent draws have the product of their probabilities. -/
@[simp↓ high, grind norm↓]
theorem prEvent_bind_bind_and (mx : m α) (my : m β) (p : α → Prop) (q : β → Prop) :
    Pr{let x ← mx; let y ← my}[p x ∧ q y] = Pr{let x ← mx}[p x] * Pr{let y ← my}[q y] := by
  simp only [prEvent_const_and_left, wp_propInd_mul]

/-- An expectation of an observation bounded by a constant is at most that constant. -/
theorem wp_le_of_forall_le (mx : m α) {g : α → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ x, g x ≤ c) :
    wp⟦mx⟧ g ≤ c :=
  (MeasureProgramLogic.wp_mono mx h).trans <| by
    rw [wp_const]
    exact mul_le_of_le_one_right' (prEvent_le_one mx)

/-- After a lossless computation, an observation bounded below by a constant has at least that
expectation. -/
theorem le_wp_of_forall_le (mx : m α) (hmx : Pr{let _ ← mx}[True] = 1) {g : α → ℝ≥0∞}
    {c : ℝ≥0∞} (h : ∀ x, c ≤ g x) : c ≤ wp⟦mx⟧ g :=
  le_of_eq_of_le (by rw [wp_const, hmx, mul_one]) (MeasureProgramLogic.wp_mono mx h)

/-- An expectation after a bind is at most the bound on each continuation's expectation. -/
theorem wp_le_prEvent_add (mx : m α) (bad : α → Prop) (g : α → ℝ≥0∞) {ε : ℝ≥0∞}
    (hg : ∀ x, ¬bad x → g x ≤ ε) (hle : ∀ x, g x ≤ 1) :
    wp⟦mx⟧ g ≤ Pr{let x ← mx}[bad x] + ε := by
  calc wp⟦mx⟧ g ≤ wp⟦mx⟧ fun x => propInd (bad x) + ε :=
        MeasureProgramLogic.wp_mono mx fun x => by
          classical
          by_cases h : bad x
          · simpa [h] using (hle x).trans le_self_add
          · simpa [h] using hg x h
    _ ≤ Pr{let x ← mx}[bad x] + ε := by
        rw [MeasureProgramLogic.wp_add, wp_propInd, wp_const]
        gcongr
        exact mul_le_of_le_one_right' (prEvent_le_one mx)

end Bounds

/-! ## Integrals and sums -/

section Sums

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
  [LawfulEvalDistSemantics m] {α β γ : Type}

/-- An expectation over a finite type is the finite sum of the point masses times the
observation. -/
theorem wp_eq_sum_fintype [Fintype α] (mx : m α) (g : α → ℝ≥0∞) :
    wp⟦mx⟧ g = ∑ a, Pr{let x ← mx}[x = a] * g a := by
  let : MeasurableSpace α := ⊤
  rw [MeasureProgramLogic.wp_eq_lintegral mx g Measurable.of_discrete, lintegral_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm, prEvent_eq_evalDist_singleton]

/-- An expectation over a countable type is the sum of the point masses times the
observation. -/
theorem wp_eq_tsum_of_countable [Countable α] (mx : m α) (g : α → ℝ≥0∞) :
    wp⟦mx⟧ g = ∑' a, Pr{let x ← mx}[x = a] * g a := by
  let : MeasurableSpace α := ⊤
  rw [MeasureProgramLogic.wp_eq_lintegral mx g Measurable.of_discrete, lintegral_countable']
  refine tsum_congr fun a => ?_
  rw [mul_comm, prEvent_eq_evalDist_singleton]

/-- An event after a bind integrates the event probability of each measurable continuation.
Only the common draw needs a selected measurable space; the continuation is observed in `Prop`.
-/
theorem prEvent_bind_eq_lintegral [MeasurableSpace α] (mx : m α) (f : α → m β) (p : β → Prop)
    (hf : Measurable fun x ↦ 𝒟[p <$> f x]) :
    Pr{let y ← mx >>= f}[p y] = ∫⁻ x, Pr{let y ← f x}[p y] ∂𝒟[mx] :=
  MeasureProgramLogic.wp_eq_lintegral mx _
    ((Measure.measurable_coe (measurableSet_singleton True)).comp hf)

/-- A discrete common draw discharges the observed continuation's measurability. -/
theorem prEvent_bind_eq_lintegral_of_discrete [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : m α) (f : α → m β) (p : β → Prop) :
    Pr{let y ← mx >>= f}[p y] = ∫⁻ x, Pr{let y ← f x}[p y] ∂𝒟[mx] :=
  prEvent_bind_eq_lintegral mx f p Measurable.of_discrete

/-- AE equality of measurable observed continuation probabilities gives equality after a draw. -/
theorem prEvent_bind_congr_ae [MeasurableSpace α] (mx : m α) (f : α → m β) (g : α → m γ)
    (p : β → Prop) (q : γ → Prop) (hf : Measurable fun x ↦ 𝒟[p <$> f x])
    (hg : Measurable fun x ↦ 𝒟[q <$> g x])
    (h : ∀ᵐ x ∂𝒟[mx], Pr{let y ← f x}[p y] = Pr{let z ← g x}[q z]) :
    Pr{let y ← mx >>= f}[p y] = Pr{let z ← mx >>= g}[q z] := by
  rw [prEvent_bind_eq_lintegral mx f p hf, prEvent_bind_eq_lintegral mx g q hg]
  exact lintegral_congr_ae h

/-- Pointwise equality of observed continuation probabilities gives equality after a common
draw. -/
theorem prEvent_bind_congr (mx : m α) (f : α → m β) (g : α → m γ) (p : β → Prop) (q : γ → Prop)
    (h : ∀ x, Pr{let y ← f x}[p y] = Pr{let z ← g x}[q z]) :
    Pr{let y ← mx >>= f}[p y] = Pr{let z ← mx >>= g}[q z] :=
  MeasureProgramLogic.wp_congr mx h

/-- After a draw from a finite type, an event is the finite sum of the draw's point masses times
the conditional event probabilities. -/
theorem prEvent_bind_eq_sum_fintype [Fintype α] (mx : m α) (f : α → m β) (p : β → Prop) :
    Pr{let y ← mx >>= f}[p y] = ∑ a, Pr{let x ← mx}[x = a] * Pr{let y ← f a}[p y] :=
  wp_eq_sum_fintype mx _

/-- After a draw from a countable type, an event is the sum of the draw's point masses times the
conditional event probabilities. -/
theorem prEvent_bind_eq_tsum_of_countable [Countable α] (mx : m α) (f : α → m β)
    (p : β → Prop) :
    Pr{let y ← mx >>= f}[p y] = ∑' a, Pr{let x ← mx}[x = a] * Pr{let y ← f a}[p y] :=
  wp_eq_tsum_of_countable mx _

end Sums

/-! ## Failure

`prFail mx` is the mass the successful-output measure of `mx` is missing: the probability that
`mx` fails or does not terminate. It needs no measurable structure on the outputs. -/

section prFail

variable {m : Type → Type v} [Monad m] [EvalDistSemantics m] {α : Type}

theorem prFail_def (mx : m α) : prFail mx = 1 - prEvent mx fun _ ↦ True := rfl

/-- Success and failure masses add up to one. -/
@[simp]
theorem prEvent_true_add_prFail (mx : m α) : prEvent mx (fun _ ↦ True) + prFail mx = 1 :=
  add_tsub_cancel_of_le (prEvent_le_one _)

/-- Failure and success masses add up to one. -/
@[simp]
theorem prFail_add_prEvent_true (mx : m α) : prFail mx + prEvent mx (fun _ ↦ True) = 1 := by
  rw [add_comm, prEvent_true_add_prFail]

@[simp]
theorem prFail_le_one (mx : m α) : prFail mx ≤ 1 := tsub_le_self

@[simp, aesop (rule_sets := [finiteness]) safe apply]
theorem prFail_ne_top (mx : m α) : prFail mx ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (prFail_le_one mx)

/-- A computation never fails exactly when it succeeds with probability one. -/
theorem prFail_eq_zero_iff (mx : m α) : prFail mx = 0 ↔ prEvent mx (fun _ ↦ True) = 1 := by
  rw [prFail_def, tsub_eq_zero_iff_le]
  exact ⟨fun h ↦ le_antisymm (prEvent_le_one _) h, fun h ↦ h.ge⟩

/-- A computation always fails exactly when it succeeds with probability zero. -/
theorem prFail_eq_one_iff (mx : m α) : prFail mx = 1 ↔ prEvent mx (fun _ ↦ True) = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [prFail_def, h, tsub_zero]⟩
  by_contra hne
  exact (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hne).ne h

/-- A pure computation never fails. -/
@[simp, grind =]
theorem prFail_pure [LawfulMonad m] [LawfulPureEvalDistSemantics m] (a : α) :
    prFail (pure a : m α) = 0 := by
  simp [prFail_def]

/-- The failure probability of a branch is that of the branch taken. -/
@[simp]
theorem prFail_ite (c : Prop) [Decidable c] (mx my : m α) :
    prFail (if c then mx else my) = if c then prFail mx else prFail my := by
  split_ifs <;> rfl

/-- Mapping the outputs does not change the failure probability. -/
@[simp, grind =]
theorem prFail_map [LawfulMonad m] {β : Type} (f : α → β) (mx : m α) :
    prFail (f <$> mx) = prFail mx := by
  rw [prFail_def, prFail_def, prEvent_map]

/-- The failure probability is the mass missing from the output measure. -/
theorem prFail_eq_one_sub_evalDist_univ [LawfulMonad m] [LawfulEvalDistSemantics m]
    [MeasurableSpace α] (mx : m α) : prFail mx = 1 - 𝒟[mx] Set.univ := by
  rw [prFail_def, prEvent_true_eq_evalDist_apply_univ]

end prFail
