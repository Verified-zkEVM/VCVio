/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Defs.Measure.Core
public import VCVio.EvalDist.ProbabilityNotation.Attr
public meta import Lean.PrettyPrinter.Formatter
public meta import Lean.PrettyPrinter.Delaborator.Basic

/-!
# Event probabilities of computations

`prEvent mx` is the mass that the successful-output measure of `mx : m Prop` puts on `True`.
`Pr{…}[…]` is its notation. The sequence between the braces is either a list of draws
`x ← mx; y ← my x`, whose actions may continue on following lines, or an ordinary Lean `do`
sequence. `Pr{mx}[= a]` is the probability that `mx` returns `a`. The notation elaborates to the
form `simp` maintains: the final draw becomes a map, `Pr{x ← mx}[p x] = prEvent (p <$> mx)`, so
event laws keyed on `prEvent` apply to derived programs.

The equations below identify an event with the measure of a set when the event is measurable.
-/

public section

open MeasureTheory
open scoped ENNReal

universe v

/-- The probability that a computation returns a true proposition: the mass its successful-output
measure puts on `True`. -/
@[expose] noncomputable def prEvent {m : Type → Type v} [EvalDistSemantics m] (mx : m Prop) :
    ℝ≥0∞ :=
  𝒟[mx] {True}

theorem prEvent_def {m : Type → Type v} [EvalDistSemantics m] (mx : m Prop) :
    prEvent mx = 𝒟[mx] {True} := rfl

/-- The mass a proposition-valued computation puts on `True` is its event probability, the form
the event laws are stated in. -/
@[simp, grind norm]
theorem evalDist_singleton_true {m : Type → Type v} [EvalDistSemantics m] (mx : m Prop) :
    𝒟[mx] {True} = prEvent mx := rfl

attribute [prEvent_norm] map_bind bind_pure_comp Functor.map_map Function.comp_def map_pure
  bind_assoc pure_bind bind_map_left id_map'

/-- A draw `x ← e` in `Pr{…}[…]`, optionally with a type ascription on `x`. -/
syntax prEventBind := ident (" : " term)? " ← " term

/-- Probability of an event after a sequence of draws `x ← e` separated by `;`. Each action may
continue on the following lines. -/
syntax (name := prEventBindsStx) (priority := high)
  "Pr{" withoutPosition(sepBy1(prEventBind, "; ")) "}[" term "]" : term

/-- Probability of a successful event after an ordinary Lean `do` sequence. -/
syntax (name := prEventStx) "Pr{" doSeq "}[" term "]" : term

/-- Probability that a computation returns the given value. -/
syntax (name := prEventEqStx) "Pr{" term "}[" "=" ppSpace term "]" : term

public meta section Formatting

open Lean PrettyPrinter Formatter Syntax.MonadTraverser

/-- Format an event sequence directly after its opening delimiter, keeping the ordinary Lean
formatter for subsequent statements and explicitly braced sequences. Explicit line breaks
after the opening delimiter are preserved. -/
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
      visitArgs <| visitArgs do
        for i in [:n] do
          if i + 1 == n then
            visitArgs do
              optionalNoAntiquot.formatter (symbolNoAntiquot.formatter "; ")
              categoryParser.formatter `doElem
          else
            formatterForKind ``Lean.Parser.Term.doSeqItem
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
  unless action.isOfKind ``Lean.Parser.Term.doExpr do return (items, t)
  let pat : Term := ⟨decl[0]⟩
  let e : Term := ⟨action[0]⟩
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

macro_rules (kind := prEventBindsStx)
  | `(Pr{$[$xs:ident $[: $tys]? ← $es];*}[$t]) => do
    let items ← (xs.zip (tys.zip es)).mapM fun (x, ty?, e) => match ty? with
      | some ty => `(Lean.Parser.Term.doSeqItem| let $x:ident : $ty ← $e:term)
      | none => `(Lean.Parser.Term.doSeqItem| let $x:ident ← $e:term)
    `((prEvent% {$items*}[$t] : ENNReal))

macro_rules (kind := prEventEqStx)
  | `(Pr{$mx}[= $a]) => `(prEvent ((· = $a) <$> $mx))

public meta section Delaboration

open Lean PrettyPrinter Delaborator SubExpr

/-- The draws of a normalized event: a chain of binds ending in a map of the final selector. -/
partial def delabPrEventDraws : DelabM (Array (TSyntax ``prEventBind) × Term) := do
  let e ← getExpr
  if e.isAppOfArity ``Bind.bind 6 then
    let a ← withNaryArg 4 delab
    withNaryArg 5 do
      unless (← getExpr).isLambda do failure
      withBindingBodyUnusedName fun x => do
        let (draws, t) ← delabPrEventDraws
        return (#[← `(prEventBind| $(⟨x⟩):ident ← $a)] ++ draws, t)
  else if e.isAppOfArity ``Functor.map 6 then
    let a ← withNaryArg 5 delab
    withNaryArg 4 do
      if (← getExpr).isLambda then
        withBindingBodyUnusedName fun x => do
          return (#[← `(prEventBind| $(⟨x⟩):ident ← $a)], ← delab)
      else
        let f ← delab
        let x := mkIdent `x
        return (#[← `(prEventBind| $x:ident ← $a)], ← `($f $x))
  else failure

/-- Display `prEvent` in the notation it elaborates from. -/
@[delab app.prEvent]
def delabPrEvent : Delab := whenPPOption getPPNotation <| withOverApp 3 do
  withNaryArg 2 do
    let e ← getExpr
    if e.isAppOfArity ``Functor.map 6 then
      let f := e.getArg! 4
      if let .lam _ _ body _ := f then
        if body.isAppOfArity ``Eq 3 && body.appFn!.appArg! == .bvar 0 &&
            !body.appArg!.hasLooseBVars then
          let mx ← withNaryArg 5 delab
          let a ← withNaryArg 4 <| withBindingBody `x <| withNaryArg 2 delab
          return ← `(Pr{$mx}[= $a])
    let (draws, t) ← delabPrEventDraws
    `(Pr{$draws;*}[$t])

end Delaboration

/-- An event is the true mass of its propositional selector. -/
theorem prEvent_eq_evalDist_map
    {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) :
    Pr{x ← mx}[p x] = 𝒟[p <$> mx] {True} := rfl

/-- A measurable predicate returned by a computation has the probability of its event. -/
theorem prEvent_eq_evalDist {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] (mx : m α) (p : α → Prop)
    (hp : Measurable p) :
    Pr{let x ← mx}[p x] = 𝒟[mx] {x | p x} := by
  rw [prEvent_eq_evalDist_map, evalDist_map_apply mx hp (measurableSet_singleton True)]
  simp

/-- On a discrete output space every predicate is a measurable event. -/
theorem prEvent_eq_evalDist_of_discrete
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : m α) (p : α → Prop) :
    Pr{let x ← mx}[p x] = 𝒟[mx] {x | p x} :=
  prEvent_eq_evalDist mx p Measurable.of_discrete

/-- Equality to one output has its singleton mass whenever singletons are measurable. -/
theorem prEvent_eq_evalDist_singleton
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] (mx : m α) (a : α) :
    Pr{let x ← mx}[x = a] = 𝒟[mx] {a} := by
  simpa only [Set.ofPred_eq_eq_singleton] using
    prEvent_eq_evalDist mx (fun x ↦ x = a) (measurableSet_singleton a).mem

/-- A final decidable event has the same success mass whether it is returned as a proposition
or decided to a Boolean; no measurable structure on intermediate values is needed. -/
theorem prEvent_eq_evalDist_decide
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) [DecidablePred p] :
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

/-- Pointwise equivalent predicates have the same probability after a common computation. -/
theorem prEvent_congr
    {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {α : Type} (mx : m α) (p q : α → Prop) (h : ∀ x, p x ↔ q x) :
    Pr{let x ← mx}[p x] = Pr{let x ← mx}[q x] := by
  have hpq : p = q := funext fun x ↦ propext (h x)
  rw [hpq]

/-- Measurable predicates agreeing almost everywhere have equal event probabilities. -/
theorem prEvent_congr_ae
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] (mx : m α) (p q : α → Prop)
    (hp : Measurable p) (hq : Measurable q) (h : ∀ᵐ x ∂𝒟[mx], p x ↔ q x) :
    Pr{let x ← mx}[p x] = Pr{let x ← mx}[q x] := by
  rw [prEvent_eq_evalDist mx p hp, prEvent_eq_evalDist mx q hq]
  exact measure_congr (h.mono fun _ hx ↦ propext hx)

/-- An event that never occurs has probability zero. -/
theorem prEvent_eq_zero_of_forall_not
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p : α → Prop) (h : ∀ x, ¬p x) :
    Pr{let x ← mx}[p x] = 0 := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete]
  simp [h]

/-- Almost-everywhere implication bounds probabilities of measurable events. -/
theorem prEvent_mono_ae
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] (mx : m α) (p q : α → Prop)
    (hp : Measurable p) (hq : Measurable q) (hpq : ∀ᵐ x ∂𝒟[mx], p x → q x) :
    Pr{let x ← mx}[p x] ≤ Pr{let x ← mx}[q x] := by
  rw [prEvent_eq_evalDist mx p hp, prEvent_eq_evalDist mx q hq]
  exact measure_mono_ae hpq

/-- Implication between events bounds their probabilities on a discrete output space. -/
theorem prEvent_mono_of_discrete
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : m α) (p q : α → Prop) (hpq : ∀ x, p x → q x) :
    Pr{let x ← mx}[p x] ≤ Pr{let x ← mx}[q x] := by
  rw [prEvent_eq_evalDist_of_discrete,
    prEvent_eq_evalDist_of_discrete]
  exact measure_mono (Set.ofPred_subset_ofPred.mpr hpq)

/-- Implication between final events bounds their probabilities without a measurable-space
argument on the intermediate values. -/
theorem prEvent_mono
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} (mx : m α) (p q : α → Prop) (hpq : ∀ x, p x → q x) :
    Pr{let x ← mx}[p x] ≤ Pr{let x ← mx}[q x] := by
  let obs : α → Prop × Prop := fun x ↦ (p x, q x)
  let : MeasurableSpace α := MeasurableSpace.comap obs inferInstance
  have hobs : Measurable obs := comap_measurable obs
  exact prEvent_mono_ae mx p q (measurable_fst.comp hobs) (measurable_snd.comp hobs)
    (Filter.Eventually.of_forall hpq)

/-- An observed bind integrates the event probability of each measurable continuation.
Only the common draw needs a selected measurable space; the continuation is observed in `Prop`.
-/
theorem prEvent_bind_eq_lintegral
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type} [MeasurableSpace α] (mx : m α) (f : α → m β) (p : β → Prop)
    (hf : Measurable fun x ↦ 𝒟[p <$> f x]) :
    Pr{let y ← mx >>= f}[p y] = ∫⁻ x, Pr{let y ← f x}[p y] ∂𝒟[mx] := by
  rw [prEvent_def, map_bind, evalDist_bind _ _ hf,
    Measure.bind_apply (measurableSet_singleton True) hf.aemeasurable]
  rfl

/-- A bind of event computations integrates the continuation's event over a measurable source. -/
theorem prEvent_bind
    {m : Type → Type v} [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] (mx : m α) (f : α → m Prop)
    (hf : Measurable fun x ↦ 𝒟[f x]) :
    prEvent (mx >>= f) = ∫⁻ x, prEvent (f x) ∂𝒟[mx] := by
  rw [prEvent_def, evalDist_bind _ _ hf,
    Measure.bind_apply (measurableSet_singleton True) hf.aemeasurable]
  rfl

/-- A bind of event computations integrates the continuation's event over a discrete source. -/
theorem prEvent_bind_of_discrete
    {m : Type → Type v} [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α] (mx : m α) (f : α → m Prop) :
    prEvent (mx >>= f) = ∫⁻ x, prEvent (f x) ∂𝒟[mx] :=
  prEvent_bind mx f Measurable.of_discrete

/-- A discrete common draw discharges the observed continuation's measurability. -/
theorem prEvent_bind_eq_lintegral_of_discrete
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : m α) (f : α → m β) (p : β → Prop) :
    Pr{let y ← mx >>= f}[p y] = ∫⁻ x, Pr{let y ← f x}[p y] ∂𝒟[mx] :=
  prEvent_bind_eq_lintegral mx f p Measurable.of_discrete

/-- AE equality of measurable observed continuation probabilities gives equality after a draw. -/
theorem prEvent_bind_congr_ae
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β γ : Type} [MeasurableSpace α] (mx : m α) (f : α → m β) (g : α → m γ)
    (p : β → Prop) (q : γ → Prop)
    (hf : Measurable fun x ↦ 𝒟[p <$> f x])
    (hg : Measurable fun x ↦ 𝒟[q <$> g x])
    (h : ∀ᵐ x ∂𝒟[mx], Pr{let y ← f x}[p y] = Pr{let z ← g x}[q z]) :
    Pr{let y ← mx >>= f}[p y] = Pr{let z ← mx >>= g}[q z] := by
  rw [prEvent_bind_eq_lintegral mx f p hf, prEvent_bind_eq_lintegral mx g q hg]
  exact lintegral_congr_ae h

/-- Pointwise equality of observed continuation probabilities gives equality after a common
draw. Neither the draw nor the continuation outputs need a measurable-space argument. -/
theorem prEvent_bind_congr
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β γ : Type} (mx : m α) (f : α → m β) (g : α → m γ)
    (p : β → Prop) (q : γ → Prop)
    (h : ∀ x,
      Pr{let y ← f x}[p y] = Pr{let z ← g x}[q z]) :
    Pr{let y ← mx >>= f}[p y] = Pr{let z ← mx >>= g}[q z] := by
  let obs : α → Measure Prop × Measure Prop := fun x ↦ (𝒟[p <$> f x], 𝒟[q <$> g x])
  let : MeasurableSpace α := MeasurableSpace.comap obs inferInstance
  have hobs : Measurable obs := comap_measurable obs
  exact prEvent_bind_congr_ae mx f g p q (measurable_fst.comp hobs)
    (measurable_snd.comp hobs) (Filter.Eventually.of_forall h)

/-- An output map composes the final event with that map. -/
@[grind norm]
theorem prEvent_map
    {m : Type → Type v} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    {α β : Type} (mx : m α) (f : α → β) (p : β → Prop) :
    Pr{let y ← f <$> mx}[p y] = Pr{let x ← mx}[p (f x)] := by
  rw [Functor.map_map]

/-- An event of a conditional computation is the conditional event. -/
theorem prEvent_ite {m : Type → Type v} [EvalDistSemantics m] (c : Prop) [Decidable c]
    (mx my : m Prop) : prEvent (if c then mx else my) = if c then prEvent mx else prEvent my := by
  split_ifs <;> rfl

/-- An event of a dependent conditional computation is the dependent conditional event. -/
theorem prEvent_dite {m : Type → Type v} [EvalDistSemantics m] (c : Prop) [Decidable c]
    (mx : c → m Prop) (my : ¬c → m Prop) :
    prEvent (if h : c then mx h else my h) = if h : c then prEvent (mx h) else prEvent (my h) := by
  split_ifs <;> rfl

/-- A returned proposition has probability one exactly when it holds. -/
@[simp, grind =]
theorem prEvent_pure_prop
    {m : Type → Type v} [Monad m] [EvalDistSemantics m] [LawfulPureEvalDistSemantics m]
    (P : Prop) [Decidable P] :
    prEvent (pure P : m Prop) = if P then 1 else 0 := by
  rw [prEvent_def, evalDist_pure]
  by_cases h : P <;> simp [h]

/-- An event of a pure computation has probability one exactly when it holds. -/
@[grind =]
theorem prEvent_pure
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulPureEvalDistSemantics m]
    {α : Type} (a : α) (p : α → Prop) [Decidable (p a)] :
    Pr{let x ← (pure a : m α)}[p x] = if p a then 1 else 0 := by
  rw [map_pure, prEvent_pure_prop]

/-- After a draw from a finite type, an event is the finite sum of the draw's point masses times
the conditional event probabilities. -/
theorem prEvent_bind_eq_sum_fintype
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type} [Fintype α] (mx : m α) (f : α → m β) (p : β → Prop) :
    Pr{let y ← mx >>= f}[p y] = ∑ a, Pr{let x ← mx}[x = a] * Pr{let y ← f a}[p y] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, MeasureTheory.lintegral_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm, prEvent_eq_evalDist_singleton]

/-- Events of independent draws have the product of their probabilities. -/
@[simp↓ high, grind norm↓]
theorem prEvent_bind_bind_and
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    {α β : Type} (mx : m α) (my : m β) (p : α → Prop) (q : β → Prop) :
    Pr{let x ← mx; let y ← my}[p x ∧ q y] =
      Pr{let x ← mx}[p x] * Pr{let y ← my}[q y] := by
  calc
    _ = Pr{let z ← (do
          let x ← p <$> mx
          let y ← q <$> my
          return (x, y))}[z.1 ∧ z.2] := by
      simp only [map_bind, bind_map_left, bind_pure_comp, Functor.map_map]
    _ = (𝒟[p <$> mx].prod 𝒟[q <$> my]) ({True} ×ˢ {True}) := by
      rw [prEvent_eq_evalDist_of_discrete, evalDist_pair]
      congr 1
      ext z
      simp [Prod.ext_iff, eq_iff_iff]
    _ = _ := by
      rw [Measure.prod_prod]
      rfl

/-- Every event probability is at most one. -/
@[simp]
theorem prEvent_le_one {m : Type → Type v} [EvalDistSemantics m] (mx : m Prop) :
    prEvent mx ≤ 1 :=
  evalDist_apply_le_one _ _

/-- Every event probability is finite. -/
@[simp]
theorem prEvent_ne_top {m : Type → Type v} [EvalDistSemantics m] (mx : m Prop) :
    prEvent mx ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (prEvent_le_one mx)

/-- Every event probability is finite. -/
@[simp]
theorem prEvent_lt_top {m : Type → Type v} [EvalDistSemantics m] (mx : m Prop) :
    prEvent mx < ⊤ :=
  (prEvent_ne_top mx).lt_top

/-- The trivially true event is the successful mass of the computation, observed in the discrete
structure on its outputs. -/
theorem prEvent_true_eq_evalDist_apply_univ
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} (mx : m α) :
    Pr{let _ ← mx}[True] = (letI : MeasurableSpace α := ⊤; 𝒟[mx] Set.univ) := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete]
  simp

/-- A prefix whose result is unused scales the event by its successful mass. -/
@[simp]
theorem prEvent_bind_const
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} (mx : m α) (my : m Prop) :
    prEvent (mx >>= fun _ ↦ my) = Pr{let _ ← mx}[True] * prEvent my := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_true_eq_evalDist_apply_univ]
  change 𝒟[mx >>= fun _ ↦ my] {True} = 𝒟[mx] Set.univ * 𝒟[my] {True}
  rw [evalDist_bind_const, Measure.smul_apply, smul_eq_mul]

/-- Computations with the same output measure in the discrete structure have the same events. -/
theorem prEvent_congr_of_evalDist_eq
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type} (mx my : m α)
    (h : (letI : MeasurableSpace α := ⊤; 𝒟[mx] = 𝒟[my])) (p : α → Prop) :
    Pr{let x ← mx}[p x] = Pr{let y ← my}[p y] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete, h]

/-- A true constant event after a lossless draw has probability one. -/
theorem prEvent_const_of_lossless
    {m : Type → Type v} [Monad m] [EvalDistSemantics m] {α : Type}
    (mx : m α) (hmx : Pr{let _ ← mx}[True] = 1) {c : Prop} (hc : c) :
    Pr{let _ ← mx}[c] = 1 := by
  rw [← hmx]
  exact prEvent_congr mx _ _ fun _ ↦ by simp [hc]

/-- A false constant event has probability zero. -/
theorem prEvent_const_of_not
    {m : Type → Type v} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α : Type}
    (mx : m α) {c : Prop} (hc : ¬ c) : Pr{let _ ← mx}[c] = 0 :=
  prEvent_eq_zero_of_forall_not mx _ fun _ ↦ hc
