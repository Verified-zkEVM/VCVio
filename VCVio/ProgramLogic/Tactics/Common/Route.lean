/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Lean.Meta

/-!
# Routing program-logic goals

`classify` reads a goal's shape into a `RouteKey`, and `RouteKey.route` names the logic and the
engine that should handle the goal. The classifier is syntactic: it looks at head constants only,
on the top-level spine of the goal and of its premises, with at most one reducible `whnf`. It never
searches the term (`find?`), unifies (`isDefEq`) or tries steps speculatively. So it is cheap
enough to run in front of every `vcgen` call, and to classify every statement of a library.

Constants are named with single-backtick literals, so the module loads in any environment, and
names that are absent simply never match. `VCVioTest.ProgramLogic.Route` checks the names with
double backticks.

The key records:

* **judgment**: the head of the conclusion (a core or VCVio triple, `⊑ wp`, a relational
  judgment, `=ᵈ`, a query bound, a Foxglove entailment, or a relation `=`/`≤`/`<`/`≠`), with
  an equation at a monad type read as an equation of programs;
* **sides** of a relation: an event `Pr{…}[…]`, a measure `𝒟[·]`, a `wp`, a coupling expectation,
  a total-variation distance, `0`, `1`, or arithmetic;
* **carrier** and **interpretation** of a triple: the assertion type (`ℝ≥0∞`, `Prob`, `Prop`,
  an order dual, or a state-passing function type) and the head of the `WP` instance (lower,
  probabilistic, necessary, possible, upper, or the legacy `Std.Do`);
* **monad** and **computation** heads, and whether the precondition is `1`;
* **premises**: support membership, triples, relational triples and query bounds among the
  hypotheses, which is how most handler-invariant statements are posed.
-/

@[expose] public section

namespace OracleComp.ProgramLogic.Route

open Lean Meta

/-- The judgment a goal states. -/
inductive Judg
  | coreTriple | coreLe | vcTriple | relTriple | relWP | coupling | approxRel | evalDistEq
  | progEq | queryBound | foxWP | foxEntails | conj | rel | other
  deriving Repr, BEq, Inhabited, Hashable

/-- What one side of a relation is. -/
inductive Side
  | prEvent | evalDist | wp | expect | eRelWP | tvDist | zero | one | lit | other
  deriving Repr, BEq, Inhabited, Hashable

/-- The assertion type of a triple. -/
inductive Carrier
  | ennreal | prob | dual (c : Carrier) | prop | state (c : Carrier) | other
  deriving Repr, BEq, Inhabited, Hashable

/-- The `WP` interpretation of a triple, read off its instance. -/
inductive Interp
  | lower | prob | necessary | possible | upper | stdDo | none | unknown (n : Name)
  deriving Repr, BEq, Inhabited, Hashable

/-- Premise bits of a `RouteKey`. -/
def premiseMemSupport : UInt8 := 1
@[inherit_doc premiseMemSupport] def premiseTriple : UInt8 := 2
@[inherit_doc premiseMemSupport] def premiseRelTriple : UInt8 := 4
@[inherit_doc premiseMemSupport] def premiseQueryBound : UInt8 := 8

/-- The shape of a goal, as far as routing needs it. -/
structure RouteKey where
  judg : Judg := .other
  relOp : Option Name := none
  lhs : Side := .other
  rhs : Side := .other
  carrier : Carrier := .other
  interp : Interp := .none
  monad : Name := .anonymous
  comp : Name := .anonymous
  preOne : Bool := false
  premises : UInt8 := 0
  /-- An event of a pair-valued program, or a decided event of two draws: the shape the
  Foxglove independence routes decide. -/
  foxProdEvent : Bool := false
  /-- For a conjunction, the judgment of the conjunct that gave the route. -/
  sub : Option Judg := none
  deriving Repr, BEq, Inhabited, Hashable

/-- The logic and engine a goal is routed to. -/
inductive Route
  /-- Core `vcgen` under the scope of this interpretation. -/
  | coreVCGen (i : Interp)
  /-- VCVio's `Triple` (the lower reading), on VCVio's `vcgen` path. -/
  | vcTriple
  /-- Event and support goals, by reading. -/
  | necessary | possible | lower | upper | lowerUpper
  /-- Relational: couplings, `=ᵈ`, game-hop equations (`rvcgen`). -/
  | relational
  /-- Quantitative relational: `≈[ε]`, `eRelWP` (eRHL steps). -/
  | eRHL
  /-- Total-variation bounds (`by_upto`, `by_dist`). -/
  | upToBad
  /-- Equations of programs through `simulateQ` (handler rules). -/
  | handler
  /-- Other equations of programs (monad laws, `simp`). -/
  | progAlgebra
  /-- Query bounds (charge triples). -/
  | queryBound
  /-- Foxglove: laws, independence, conditioning. -/
  | foxglove
  /-- No route; the key is reported. -/
  | none
  deriving Repr, BEq, Inhabited, Hashable

/-! ## Constants -/

/-- Judgment heads. -/
def judgHeads : List (Name × Judg) :=
  [(`Std.WP.Triple, .coreTriple), (`OracleComp.ProgramLogic.Triple, .vcTriple),
   (`OracleComp.ProgramLogic.Relational.RelTriple, .relTriple),
   (`VCVio.ProgramLogic.RelTriple, .relTriple),
   (`OracleComp.ProgramLogic.Relational.RelWP, .relWP),
   (`OracleComp.ProgramLogic.Relational.CouplingPost, .coupling),
   (`OracleComp.ProgramLogic.Relational.ApproxRelTriple, .approxRel),
   (`EvalDistEq, .evalDistEq),
   (`OracleComp.IsQueryBound, .queryBound), (`OracleComp.IsTotalQueryBound, .queryBound),
   (`PFunctor.FreeM.IsRollBound, .queryBound), (`PFunctor.FreeM.IsTotalRollBound, .queryBound),
   (`OracleComp.IsQueryBoundP, .queryBound),
   (`Iris.BI.BIBase.Entails, .foxEntails), (`Iris.BI.BIBase.EmpValid, .foxEntails),
   (`Iris.BI.BIBase.BiEntails, .foxEntails), (`Iris.UpperSetBI.entail, .foxEntails)]

/-- Relations, with `≥` and `>` read as `≤` and `<` with the sides swapped. -/
def relHeads : List (Name × Name × Bool) :=
  [(`Eq, `Eq, false), (`LE.le, `LE.le, false), (`LT.lt, `LT.lt, false),
   (`GE.ge, `LE.le, true), (`GT.gt, `LT.lt, true), (`Ne, `Ne, false)]

/-- Interpretation heads: the `WP` instances of the readings. -/
def interpHeads : List (Name × Interp) :=
  [(`OracleComp.Lower.instWP, .lower), (`ExpectationWP.Lower.instWP, .lower),
   (`OracleComp.Probabilistic.instWP_prob, .prob), (`ExpectationWP.Probabilistic.instWP, .prob),
   (`OracleComp.Necessary.instWP, .necessary), (`MonadAttach.toWPMonadDemonic, .necessary),
   (`MonadAttach.toWPMonadAngelic, .possible), (`ExactWPMonad.dual, .upper)]

/-- Monad heads whose equations are equations of programs. -/
def monadHeads : List Name :=
  [`OracleComp, `PFunctor.FreeM, `StateT, `ReaderT, `OptionT, `ExceptT, `WriterT, `ProbComp]

/-- Heads that mark a computation run through a handler. -/
def handlerHeads : List Name := [`simulateQ, `StateT.run, `StateT.run', `simulateQ']

/-- Arithmetic heads: a side built from numbers. -/
def arithHeads : List Name :=
  [`HDiv.hDiv, `HMul.hMul, `HAdd.hAdd, `HSub.hSub, `HPow.hPow, `Inv.inv, `OfNat.ofNat,
   `Nat.cast, `NNReal.toReal, `ENNReal.ofReal, `ENNReal.ofNNReal, `Real.toNNReal, `min, `max]

/-- Query-bound and cost predicates, by name: `Uses…Cost…`, `Is…Query…Bound`, … -/
def isCostHead (n : Name) : Bool :=
  match n with
  | .str _ s =>
    (s.startsWith "Uses" || s.startsWith "uses" || s.startsWith "Is") &&
      ((s.splitOn "Cost").length > 1 || (s.splitOn "Quer").length > 1) &&
      ((s.splitOn "Bound").length > 1 || (s.splitOn "AtMost").length > 1 ||
        (s.splitOn "Exactly").length > 1 || (s.splitOn "AtLeast").length > 1 ||
        (s.splitOn "Cost").length > 1)
  | _ => false

/-! ## Reading the spine -/

/-- The head constant of `e`, looking through metadata. -/
def headConst? (e : Expr) : Option Name := e.consumeMData.getAppFn.consumeMData.constName?

def lookup {β : Type} (l : List (Name × β)) (n : Name) : Option β :=
  (l.find? (·.1 == n)).map (·.2)

/-- `e` is the numeral `k` (`OfNat.ofNat _ k _`, `Zero.zero`, `One.one`). -/
def isNumeral (e : Expr) (k : Nat) : Bool :=
  let e := e.consumeMData
  if e.isAppOfArity ``OfNat.ofNat 3 then
    match (e.getArg! 1).consumeMData with
    | .lit (.natVal n) => n == k
    | _ => false
  else (k == 0 && e.isAppOf ``Zero.zero) || (k == 1 && e.isAppOf ``One.one)

/-- What one side of a relation is. -/
def sideKind (e : Expr) : Side :=
  if isNumeral e 0 then .zero else if isNumeral e 1 then .one else
  match headConst? e with
  | some `prEvent => .prEvent
  | some `evalDist => .evalDist
  | some `DFunLike.coe =>
    -- `𝒟[mx] s`: a measure applied to a set
    if headConst? (e.consumeMData.getArg! 4) == some `evalDist then .evalDist else .other
  | some `Std.WP.WP.wp | some `OracleComp.ProgramLogic.wp => .wp
  | some `OracleComp.ProgramLogic.Relational.eRelWP => .eRelWP
  | some `measureETVDist | some `measureTVDist => .tvDist
  | some `tsum | some `MeasureTheory.lintegral => .expect
  | some n => if arithHeads.contains n then .lit else .other
  | none => .other

/-- The assertion type `t`. -/
partial def carrierOf (t : Expr) : Carrier :=
  let t := t.consumeMData
  match t with
  | .sort .zero => .prop
  | .forallE _ _ b _ => .state (carrierOf b)
  | _ =>
    match headConst? t with
    | some `ENNReal => .ennreal
    | some `OracleComp.Prob | some `Prob => .prob
    | some `OrderDual => .dual (carrierOf t.consumeMData.appArg!)
    | _ => .other

/-- The body of a definition, under its lambdas. -/
def defBody? (env : Environment) (n : Name) : Option Expr :=
  match env.find? n with
  | some (.defnInfo d) =>
    let rec strip : Expr → Expr
      | .lam _ _ b _ => strip b
      | e => e
    some (strip d.value)
  | _ => none

/-- The interpretation of a `WP` instance: the first known reading among the instance's head,
its arguments and, for an instance constant of the caller's own (such as a scoped instance built
from `ExactWPMonad.dual`), its definition, to a bounded depth. A goal's instance is typically
core's generic instance applied to the reading's `WPMonad` instance. -/
partial def interpOf (env : Environment) (e : Expr) (depth : Nat := 3) : Interp :=
  match headConst? e with
  | none => .none
  | some n =>
    if let some i := lookup interpHeads n then i
    else if (`Std.Do).isPrefixOf n then .stdDo
    else if depth == 0 then .unknown n
    else
      let known (i : Interp) : Option Interp :=
        match i with
        | .none | .unknown _ => none
        | i => some i
      let fromArgs := e.consumeMData.getAppArgs.reverse.findSome? fun a ↦
        known (interpOf env a (depth - 1))
      let fromDef := (defBody? env n).bind fun b ↦ known (interpOf env b (depth - 1))
      (fromArgs <|> fromDef).getD (.unknown n)

/-- Positions of the arguments routing reads, from the binders of `c`'s type: the assertion
type (`Pred`), the program type (`Prog`), the program (`x`/`oa`/`mx`), the precondition (`pre`)
and the `WP` instance. -/
structure ArgPos where
  pred? : Option Nat := none
  prog? : Option Nat := none
  comp? : Option Nat := none
  pre? : Option Nat := none
  inst? : Option Nat := none

/-- `ArgPos` of a constant. -/
def argPos (c : Name) : MetaM ArgPos := do
  let some ci := (← getEnv).find? c | return {}
  let mut pos : ArgPos := {}
  let mut t := ci.type
  let mut i := 0
  while t.isForall do
    let .forallE n d b _ := t | break
    let s := n.eraseMacroScopes.toString
    if s == "Pred" && pos.pred?.isNone then pos := { pos with pred? := some i }
    if s == "Prog" && pos.prog?.isNone then pos := { pos with prog? := some i }
    if (s == "x" || s == "oa" || s == "mx" || s == "t") && pos.comp?.isNone then
      pos := { pos with comp? := some i }
    if s == "pre" && pos.pre?.isNone then pos := { pos with pre? := some i }
    if d.getForallBody.getAppFn.constName? == some `Std.WP.WP && pos.inst?.isNone then
      pos := { pos with inst? := some i }
    t := b
    i := i + 1
  return pos

def argAt? (e : Expr) (i? : Option Nat) : Option Expr :=
  i?.bind fun i ↦ if i < e.getAppNumArgs then some (e.getArg! i) else none

/-- Fill in carrier, interpretation, monad, computation and `preOne` from a triple-like
application `e` of the constant `c`. -/
def readTriple (key : RouteKey) (e : Expr) (c : Name) : MetaM RouteKey := do
  let pos ← argPos c
  let mut key := key
  if let some p := argAt? e pos.pred? then key := { key with carrier := carrierOf p }
  if let some inst := argAt? e pos.inst? then key := { key with interp := interpOf (← getEnv) inst }
  if let some prog := argAt? e pos.prog? then
    key := { key with monad := (headConst? prog).getD .anonymous }
  if let some x := argAt? e pos.comp? then
    let x := x.consumeMData
    let x ← if (headConst? x).isSome then pure x else whnfR x
    key := { key with comp := (headConst? x).getD .anonymous }
  if let some pre := argAt? e pos.pre? then key := { key with preOne := isNumeral pre 1 }
  return key

/-- The premise bits of a hypothesis type. -/
def premiseBits (t : Expr) : UInt8 :=
  let t := t.consumeMData
  match headConst? t with
  | some `Membership.mem =>
    if t.getAppNumArgs ≥ 4 &&
        ((headConst? (t.getArg! 3)).any ([`MonadAttach.support, `HasEvalFinset.finSupport].contains ·)
          || (headConst? (t.getArg! (t.getAppNumArgs - 1))).any
            ([`MonadAttach.support, `HasEvalFinset.finSupport].contains ·))
    then premiseMemSupport else 0
  | some n =>
    match lookup judgHeads n with
    | some .coreTriple | some .vcTriple => premiseTriple
    | some .relTriple | some .relWP | some .coupling | some .approxRel => premiseRelTriple
    | some .queryBound => premiseQueryBound
    | _ => 0
  | none => 0

/-- `e` is `fun _ ↦ body`; its body, else `none`. -/
def lamBody? (e : Expr) : Option Expr :=
  match e.consumeMData with
  | .lam _ _ b _ => some b.consumeMData
  | _ => none

/-- Whether a relation side `e` is an event of a pair-valued program (`Pr{let x ← oa}[p x]` with
`p` a function on pairs), or a decided event of two draws, `𝒟[do let a ← A; let b ← B a;
return decide …] {true}`: the shapes the Foxglove independence routes decide. A bounded syntactic
match. -/
def isProdEvent (e : Expr) : Bool :=
  let e := e.consumeMData
  match headConst? e with
  | some `prEvent =>
    -- `Pr{let x ← oa}[p x]` is `prEvent (p <$> oa)`
    let mx := e.getAppArgs.back!.consumeMData
    if mx.isAppOf ``Functor.map && mx.getAppNumArgs ≥ 6 then
      match (mx.getArg! 4).consumeMData with
      | .lam _ d _ _ => headConst? d == some ``Prod
      | _ => false
    else false
  | some `DFunLike.coe =>
    if e.getAppNumArgs < 6 || headConst? (e.getArg! 4) != some `evalDist then false else
    let mx := (e.getArg! 4).getAppArgs.back!.consumeMData
    let decidedTwoDraws : Option Bool := do
      guard (mx.isAppOf ``Bind.bind)
      let b₁ ← lamBody? mx.getAppArgs.back!
      guard (b₁.isAppOf ``Bind.bind)
      let b₂ ← lamBody? b₁.getAppArgs.back!
      guard (b₂.isAppOf ``Pure.pure)
      return headConst? b₂.getAppArgs.back! == some ``Decidable.decide
    decidedTwoDraws.getD false
  | _ => false

/-! ## Routes -/

/-- The route of a key. A Foxglove candidate (`foxProdEvent`) keeps its reading's route; the
Foxglove routes are tried first, all-or-nothing, by `vcgen`. -/
partial def RouteKey.route (k : RouteKey) : Route :=
  match k.judg with
  | .coreTriple | .coreLe =>
    match k.interp with
    | .none | .unknown _ => .none
    | i => .coreVCGen i
  | .vcTriple => .vcTriple
  | .relTriple | .relWP | .coupling | .evalDistEq => .relational
  | .approxRel => .eRHL
  | .queryBound => .queryBound
  | .foxWP | .foxEntails => .foxglove
  | .progEq => if handlerHeads.contains k.comp then .handler else .progAlgebra
  | .conj => match k.sub with
    | some j => { k with judg := j, sub := none }.route
    | none => .none
  | .rel =>
    -- a probability-like side: an event, a measure, or a `wp`
    let probSide (s : Side) := s == .prEvent || s == .evalDist || s == .wp || s == .expect
    if k.lhs == .tvDist || k.rhs == .tvDist then .upToBad
    else if k.lhs == .eRelWP || k.rhs == .eRelWP then .eRHL
    else match k.relOp, k.lhs, k.rhs with
    | some `Membership.mem, _, _ => .possible
    | some `Eq, l, r =>
      if probSide l && probSide r then .relational
      else if probSide l || probSide r then
        let bound := if probSide l then r else l
        if bound == .one then .necessary else if bound == .zero then .upper else .lowerUpper
      else if k.premises &&& premiseMemSupport != 0 then .necessary else .none
    | some `LE.le, l, r =>
      if probSide r && !probSide l then .lower
      else if probSide l && !probSide r then .upper
      else if probSide l && probSide r then .relational
      else if k.premises &&& premiseMemSupport != 0 then .necessary else .none
    | some `LT.lt, l, r =>
      if l == .zero && probSide r then .possible
      else if probSide l && !probSide r then .upper
      else if probSide r then .lower else .none
    | some `Ne, l, r =>
      if (probSide l && r == .zero) || (probSide r && l == .zero) then .possible else .none
    | _, _, _ => .none
  | .other => if k.premises &&& premiseMemSupport != 0 then .necessary else .none

/-- A short tag for an interpretation. -/
def Interp.tag : Interp → String
  | .lower => "lower" | .prob => "prob" | .necessary => "necessary"
  | .possible => "possible" | .upper => "upper" | .stdDo => "stdDo" | .none => "none"
  | .unknown n => s!"unknown {n}"

/-- A short tag for a route, for diagnostics and tests. -/
def Route.tag : Route → String
  | .coreVCGen i => "core:" ++ i.tag
  | .vcTriple => "vcTriple" | .necessary => "necessary" | .possible => "possible"
  | .lower => "lower" | .upper => "upper" | .lowerUpper => "lowerUpper"
  | .relational => "relational" | .eRHL => "eRHL" | .upToBad => "upToBad"
  | .handler => "handler" | .progAlgebra => "progAlgebra" | .queryBound => "queryBound"
  | .foxglove => "foxglove"
  | .none => "none"

/-- A key's route tag, with `+fox` when the Foxglove independence routes are also candidates. -/
def RouteKey.tag (k : RouteKey) : String :=
  k.route.tag ++ if k.foxProdEvent && k.route != .foxglove then "+fox" else ""

/-! ## The classifier -/

/-- Whether `ty` is `m α` for a variable `m : Type u → Type v`: a program in a generic monad. -/
def isMonadVarApp (ty : Expr) : MetaM Bool := do
  let f := ty.getAppFn.consumeMData
  unless f.isFVar && ty.getAppNumArgs ≥ 1 do return false
  match (← whnfR (← inferType f)) with
  | .forallE _ (.sort _) (.sort _) _ => return true
  | _ => return false

/-- Classify a conclusion `e`, with premise bits `prem`. -/
partial def classifyConcl (e : Expr) (prem : UInt8) : MetaM RouteKey := do
  let e := (← instantiateMVars e).consumeMData
  let e := if e.isAppOfArity ``Not 1 then e.appArg!.consumeMData else e
  let mut key : RouteKey := { premises := prem }
  let some head := headConst? e | return key
  if (lookup judgHeads head).isNone && isCostHead head then
    return { key with judg := .queryBound }
  if let some j := lookup judgHeads head then
    key := { key with judg := j }
    if j == .foxEntails then
      if e.getAppNumArgs > 0 && headConst? e.appArg! == some `Foxglove.wp then
        key := { key with judg := .foxWP }
      return key
    if j == .coreTriple || j == .vcTriple then
      key ← readTriple key e head
      if j == .vcTriple then
        key := { key with carrier := .ennreal, interp := .lower, monad := `OracleComp }
    return key
  if head == `Lean.Order.PartialOrder.rel && e.getAppNumArgs == 4 then
    let rhs := e.getArg! 3
    if let some w := headConst? rhs then
      if w == `Std.WP.WP.wp || w == `OracleComp.ProgramLogic.wp then
        key := { key with judg := .coreLe }
        key ← readTriple key rhs w
        if w == `OracleComp.ProgramLogic.wp then
          key := { key with carrier := .ennreal, interp := .lower, monad := `OracleComp }
        key := { key with preOne := isNumeral (e.getArg! 2) 1 }
        return key
  if head == ``And && e.getAppNumArgs == 2 then
    -- a conjunction: the first conjunct with a route
    let l ← classifyConcl (e.getArg! 0) prem
    let r ← classifyConcl (e.getArg! 1) prem
    let k := if l.route != .none then l else r
    return { k with judg := .conj, sub := some k.judg }
  if head == ``Membership.mem && e.getAppNumArgs ≥ 5 then
    -- `x ∈ support oa`: a possibility
    if (headConst? (e.getArg! 3)).any ([`MonadAttach.support, `HasEvalFinset.finSupport].contains ·)
    then return { key with judg := .rel, relOp := some ``Membership.mem, lhs := .prEvent }
  if let some (op, swap) := (relHeads.find? (·.1 == head)).map (·.2) then
    let n := e.getAppNumArgs
    if n < 2 then return key
    let (l, r) := (e.getArg! (n - 2), e.getArg! (n - 1))
    let (l, r) := if swap then (r, l) else (l, r)
    key := { key with judg := .rel, relOp := some op, lhs := sideKind l, rhs := sideKind r }
    if op == `Eq then
      -- an equation of programs
      let ty := (e.getArg! 0).consumeMData
      if (headConst? ty).any monadHeads.contains || (← isMonadVarApp ty) then
        key := { key with judg := .progEq, comp := (headConst? l).getD .anonymous }
        return key
    key := { key with foxProdEvent := isProdEvent l || isProdEvent r }
  return key

/-- Classify a goal: its premises (the hypotheses of a statement, or the local context of a
goal) and its conclusion. -/
def classify (e : Expr) : MetaM RouteKey := do
  let e ← instantiateMVars e
  forallTelescope e fun xs body ↦ do
    let mut prem : UInt8 := 0
    for x in xs do
      prem := prem ||| premiseBits (← inferType x)
    classifyConcl body prem

/-- Classify a goal in its local context: the hypotheses count as premises. -/
def classifyGoal (g : MVarId) : MetaM RouteKey := g.withContext do
  let mut prem : UInt8 := 0
  for d in ← getLCtx do
    if !d.isImplementationDetail then prem := prem ||| premiseBits d.type
  let key ← classify (← g.getType)
  return { key with premises := key.premises ||| prem }

end OracleComp.ProgramLogic.Route
