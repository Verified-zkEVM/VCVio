/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Unary.WP.NecessarySpecs
public import VCVio.ProgramLogic.Unary.WP.LowerSpecs
public import VCVio.ProgramLogic.Unary.WP.Coherence
public import VCVio.ProgramLogic.Unary.WP.Possible
public import VCVio.ProgramLogic.Unary.WP.Upper
public import VCVio.ProgramLogic.Unary.WP.TransformerSpecs
public import VCVio.ProgramLogic.Unary.SimulateQSpecs
public meta import Lean.Elab.Tactic.Basic
public meta import Std.Tactic.Do

/-!
# `prvcgen`: core `vcgen` on events, under the matching reading

A statement about the outcomes of an oracle computation is a core triple under one of four
readings of `OracleComp spec`. `prvcgen` classifies the goal, states it as a triple of that reading
with its bridge lemma, and runs core's `vcgen` inside the reading's per-call scope:

| Goal | Reading | Triple |
|------|---------|--------|
| `Pr{…}[p] = 1`, `∀ x ∈ support oa, p x` | necessary | `⦃ True ⦄ oa ⦃ p ⦄` |
| `0 < Pr{…}[p]`, `∃ x ∈ support oa, p x` | possible | `⦃ True ⦄ oa ⦃ p ⦄` |
| `r ≤ Pr{…}[p]` | lower bound (`OracleComp.Lower`) | `⦃ r ⦄ oa ⦃ predInd p ⦄` |
| `Pr{…}[p] ≤ ε`, `Pr{…}[p] = 0` | upper bound | `⦃ toDual ε ⦄ oa ⦃ … ⦄` |
| `Pr{…}[p] = c` | upper and lower bound | both of the above |
| `⦃ pre ⦄ oa ⦃ post ⦄` | read off the assertion type | the goal itself |

The readings are `OracleComp.Necessary` (the global instance), `OracleComp.Possible`,
`OracleComp.Lower` and `OracleComp.Upper`. `𝔼{…}[g]` and `wp⟦oa⟧ g` stand wherever `Pr{…}[p]` does,
`≥` is read as `≤` with its sides swapped, and an equation may have the expectation on either side.
A triple already stated is run in the reading of its assertion type: `ℝ≥0∞` for lower bounds,
`ℝ≥0∞ᵒᵈ` for upper bounds, and `Prop` for the necessary reading, or the possible one when the
triple's interpretation is possible; a state-passing assertion `σ → …` is read by its codomain, so
triples of handlers over `StateT` are run the same way.

The event forms nest one expectation per draw; the bridges rewrite each nested expectation into
the reading, so `vcgen` steps through the whole program. The necessary and possible bridges of an
event need answers of positive mass; `prvcgen` uses their uniform-answer forms
(`UniformAnswerMeasure`). The shapes `vcgen` reads itself — a triple, its unfolded form
`pre ⊑ wp oa post epost`, and a weakest precondition of a `Prop` reading such as the
`∃ u, wp (rest u) post ⊥` a possible draw leaves once its witness is named — are only classified,
by the assertion type and the interpretation of their `wp`, and handed to `vcgen` in that reading's
scope.

## Equations

An equation `Pr{…}[p] = c`, with `c` not an expectation, splits by `le_antisymm` into the upper
bound `Pr{…}[p] ≤ c` and the lower bound `c ≤ Pr{…}[p]`, each run in its reading. Two values have
a simpler route:

* `= 0` is the upper bound alone, the lower bound `0 ≤ …` holding outright;
* `= 1` is the necessary triple when uniform answers are available, whose verification
  conditions are the event itself at every possible output and whose rule catalogue is the
  largest; otherwise it splits, the upper half closes on the range of the indicator
  (`wp_le_of_forall_le`), and the lower half is run in the expectation reading.

The split settles both halves outright with the every-outcome rules, and with a loop invariant or
handler potential that pins the value exactly. With the averaging rules each half ends in a sum,
which `simp` on the normal form evaluates. An equation between the probabilities of two programs
is a program equality, a game hop, and is refused: it is proved with `prrw` (bind swaps and shared
prefixes), the couplings `rvcstep` / `rvcgen`, or the `=ᵈ` lemmas. An equation stating the value
of one program's expectation step by step, such as `wp⟦oa >>= f⟧ g = wp⟦oa⟧ fun x => wp⟦f x⟧ g`,
is `simp only [expect_norm, expect_eval]`.

## Arguments

`prvcgen` takes `vcgen`'s arguments and passes them on unchanged:
`prvcgen (config) [rules] until pat frames … invariants … simplifying_assumptions … with step`.
`prvcgen (errorOnMissingSpec := false)` leaves a program without a rule, such as an opaque
sub-program, as a verification condition stating its weakest precondition. On an equation both
halves receive the same arguments; a rule stated in the other half's reading does not match there.
An invariant shared by the two halves is written without a carrier ascription, as
`fun _ suff c => ↑c + ↑suff.length`, so that each half elaborates it in its own carrier.
`prvcgen => tac` runs `tac` in place of `vcgen`, on each half of an equation.

The verification conditions of the expectation readings are read back into `ℝ≥0∞`
(`Lean.Order.rel_eq_le`; `OracleComp.Upper.rel_iff`, `ofDual_toDual`,
`OracleComp.Upper.ofDual_wp`, and Mathlib's `ofDual_add`, …), and those an indicator's range
settles or that are reflexive are closed (`propInd_le_one`, `one_le_propInd_iff`, `le_refl`).

A comparison `Pr{A}[p] ≤ Pr{B}[q]` of two events has an expectation on both sides; `prvcgen`
reads it as an upper bound on the left-hand side, with the right-hand side as the bound.

The per-call scopes (`OracleComp.Necessary.Dispatch`, `OracleComp.Possible.Dispatch`,
`OracleComp.Lower.Dispatch`, `OracleComp.Upper.Dispatch`) register each reading above every
reading a file opens, so `prvcgen` is unaffected by the file's `open scoped` readings.
-/

public meta section

open Lean Elab Tactic Meta

/-- Discharge `∀ a, g a ≤ 1` for an observation built from indicators and nested expectations of
indicators, the side condition of the necessary bridge on an event's normal form. -/
syntax (name := prvcgenLeOne) "prvcgen_le_one" : tactic

macro_rules
  | `(tactic| prvcgen_le_one) => `(tactic| (
      intro _
      first
        | exact propInd_le_one _
        | (rw [predInd_apply]; exact propInd_le_one _)
        | (refine wp_le_of_forall_le _ ?_; prvcgen_le_one)))

namespace OracleComp.ProgramLogic.PrVCGen

/-- The four readings `prvcgen` dispatches to. -/
inductive Reading where
  /-- All possible outputs: `OracleComp.Necessary`. -/
  | necessary
  /-- Some possible output: `OracleComp.Possible`. -/
  | possible
  /-- Expectation lower bounds: `OracleComp.Lower`. -/
  | lower
  /-- Expectation upper bounds: `OracleComp.Upper`. -/
  | upper
  deriving BEq

/-- The per-call scope of a reading. -/
def Reading.scope : Reading → Name
  | .necessary => `OracleComp.Necessary.Dispatch
  | .possible => `OracleComp.Possible.Dispatch
  | .lower => `OracleComp.Lower.Dispatch
  | .upper => `OracleComp.Upper.Dispatch

/-- Whether `e` is an application of core's `wp`. -/
def isWpApp (e : Expr) : Bool :=
  e.cleanupAnnotations.isAppOf ``Std.WP.WP.wp

/-- Whether `e` is the numeral `n`. -/
def isNumeral (e : Expr) (n : Nat) : Bool :=
  let e := e.cleanupAnnotations
  e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).rawNatLit? == some n

/-- The plan for a goal: one triple of a reading, or an equation split by antisymmetry into an
upper-bound goal and a lower-bound goal. -/
inductive Plan where
  /-- The main goal is a triple of the reading. -/
  | single (reading : Reading)
  /-- The main goal was split into `wp⟦oa⟧ g ≤ c` and `c ≤ wp⟦oa⟧ g`; when `upperClosed`, the
  upper bound was settled on the range of the observation and only the lower bound remains. -/
  | split (upperClosed : Bool)

/-- The interpretation behind a `WP` instance term, by its head constant: the `WPMonad` an
instance wraps (`instWPOfWPMonad`, `WPMonad.toWP`), the interpretation of the base monad inside a
transformer's instance, and otherwise the instance seen through reducible and instance
definitions, until a `MonadAttach` interpretation or an irreducible head. -/
partial def interpretationHead? (inst : Expr) : MetaM (Option Name) := do
  let inst := inst.cleanupAnnotations
  if inst.isAppOfArity ``Std.WP.instWPOfWPMonad 8 then
    return ← interpretationHead? (inst.getArg! 7)
  if inst.isAppOfArity ``Std.WP.WPMonad.toWP 8 then
    return ← interpretationHead? (inst.getArg! 6)
  let .const n _ := inst.getAppFn | return none
  if n == ``MonadAttach.toWPMonadAngelic || n == ``MonadAttach.toWPMonadDemonic then
    return some n
  for arg in inst.getAppArgs do
    if (← inferType arg).cleanupAnnotations.isAppOf ``Std.WP.WPMonad then
      if let some h ← interpretationHead? arg then return some h
  match ← withReducibleAndInstances (unfoldDefinition? inst) with
  | some inst' => interpretationHead? inst'
  | none => return some n

/-- The reading of a triple or an entailment, read off its assertion type: `ℝ≥0∞ᵒᵈ` for the
upper-bound reading, `ℝ≥0∞` for the lower-bound reading, and `Prop` for the necessary reading, or
the possible one when the interpretation behind its `wp` is possible. A state-passing assertion
`σ → …` is read by its codomain. -/
def readingOf? (carrier inst : Expr) : MetaM (Option Reading) := do
  let carrier := carrier.cleanupAnnotations.getForallBody
  if carrier.isAppOf ``OrderDual then return some .upper
  if carrier.isConstOf ``ENNReal then return some .lower
  unless carrier.isProp do return none
  let possible := match ← interpretationHead? inst with
    | some h => h == ``MonadAttach.toWPMonadAngelic || (`OracleComp.Possible).isPrefixOf h
    | none => false
  return some (if possible then .possible else .necessary)

/-- The reading of a core triple `Triple x pre post epost`. -/
def tripleReading? (goal : Expr) : MetaM (Option Reading) := do
  unless goal.isAppOfArity ``Std.WP.Triple 11 do return none
  readingOf? (goal.getArg! 0) (goal.getArg! 7)

/-- State the necessary bridge for `wp⟦oa⟧ g = 1`, rewriting each nested expectation. -/
def bridgeEqOne : TacticM Unit := do
  evalTactic (← `(tactic| (
    simp (disch := prvcgen_le_one) only
      [OracleComp.Necessary.wp_eq_one_eq_wp, predInd_apply, propInd_eq_one_iff]
    rw [OracleComp.Necessary.wp_iff_triple])))

/-- State the main goal as a triple of the reading it belongs to, or split an equation. -/
partial def bridge (goal : Expr) : TacticM Plan := do
  let goal := goal.cleanupAnnotations
  -- a core triple, run in the reading of its assertion type
  if goal.isAppOf ``Std.WP.Triple then
    let some reading ← tripleReading? goal
      | throwError "prvcgen: a triple must have assertions in `Prop`, `ℝ≥0∞` or `ℝ≥0∞ᵒᵈ`, \
          or in functions into them{indentExpr goal}"
    return .single reading
  -- `pre ⊑ wp oa post epost`, the unfolded form of a triple, which `vcgen` reads itself
  if goal.isAppOfArity ``Lean.Order.PartialOrder.rel 4 && isWpApp (goal.getArg! 3) then
    let w := (goal.getArg! 3).cleanupAnnotations
    let some reading ← readingOf? (goal.getArg! 0) (w.getArg! 6)
      | throwError "prvcgen: an entailment must have assertions in `Prop`, `ℝ≥0∞` or `ℝ≥0∞ᵒᵈ`, \
          or in functions into them{indentExpr goal}"
    return .single reading
  -- equations: `= 1`, `= 0`, `= c`, and their symmetric forms
  if let some (_, lhs, rhs) := goal.eq? then
    if isWpApp lhs && isWpApp rhs then
      throwError "prvcgen: both sides are expectations. An equation between two programs' \
        probabilities is a program equality, not a triple of one program: `prrw` swaps binds and \
        reduces a shared prefix, the couplings `rvcstep` / `rvcgen` relate the programs, and \
        the `=ᵈ` lemmas relate their distributions. When one side evaluates the other, \
        `simp only [expect_norm, expect_eval]` unfolds it"
    let (lhs, rhs, swap) :=
      if isWpApp lhs then (lhs, rhs, false) else (rhs, lhs, true)
    unless isWpApp lhs do
      throwError "prvcgen: neither side of the equation is an expectation `Pr\{…}[…]`, \
        `𝔼\{…}[…]`, or `wp⟦…⟧ …`"
    if swap then evalTactic (← `(tactic| apply Eq.symm))
    if isNumeral rhs 1 then
      -- the necessary bridge, when its uniform-answer form applies
      let saved ← saveState
      try
        bridgeEqOne
        return .single .necessary
      catch _ =>
        saved.restore
    if isNumeral rhs 0 then
      -- the lower half `0 ≤ …` holds outright
      evalTactic (← `(tactic| (
        rw [← nonpos_iff_eq_zero]
        first
          | rw [OracleComp.Upper.wp_le_iff_triple]
          | rw [OracleComp.Upper.OptionT.wp_le_iff_triple]
          | rw [OracleComp.Upper.ExceptT.wp_le_iff_triple]
        try simp only [OracleComp.Upper.toDual_wp])))
      return .single .upper
    evalTactic (← `(tactic| refine le_antisymm ?_ ?_))
    if isNumeral rhs 1 then
      -- the upper half `wp⟦oa⟧ g ≤ 1` on the range of an event's observation
      let saved ← saveState
      try
        evalTactic (← `(tactic| focus
          refine wp_le_of_forall_le _ ?_
          prvcgen_le_one
          done))
        return .split true
      catch _ =>
        saved.restore
    return .split false
  -- `0 < Pr{…}[p]`
  if goal.isAppOfArity ``LT.lt 4 && isWpApp (goal.getArg! 3) then
    unless isNumeral (goal.getArg! 2) 0 do
      throwError "prvcgen: a strict inequality must be `0 < Pr\{…}[…]`"
    evalTactic (← `(tactic| (
      simp only [OracleComp.Possible.pos_wp_eq_wp, predInd_apply, propInd_pos_iff]
      first
        | rw [OracleComp.Possible.wp_iff_triple]
        | fail "prvcgen: the possible bridge for `0 < …` needs uniform answers \
            (`UniformAnswerMeasure`); otherwise use \
            `OracleComp.Possible.prEvent_pos_iff_triple_of_fullSupport`")))
    return .single .possible
  -- `≤` and `≥`
  let ineq? : Option (Expr × Expr × Bool) :=
    if goal.isAppOfArity ``LE.le 4 then some (goal.getArg! 2, goal.getArg! 3, false)
    else if goal.isAppOfArity ``GE.ge 4 then some (goal.getArg! 3, goal.getArg! 2, true)
    else none
  if let some (lhs, rhs, isGe) := ineq? then
    if isGe then evalTactic (← `(tactic| rw [ge_iff_le]))
    if isWpApp lhs then
      evalTactic (← `(tactic| (
        first
          | rw [OracleComp.Upper.wp_le_iff_triple]
          | rw [OracleComp.Upper.OptionT.wp_le_iff_triple]
          | rw [OracleComp.Upper.ExceptT.wp_le_iff_triple]
        try simp only [OracleComp.Upper.toDual_wp])))
      return .single .upper
    if isWpApp rhs then
      -- the stack bridges first: they state the triple in core's lift of the reading, which
      -- the transformer rules match without unfolding the lifted expectation. The bridges are
      -- applied by `rw`, which keeps the goal's spelling of the specification: `refine` lets
      -- unification unfold a concrete specification, after which no rule matches its queries
      evalTactic (← `(tactic| first
        | rw [OracleComp.Lower.OptionT.le_wp_iff_triple]
        | rw [OracleComp.Lower.ExceptT.le_wp_iff_triple]
        | rw [OracleComp.ProgramLogic.le_wp_iff_triple]
        | rw [ExpectationWP.le_wp_iff_triple]))
      return .single .lower
    throwError "prvcgen: neither side of the inequality is an expectation `Pr\{…}[…]`, \
      `𝔼\{…}[…]`, or `wp⟦…⟧ …`"
  -- `∃ x ∈ support oa, p x`
  if goal.isAppOfArity ``Exists 2 then
    try
      evalTactic (← `(tactic|
        rw [OracleComp.Possible.exists_mem_support_iff_triple]))
      return .single .possible
    catch _ =>
      throwError "prvcgen: an existential must be `∃ x ∈ support oa, p x`"
  -- a weakest precondition of a `Prop` reading, which `vcgen` reads as `⊤ ⊑ wp …`
  if isWpApp goal then
    let w := goal.cleanupAnnotations
    let some reading ← readingOf? (w.getArg! 2) (w.getArg! 6)
      | throwError "prvcgen: a weakest-precondition goal must be of the possible or the \
          necessary reading of an oracle computation"
    return .single reading
  -- `∀ x ∈ support oa, p x`
  if goal.isForall then
    try
      evalTactic (← `(tactic|
        rw [OracleComp.Necessary.forall_mem_support_iff_triple]))
      return .single .necessary
    catch _ =>
      throwError "prvcgen: a universal statement must be `∀ x ∈ support oa, p x`"
  throwError "prvcgen: unsupported goal{indentExpr goal}\n\
    expected `Pr\{…}[…] = c`, `0 < Pr\{…}[…]`, `r ≤ Pr\{…}[…]`, `Pr\{…}[…] ≤ ε` (or the same \
    with `𝔼\{…}[…]` or `wp⟦…⟧ …`), `∀ x ∈ support oa, p x`, `∃ x ∈ support oa, p x`, or a \
    triple `⦃ pre ⦄ oa ⦃ post ⦄`"

/-- Read the verification conditions of the expectation readings back into `ℝ≥0∞`, closing those
that an indicator's range settles. -/
def normalizeVCs : Reading → TacticM Unit
  | .lower => do
    evalTactic (← `(tactic| all_goals simp -failIfUnchanged only [lower_readback]))
  | .upper => do
    evalTactic (← `(tactic| all_goals simp -failIfUnchanged only [upper_readback]))
  | _ => pure ()

end OracleComp.ProgramLogic.PrVCGen

/-- Core `vcgen` on a statement about the outcomes of an oracle computation, under the reading the
statement belongs to: `Pr{…}[p] = 1` and `∀ x ∈ support oa, p x` (necessary), `0 < Pr{…}[p]` and
`∃ x ∈ support oa, p x` (possible), `r ≤ Pr{…}[p]` (expectation lower bound), `Pr{…}[p] ≤ ε` and
`Pr{…}[p] = 0` (expectation upper bound), and `Pr{…}[p] = c` (both bounds, by antisymmetry), with
`𝔼{…}[…]` and `wp⟦…⟧ …` in place of `Pr{…}[…]`; a core triple runs in the reading of its
assertion type. `vcgen`'s arguments — configuration, rules, `until`, `frames`, invariants,
`simplifying_assumptions`, `with` — are passed to it; `prvcgen => tac` runs `tac` in the
reading's scope in place of `vcgen`. See `VCVio.ProgramLogic.Tactics.PrVCGen`. -/
syntax (name := prvcgenStx) "prvcgen" Lean.Parser.Tactic.optConfig
  (" [" withoutPosition((Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),*,?) "] ")?
  (&" until " term)?
  (&" frames " withPosition((colGe Lean.Parser.Tactic.frameAlt)+))?
  (Lean.Parser.Tactic.invariantAlts)?
  (&" simplifying_assumptions" (ppSpace colGt ident)? (" [" ident,* "]")?)?
  (&" with " vcgenDischarge)?
  (" => " tacticSeq)? : tactic

namespace OracleComp.ProgramLogic.PrVCGen

/-- Run `vcgen` with `prvcgen`'s arguments, or the user's tactic, on the main goal inside the
scope of `reading`, then normalize the verification conditions. -/
def runReading (reading : Reading) (stx : Syntax)
    (tac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) : TacticM Unit := focus do
  let tail : TSyntax ``Lean.Parser.Tactic.tacticSeq ← match tac? with
    | some tac => pure tac
    | none =>
      -- `prvcgen` takes `vcgen`'s arguments in `vcgen`'s positions
      let t := mkNode ``Lean.Parser.Tactic.vcgen
        #[mkAtom "vcgen", stx[1], stx[2], stx[3], stx[4], stx[5], stx[6], stx[7]]
      `(tacticSeq| $(⟨t⟩):tactic)
  let scope := mkIdent reading.scope
  evalTactic (← `(tactic|
    open scoped $scope:ident in set_option experimental.vcgen true in ($tail)))
  normalizeVCs reading

@[tactic prvcgenStx, inherit_doc prvcgenStx]
def evalPrvcgen : Tactic := fun stx => focus do
  let tac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) :=
    if stx[8].getNumArgs > 0 then some ⟨stx[8][1]⟩ else none
  if tac?.isSome &&
      (stx[1][0].getNumArgs > 0 || (List.range 6).any fun i => stx[2 + i].getNumArgs > 0) then
    throwError "prvcgen: pass `vcgen`'s arguments to `vcgen` inside the `=>` tactic"
  match ← bridge (← instantiateMVars (← getMainTarget)) with
  | .single reading => runReading reading stx tac?
  | .split upperClosed =>
    let goals ← getGoals
    let readings := if upperClosed then [Reading.lower] else [Reading.upper, Reading.lower]
    let mut remaining := #[]
    for (goal, reading) in goals.zip readings do
      setGoals [goal]
      match ← bridge (← instantiateMVars (← goal.getType)) with
      | .single r =>
        unless r == reading do throwError "prvcgen: unexpected reading for a bound"
        runReading r stx tac?
      | .split _ => throwError "prvcgen: unexpected split of a bound"
      remaining := remaining ++ (← getGoals)
    setGoals remaining.toList

end OracleComp.ProgramLogic.PrVCGen
