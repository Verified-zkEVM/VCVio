/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.ProgramLogic.Unary.WP.QualitativeSpecs
public import VCVio.ProgramLogic.Unary.WP.QuantitativeSpecs
public import VCVio.ProgramLogic.Unary.WP.Coherence
public import VCVio.ProgramLogic.Unary.WP.Angelic
public import VCVio.ProgramLogic.Unary.WP.Upper
public meta import Lean.Elab.Tactic.Basic
public meta import Std.Tactic.Do

/-!
# `prvcgen`: core `vcgen` on events, under the matching reading

A statement about the outcomes of an oracle computation is a core triple under one of four
readings of `OracleComp spec`. `prvcgen` classifies the goal, states it as a triple of that reading
with its bridge lemma, and runs core's `vcgen` inside the reading's per-call scope:

| Goal | Reading | Triple |
|------|---------|--------|
| `Pr{…}[p] = 1`, `∀ x ∈ support oa, p x` | structural | `⦃ True ⦄ oa ⦃ p ⦄` |
| `0 < Pr{…}[p]`, `∃ x ∈ support oa, p x` | angelic | `⦃ True ⦄ oa ⦃ p ⦄` |
| `r ≤ Pr{…}[p]` | expectation (global) | `⦃ r ⦄ oa ⦃ predInd p ⦄` |
| `Pr{…}[p] ≤ ε`, `Pr{…}[p] = 0` | upper bound | `⦃ toDual ε ⦄ oa ⦃ … ⦄` |
| `Pr{…}[p] = c` | upper bound and expectation | both of the above |
| `⦃ pre ⦄ oa ⦃ post ⦄` | read off the assertion type | the goal itself |

The readings are `OracleComp.Qualitative`, `OracleComp.Angelic`, the global expectation reading,
and `OracleComp.Upper`. `𝔼{…}[g]` and `wp⟦oa⟧ g` stand wherever `Pr{…}[p]` does, `≥` is read as
`≤` with its sides swapped, and an equation may have the expectation on either side. A triple
already stated is run in the reading of its assertion type: `ℝ≥0∞` for lower bounds, `ℝ≥0∞ᵒᵈ`
for upper bounds, and `Prop` for the structural reading, or the angelic one when the triple's
interpretation is angelic; a state-passing assertion `σ → …` is read by its codomain, so triples
of handlers over `StateT` are run the same way.

The event forms nest one expectation per draw; the bridges rewrite each nested expectation into
the reading, so `vcgen` steps through the whole program. The structural and angelic bridges of an
event need answers of positive mass; `prvcgen` uses their uniform-answer forms
(`IsUniformMeasureSpec`). A goal that is already a weakest precondition of the angelic or the
structural reading, such as the `∃ u, wp (rest u) post ⊥` an angelic draw leaves once its witness
is named, is continued in its reading.

## Equations

An equation `Pr{…}[p] = c`, with `c` not an expectation, splits by `le_antisymm` into the upper
bound `Pr{…}[p] ≤ c` and the lower bound `c ≤ Pr{…}[p]`, each run in its reading. Two values have
a simpler route:

* `= 0` is the upper bound alone, the lower bound `0 ≤ …` holding outright;
* `= 1` is the structural triple when uniform answers are available, whose verification
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

`prvcgen (config) [rules] invariants … with step` passes its configuration, rules, invariant
alternatives and `with` step to `vcgen`; `prvcgen (errorOnMissingSpec := false)` leaves a program
without a rule, such as an opaque sub-program, as a verification condition stating its weakest
precondition. The goal's metavariables are substituted first, since `vcgen` matches programs
syntactically. On an equation both halves receive the invariants and the `with` step, and each keeps
the rules whose triples are stated in its reading, read off the assertion type of the rule's
conclusion; definitions to unfold go to both. An invariant shared by the two halves is written
without a carrier ascription, as `fun _ suff c => ↑c + ↑suff.length`, so that each half elaborates
it in its own carrier. `prvcgen => tac` runs `tac` in place of `vcgen`, on each half of an equation.

The verification conditions of the expectation readings are read back into `ℝ≥0∞`
(`Lean.Order.rel_eq_le`; `OracleComp.Upper.rel_iff`, `ofDual_toDual`,
`OracleComp.Upper.ofDual_wp`, and Mathlib's `ofDual_add`, …), and those an indicator's range
settles or that are reflexive are closed (`propInd_le_one`, `one_le_propInd_iff`, `le_refl`).

A comparison `Pr{A}[p] ≤ Pr{B}[q]` of two events has an expectation on both sides; `prvcgen`
reads it as an upper bound on the left-hand side, with the right-hand side as the bound.

The per-call scopes (`OracleComp.Qualitative.Dispatch`, `OracleComp.Angelic.Dispatch`,
`OracleComp.Quantitative.Dispatch`, `OracleComp.Upper.Dispatch`) register each reading above every
reading a file opens, so `prvcgen` is unaffected by the file's `open scoped` readings.
-/

public meta section

open Lean Elab Tactic Meta

/-- Discharge `∀ a, g a ≤ 1` for an observation built from indicators and nested expectations of
indicators, the side condition of the structural bridge on an event's normal form. -/
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
  /-- All possible outputs: `OracleComp.Qualitative`. -/
  | necessary
  /-- Some possible output: `OracleComp.Angelic`. -/
  | possible
  /-- Expectation lower bounds: the global reading. -/
  | lower
  /-- Expectation upper bounds: `OracleComp.Upper`. -/
  | upper
  deriving BEq

/-- The per-call scope of a reading. -/
def Reading.scope : Reading → Name
  | .necessary => `OracleComp.Qualitative.Dispatch
  | .possible => `OracleComp.Angelic.Dispatch
  | .lower => `OracleComp.Quantitative.Dispatch
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

/-- The reading of a core triple, read off its assertion type: `ℝ≥0∞ᵒᵈ` for the upper-bound
reading, `ℝ≥0∞` for the lower-bound reading, and `Prop` for the structural reading, or the angelic
one when the triple's interpretation is angelic. A state-passing assertion `σ → …` is read by its
codomain. -/
def tripleReading? (goal : Expr) : Option Reading :=
  if !goal.isAppOfArity ``Std.WP.Triple 11 then none else
  let carrier := (goal.getArg! 0).getForallBody
  if carrier.isAppOf ``OrderDual then some .upper
  else if carrier.isConstOf ``ENNReal then some .lower
  else if carrier.isProp then
    let angelic := (goal.getArg! 7).find? fun
      | .const n _ => (`OracleComp.Angelic).isPrefixOf n || n == ``MonadAttach.toWPMonadAngelic
      | _ => false
    some (if angelic.isSome then .possible else .necessary)
  else none

/-- State the structural bridge for `wp⟦oa⟧ g = 1`, rewriting each nested expectation. -/
def bridgeEqOne : TacticM Unit := do
  evalTactic (← `(tactic| (
    simp (disch := prvcgen_le_one) only
      [OracleComp.Qualitative.wp_eq_one_eq_wp, predInd_apply, propInd_eq_one_iff]
    refine (OracleComp.Qualitative.wp_iff_triple _ _).2 ?_)))

/-- State the main goal as a triple of the reading it belongs to, or split an equation. -/
partial def bridge (goal : Expr) : TacticM Plan := do
  let goal := goal.cleanupAnnotations
  -- a core triple, run in the reading of its assertion type
  if goal.isAppOf ``Std.WP.Triple then
    let some reading := tripleReading? goal
      | throwError "prvcgen: a triple must have assertions in `Prop`, `ℝ≥0∞` or `ℝ≥0∞ᵒᵈ`, \
          or in functions into them{indentExpr goal}"
    return .single reading
  -- `pre ⊑ wp oa post epost`, the unfolded form of a triple
  if goal.isAppOfArity ``Lean.Order.PartialOrder.rel 4 && isWpApp (goal.getArg! 3) then
    evalTactic (← `(tactic| refine Std.WP.Triple.iff.1 ?_))
    return ← bridge (← instantiateMVars (← getMainTarget))
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
      -- the structural bridge, when its uniform-answer form applies
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
        refine (OracleComp.Upper.wp_le_iff_triple _ _ _).2 ?_
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
      simp only [OracleComp.Angelic.pos_wp_eq_wp, predInd_apply, propInd_pos_iff]
      first
        | refine (OracleComp.Angelic.wp_iff_triple _ _).2 ?_
        | fail "prvcgen: the angelic bridge for `0 < …` needs uniform answers \
            (`IsUniformMeasureSpec`); otherwise use \
            `OracleComp.Angelic.prEvent_pos_iff_triple_of_fullSupport`")))
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
        refine (OracleComp.Upper.wp_le_iff_triple _ _ _).2 ?_
        try simp only [OracleComp.Upper.toDual_wp])))
      return .single .upper
    if isWpApp rhs then
      evalTactic (← `(tactic| refine (OracleComp.ProgramLogic.le_wp_iff_triple _ _ _).2 ?_))
      return .single .lower
    throwError "prvcgen: neither side of the inequality is an expectation `Pr\{…}[…]`, \
      `𝔼\{…}[…]`, or `wp⟦…⟧ …`"
  -- `∃ x ∈ support oa, p x`
  if goal.isAppOfArity ``Exists 2 then
    try
      evalTactic (← `(tactic|
        refine (OracleComp.Angelic.exists_mem_support_iff_triple _ _).2 ?_))
      return .single .possible
    catch _ =>
      throwError "prvcgen: an existential must be `∃ x ∈ support oa, p x`"
  -- a weakest precondition of the angelic or the structural reading
  if isWpApp goal then
    try
      evalTactic (← `(tactic| refine (OracleComp.Angelic.wp_iff_triple _ _).2 ?_))
      return .single .possible
    catch _ =>
    try
      evalTactic (← `(tactic| refine (OracleComp.Qualitative.wp_iff_triple _ _).2 ?_))
      return .single .necessary
    catch _ =>
      throwError "prvcgen: a weakest-precondition goal must be of the angelic or the \
        structural reading of an oracle computation"
  -- `∀ x ∈ support oa, p x`
  if goal.isForall then
    try
      evalTactic (← `(tactic|
        refine (OracleComp.Qualitative.forall_mem_support_iff_triple _ _).2 ?_))
      return .single .necessary
    catch _ =>
      throwError "prvcgen: a universal statement must be `∀ x ∈ support oa, p x`"
  throwError "prvcgen: unsupported goal{indentExpr goal}\n\
    expected `Pr\{…}[…] = c`, `0 < Pr\{…}[…]`, `r ≤ Pr\{…}[…]`, `Pr\{…}[…] ≤ ε` (or the same \
    with `𝔼\{…}[…]` or `wp⟦…⟧ …`), `∀ x ∈ support oa, p x`, `∃ x ∈ support oa, p x`, or a \
    triple `⦃ pre ⦄ oa ⦃ post ⦄`"

/-- The reading a rule is stated in, read off the assertion type of the triple it concludes:
`ℝ≥0∞ᵒᵈ` for the upper-bound reading, `ℝ≥0∞` for the lower-bound reading, `Prop` for the
structural and angelic readings, and `none` for a rule that is not a triple (a definition to
unfold, an equation). -/
def ruleCarrier? (rule : Syntax) : TacticM (Option Name) := withMainContext do
  unless rule.getKind == ``Lean.Parser.Tactic.simpLemma do return none
  let saved ← saveState
  try
    let e ← Term.withoutErrToSorry <| Term.elabTerm rule[2] none
    let ty ← instantiateMVars (← inferType e)
    let res ← forallTelescopeReducing ty fun _ body => do
      let body := body.cleanupAnnotations
      unless body.isAppOf ``Std.WP.Triple do return none
      let mut pred := body.getArg! 0
      while pred.isForall do pred := pred.bindingBody!
      if pred.isAppOf ``OrderDual then return some ``OrderDual
      if pred.isConstOf ``ENNReal then return some ``ENNReal
      if pred.isProp then return some `Prop
      return none
    saved.restore
    return res
  catch _ =>
    saved.restore
    return none

/-- Whether a rule stated in `carrier` applies to the triples of `reading`. -/
def Reading.accepts (reading : Reading) : Option Name → Bool
  | none => true
  | some c => match reading with
    | .upper => c == ``OrderDual
    | .lower => c == ``ENNReal
    | .necessary | .possible => c == `Prop

/-- Read the verification conditions of the expectation readings back into `ℝ≥0∞`, closing those
that an indicator's range settles. -/
def normalizeVCs : Reading → TacticM Unit
  | .lower => do
    evalTactic (← `(tactic| all_goals simp -failIfUnchanged only [Lean.Order.rel_eq_le,
      binderNameHint, predInd_apply, one_le_propInd_iff, le_refl]))
  | .upper => do
    evalTactic (← `(tactic| all_goals simp -failIfUnchanged only [OracleComp.Upper.rel_iff,
      OracleComp.Upper.le_iff_ofDual, OrderDual.ofDual_toDual, OracleComp.Upper.ofDual_wp,
      binderNameHint, predInd_apply, propInd_le_one, ofDual_add, ofDual_mul, ofDual_div,
      ofDual_inv, ofDual_zero, ofDual_one, ofDual_natCast, ofDual_ofNat, le_refl]))
  | _ => pure ()

end OracleComp.ProgramLogic.PrVCGen

/-- Core `vcgen` on a statement about the outcomes of an oracle computation, under the reading the
statement belongs to: `Pr{…}[p] = 1` and `∀ x ∈ support oa, p x` (structural), `0 < Pr{…}[p]` and
`∃ x ∈ support oa, p x` (angelic), `r ≤ Pr{…}[p]` (expectation lower bound), `Pr{…}[p] ≤ ε` and
`Pr{…}[p] = 0` (expectation upper bound), and `Pr{…}[p] = c` (both bounds, by antisymmetry), with
`𝔼{…}[…]` and `wp⟦…⟧ …` in place of `Pr{…}[…]`; a core triple runs in the reading of its
assertion type. The configuration, rules, invariants and `with` step are passed to `vcgen`;
`prvcgen => tac` runs `tac` in the reading's scope in place of `vcgen`. See
`VCVio.ProgramLogic.Tactics.PrVCGen`. -/
syntax (name := prvcgenStx) "prvcgen" Lean.Parser.Tactic.optConfig
  (" [" withoutPosition((Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),*,?) "] ")?
  (Lean.Parser.Tactic.invariantAlts)?
  (&" with " vcgenDischarge)?
  (" => " tacticSeq)? : tactic

namespace OracleComp.ProgramLogic.PrVCGen

/-- Run `vcgen`, or the user's tactic, on the main goal inside the scope of `reading`, then
normalize the verification conditions. `filter` keeps only the rules stated in the reading. -/
def runReading (reading : Reading) (config : Syntax) (rules : Array Syntax)
    (invs? : Option (TSyntax ``Lean.Parser.Tactic.invariantAlts))
    (with? : Option (TSyntax `vcgenDischarge))
    (tac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) (filter : Bool) :
    TacticM Unit := focus do
  -- `vcgen` matches programs syntactically, so assigned metavariables must be substituted
  let g ← getMainGoal
  replaceMainGoal [← g.replaceTargetDefEq (← instantiateMVars (← g.getType))]
  let tail : TSyntax ``Lean.Parser.Tactic.tacticSeq ← match tac? with
    | some tac => pure tac
    | none => do
      let rules ← if filter then rules.filterM fun r => return reading.accepts (← ruleCarrier? r)
        else pure rules
      -- `vcgen`'s arguments by position: configuration at 1, `[rules]` at 2, `invariants` at 5,
      -- `with` at 7
      let base ← `(tactic| vcgen)
      unless base.raw.getKind == ``Lean.Parser.Tactic.vcgen && base.raw.getNumArgs == 8 do
        throwError "prvcgen: unexpected shape of `vcgen` syntax"
      let mut t := base.raw.setArg 1 config
      unless rules.isEmpty do
        t := t.setArg 2 (mkNullNode #[mkAtom "[", Syntax.mkSep rules (mkAtom ","), mkAtom "]"])
      if let some invs := invs? then t := t.setArg 5 (mkNullNode #[invs])
      if let some w := with? then t := t.setArg 7 (mkNullNode #[mkAtom "with", w])
      `(tacticSeq| $(⟨t⟩):tactic)
  let scope := mkIdent reading.scope
  evalTactic (← `(tactic|
    open scoped $scope:ident in set_option experimental.vcgen true in ($tail)))
  normalizeVCs reading

@[tactic prvcgenStx, inherit_doc prvcgenStx]
def evalPrvcgen : Tactic := fun stx => focus do
  let config := stx[1]
  let rules := if stx[2].getNumArgs > 0 then stx[2][1].getSepArgs else #[]
  let invs? : Option (TSyntax ``Lean.Parser.Tactic.invariantAlts) :=
    if stx[3].getNumArgs > 0 then some ⟨stx[3][0]⟩ else none
  let with? : Option (TSyntax `vcgenDischarge) :=
    if stx[4].getNumArgs > 0 then some ⟨stx[4][1]⟩ else none
  let tac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) :=
    if stx[5].getNumArgs > 0 then some ⟨stx[5][1]⟩ else none
  if tac?.isSome &&
      (config[0].getNumArgs > 0 || !rules.isEmpty || invs?.isSome || with?.isSome) then
    throwError "prvcgen: pass the configuration, rules, invariants and `with` to `vcgen` inside \
      the `=>` tactic"
  match ← bridge (← instantiateMVars (← getMainTarget)) with
  | .single reading => runReading reading config rules invs? with? tac? false
  | .split upperClosed =>
    let goals ← getGoals
    let readings := if upperClosed then [Reading.lower] else [Reading.upper, Reading.lower]
    let mut remaining := #[]
    for (goal, reading) in goals.zip readings do
      setGoals [goal]
      match ← bridge (← instantiateMVars (← goal.getType)) with
      | .single r =>
        unless r == reading do throwError "prvcgen: unexpected reading for a bound"
        runReading r config rules invs? with? tac? true
      | .split _ => throwError "prvcgen: unexpected split of a bound"
      remaining := remaining ++ (← getGoals)
    setGoals remaining.toList

end OracleComp.ProgramLogic.PrVCGen
