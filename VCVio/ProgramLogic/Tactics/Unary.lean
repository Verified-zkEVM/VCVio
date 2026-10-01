/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public meta import VCVio.ProgramLogic.Tactics.Unary.Internals.ProbEq
public import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Unary probability tactics

`prrw` proves equalities between the events, expectations or output measures of two programs that
differ by the order of independent draws or agree after a shared prefix, the program equalities of
a game hop. `expect_arith` normalizes expectation and indicator arithmetic, and `by_hoare` states a
probability goal as an expectation.

Statements about the outcomes of one program (bounds, probability one, possibility) are core
triples, proved by `prvcgen` (`VCVio.ProgramLogic.Tactics.PrVCGen`); `rvcgen` relates two programs
by a coupling.
-/

public meta section

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic

private def binderIdentsToNames (ids : Syntax.TSepArray `Lean.binderIdent ",") : Array Name :=
  ids.getElems.map fun
    | `(binderIdent| $name:ident) => name.getId
    | _ => Name.anonymous

/-- `prrw` rewrites an equality between the probabilities of two programs, `Pr{…}[…] = Pr{…}[…]`,
`𝔼{…}[…] = 𝔼{…}[…]` or `𝒟[oa] = 𝒟[ob]`, by one program-equality step:

- `prrw` swaps two adjacent independent binds at the top of one side (`OracleComp.wp_swap`,
  `OracleComp.evalDist_bind_bind_swap`, or their uniform-answer forms);
- `prrw under n` swaps two adjacent binds under `n` shared bind prefixes;
- `prrw move i j` moves the draw at depth `i` of the left-hand side to depth `j` by adjacent
  swaps of independent draws, sinking it when `i < j` and lifting it when `j < i` (`symm` first
  to move a draw of the right-hand side);
- `prrw congr` reduces a shared first bind to its continuations on the support of the shared
  program (`wp_congr_of_support`, `OracleComp.evalDist_bind_congr_of_support`), introducing the
  bound value and its support hypothesis;
- `prrw congr'` reduces a shared first bind for every value, without a support hypothesis;
- `prrw normalize` searches bounded sequences of swaps and congruence steps, sized by the bind
  depth of the goal, for one that closes the equality.

`as ⟨x, …⟩` names the values a step introduces; `prrw congr as ⟨x, hx, y, hy⟩` reduces one shared
bind per name pair. Both sides are first brought into the normal form of `Pr{…}[…]` and `𝔼{…}[…]`
(`expect_norm`), or into plain bind chains for output measures. -/
syntax (name := prrw) "prrw" : tactic
@[inherit_doc prrw, tactic_alt prrw]
syntax "prrw" " under " num : tactic
@[inherit_doc prrw, tactic_alt prrw]
syntax (name := prrwMove) "prrw" &"move" num num : tactic
@[inherit_doc prrw, tactic_alt prrw]
syntax "prrw" &"normalize" : tactic
@[inherit_doc prrw, tactic_alt prrw]
syntax "prrw" &"congr" : tactic
@[inherit_doc prrw, tactic_alt prrw]
syntax "prrw" &"congr'" : tactic
@[inherit_doc prrw, tactic_alt prrw]
syntax "prrw" "as" "⟨" binderIdent,* "⟩" : tactic
@[inherit_doc prrw, tactic_alt prrw]
syntax "prrw" " under " num "as" "⟨" binderIdent,* "⟩" : tactic
@[inherit_doc prrw, tactic_alt prrw]
syntax "prrw" &"congr" "as" "⟨" binderIdent,* "⟩" : tactic
@[inherit_doc prrw, tactic_alt prrw]
syntax "prrw" &"congr'" "as" "⟨" binderIdent,* "⟩" : tactic

elab_rules : tactic
  | `(tactic| prrw as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runProbEqAction .rewrite then
        introAllGoalsNames names
        renameInaccessibleNames names
        return
      TacticInternals.Unary.throwPrrwError 0
  | `(tactic| prrw under $n:num as ⟨ $ids,* ⟩) => do
      let depth := n.getNat
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runProbEqAction (.rewriteUnder depth) then
        introAllGoalsNames names
        renameInaccessibleNames names
        return
      TacticInternals.Unary.throwPrrwError depth
  | `(tactic| prrw congr as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runProbEqCongrChainWithNames true names then return
      TacticInternals.Unary.throwPrrwCongrError true
  | `(tactic| prrw congr' as ⟨ $ids,* ⟩) => do
      let names := binderIdentsToNames ids
      if ← TacticInternals.Unary.runProbEqCongrChainWithNames false names then return
      TacticInternals.Unary.throwPrrwCongrError false
  | `(tactic| prrw) => do
      if ← TacticInternals.Unary.runProbEqAction .rewrite then return
      TacticInternals.Unary.throwPrrwError 0
  | `(tactic| prrw under $n:num) => do
      let depth := n.getNat
      if ← TacticInternals.Unary.runProbEqAction (.rewriteUnder depth) then return
      TacticInternals.Unary.throwPrrwError depth
  | `(tactic| prrw move $i:num $j:num) => do
      let i := i.getNat
      let j := j.getNat
      if ← TacticInternals.Unary.runProbEqMove i j then return
      TacticInternals.Unary.throwPrrwMoveError i j
  | `(tactic| prrw normalize) => do
      if ← TacticInternals.Unary.runProbEqNormalize then return
      TacticInternals.Unary.throwPrrwNormalizeError
  | `(tactic| prrw congr) => do
      if ← TacticInternals.Unary.runProbEqAction .congr then return
      TacticInternals.Unary.throwPrrwCongrError true
  | `(tactic| prrw congr') => do
      if ← TacticInternals.Unary.runProbEqAction .congrNoSupport then return
      TacticInternals.Unary.throwPrrwCongrError false

/-- `expect_arith` normalizes expectation / indicator arithmetic in the current goal: the
normal form (`expect_norm`), the evaluation of loops, queries and uniform draws (`expect_eval`),
linearity of expectation (`expect_arith`), and the algebra of indicators (`propInd_true`,
`propInd_false`, `propInd_and`, …). -/
macro (name := expectArith) "expect_arith" : tactic =>
  `(tactic| simp only [
    propInd_true, propInd_false,
    propInd_and, propInd_eq_ite,
    propInd_not, propInd_le_one,
    propInd,
    ExpectationWP.wp_const_of_oracle, OracleComp.ProgramLogic.wp_eq_tsum,
    ite_true, ite_false, ite_true, ite_false, dite_true, dite_false,
    one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero,
    expect_norm, expect_eval, expect_arith])

/-- `by_hoare` transforms a probability goal into a quantitative WP goal. -/
macro (name := byHoare) "by_hoare" : tactic =>
  `(tactic|
    simp only [prEvent_ite, prEvent_dite, evalDist_ite_apply, evalDist_dite_apply,
      OracleComp.ProgramLogic.prEvent_eq_wp_propInd,
      ← propInd_eq_ite])

end OracleComp.ProgramLogic
