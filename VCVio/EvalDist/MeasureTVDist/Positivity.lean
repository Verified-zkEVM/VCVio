/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVio.EvalDist.MeasureTVDist.Basic
public import VCVio.EvalDist.EvalDistTV
public meta import Mathlib.Tactic.Positivity.Core

/-!
# Positivity of total variation distance

The `positivity` extension for `measureTVDist` uses its public nonnegativity theorem. It composes
with arithmetic extensions and does not assert strict positivity or distinguishability.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Meta.Positivity

/-- Total variation distance between output measures is nonnegative. -/
@[positivity measureTVDist _ _]
def evalMeasureTVDist : PositivityExt where
  eval {u α} _ pα? e :=
    match pα? with | none => pure .none | some _ => do
    match u, α, e with
    | 0, ~q(ℝ), ~q(@measureTVDist $m $β $inst $ms $mx $my) =>
        assertInstancesCommute
        return .nonnegative q(@measureTVDist_nonneg $m $β $inst $ms $mx $my)
    | _, _, _ => throwError "not a total variation distance"

/-- The event-keyed total variation distance between computations is nonnegative. -/
@[positivity tvDist _ _]
def evalTVDist : PositivityExt where
  eval {u α} _ pα? e :=
    match pα? with | none => pure .none | some _ => do
    match u, α, e with
    | 0, ~q(ℝ), ~q(@tvDist $m $m' $β $i1 $i2 $i3 $i4 $j1 $j2 $j3 $j4 $mx $my) =>
        assertInstancesCommute
        return .nonnegative q(@tvDist_nonneg $m $m' $β $i1 $i2 $i3 $i4 $j1 $j2 $j3 $j4 $mx $my)
    | _, _, _ => throwError "not a total variation distance"

end Mathlib.Meta.Positivity
