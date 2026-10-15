/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Interop.Cryptol.Model.Examples
import Interop.Cryptol.Model.Comprehensions

/-! # Sequential and parallel generator demand and binding regressions -/

open Interop.Cryptol

example : (Resolved.lower (Resolved.Term.index Examples.dependentRows (.integer 1))).start.run
      2000 =
    .inl (.ok (.integer 10)) := rfl

example : (Resolved.lower (Resolved.Term.index Examples.dependentRows (.integer 2))).start.run
      2000 =
    .inl (.ok (.integer 2)) := rfl

example : (Resolved.lower (Resolved.Term.index Examples.parallelRows (.integer 1))).start.run
      1000 =
    .inl (.ok (.integer 12)) := rfl

example : (Resolved.lower (Resolved.Term.index Examples.parallelRows (.integer 2))).start.run
      1000 =
    .inl (.error (.invalidIndex 2)) := rfl

example : (Resolved.lower (Resolved.Term.index Examples.ignoredParallel (.integer 1))).start.run
      1000 =
    .inl (.ok (.integer 23)) := rfl

/-- An empty inner generator produces an outer value despite erroneous sources. -/
example : (Expr.force (Resolved.lower (Resolved.Term.flatMap (l := .infinite)
    (a := .integer) (b := .integer) 0 (.error (.user "function"))
      (.error (.user "sequence")))) (.integer 17)).start.run 100 =
    .inl (.ok (.integer 17)) := rfl

/-- An infinite inner row keeps observing the first outer element. -/
example : (Expr.index (Expr.flatMap (a := .integer) (b := .integer) (outer := .infinite) .infinite
    (.lam (.generate Length.infinite (.var (.succ .zero))))
    (.generate Length.infinite (.var .zero))) (.integer 1000)).start.run 100 =
      .inl (.ok (.integer 0)) := rfl

/-- A zero outer dimension suppresses an infinite inner row and its errors. -/
example : (Expr.force (Expr.flatMap (a := .integer) (b := .integer) (outer := .finite 0)
    .infinite (.error (.user "function")) (.error (.user "sequence")))
      (.integer 17)).start.run 100 = .inl (.ok (.integer 17)) := rfl

/-- Parallel branch construction does not demand the unused branch. -/
example : (Expr.fst (Expr.index (Expr.zip
    (.generate (.finite 2) (.integer 23))
    (.error (.user "unused") : Expr [] (.seq (.finite 3) .bit)))
      (.integer 1))).start.run 100 = .inl (.ok (.integer 23)) := rfl
