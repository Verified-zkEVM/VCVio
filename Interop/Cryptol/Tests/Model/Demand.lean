/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

import Interop.Cryptol.Model.Resolved

/-!
# Demand-sensitive regressions

These examples distinguish outer errors from errors in unselected fields,
including empty dimensions and the versioned reference update rule.
-/

public section

open Interop.Cryptol

example (err : EvalError) :
    (Expr.wordNot (.error err) : ClosedExpr [] (.seq (.finite 0) .bit)).denote
      Environment.empty = .error err := rfl

example (err : EvalError) :
    (Expr.wordToInteger (.error err : ClosedExpr [] (.seq (.finite 0) .bit))).denote
      Environment.empty = .error err := rfl

example (err : EvalError) :
    (Expr.integerToWord 0 (.error err) : ClosedExpr [] (.seq (.finite 0) .bit)).denote
      Environment.empty = .error err := rfl

example : (Expr.wordEq
    (.list [.bit false, .error (.user "unselected")])
    (.list [.bit true, .error (.user "unselected")]) : ClosedExpr [] .bit).start.run 500 =
      .inl (.ok (.bit false)) := rfl

example : (Expr.wordEq
    (.error (.user "left") : ClosedExpr [] (.seq (.finite 0) .bit))
    (.error (.user "right"))).start.run 20 = .inl (.error (.user "left")) := rfl

example : (Expr.index (Expr.wordNot (.list [.bit false, .error (.user "unselected")]))
    (.integer 0) : ClosedExpr [] .bit).start.run 100 = .inl (.ok (.bit true)) := rfl

example : (Expr.force (Expr.wordOp .add
    (.list [.bit false, .error (.user "demanded")]) (Expr.word (0#2)))
    (.integer 17) : ClosedExpr [] .integer).start.run 1000 =
      .inl (.error (.user "demanded")) := rfl

example : (Expr.index
    (Expr.update (.error (.user "source") : ClosedExpr [] (.seq (.finite 2) .bit))
      (.integer 0) (.bit true)) (.integer 0)).start.run 100 =
      .inl (.ok (.bit true)) := rfl

example : (Expr.index (Expr.update (Expr.word (2#2)) (.integer (-1)) (.bit false))
    (.integer 0) : ClosedExpr [] .bit).start.run 200 = .inl (.ok (.bit true)) := rfl

example : (Expr.force
    (Expr.take (.finite 0) (.finite 2)
      (.error (.user "source") : ClosedExpr [] (.seq (.finite 2) .bit)))
    (.integer 17)).start.run 30 = .inl (.ok (.integer 17)) := rfl

-- Elementwise round trips do not preserve an erroneous outer constructor.
example : (Expr.force
    (Expr.join (.finite 2) 2 (Expr.split (.finite 2) 2
      (.error (.user "source") : ClosedExpr [] (.seq (.finite 4) .bit))))
    (.integer 17)).start.run 30 = .inl (.ok (.integer 17)) := rfl


set_option maxRecDepth 4096 in
example : (Expr.wordToInteger (Expr.shift .rotateLeft (Expr.word (9#4))
    (.integer (-1))) : ClosedExpr [] .integer).start.run 3000 =
      .inl (.ok (.integer 12)) := rfl

set_option maxRecDepth 4096 in
example : (Expr.wordToInteger (Expr.shift .left
    (.error (.user "unselected") : ClosedExpr [] (wordTy 4)) (.integer 4))).start.run 2000 =
      .inl (.ok (.integer 0)) := rfl

example : (Expr.force (Expr.shift .rotateRight
    (.error (.user "source") : ClosedExpr [] (wordTy 0)) (.error (.user "amount")))
    (.integer 0)).start.run 100 = .inl (.error (.user "amount")) := rfl

example : (Expr.force (Expr.shift .rotateRight
    (.error (.user "source") : ClosedExpr [] (wordTy 0)) (.integer 0))
    (.integer 0)).start.run 100 = .inl (.error (.user "source")) := rfl

example : (Expr.force (Expr.shift .left
    (.error (.user "source") : ClosedExpr [] (wordTy 0)) (.integer 0))
    (.integer 0)).start.run 100 = .inl (.ok (.integer 0)) := rfl

set_option maxRecDepth 4096 in
example : (Resolved.lower (Resolved.Term.toInteger (Resolved.Term.shiftWord .left
    (.word (3#4)) (.word (1#3))))).start.run 4000 = .inl (.ok (.integer 6)) := rfl

example : (Expr.force (Resolved.lower (Resolved.Term.shiftWord .left
    (.word (0#4)) (.sequence 2 (fun i => if i.val = 0 then .bit false
      else .error (.user "amount bit"))))) (.integer 0)).start.run 500 =
      .inl (.error (.user "amount bit")) := rfl

example : (Expr.wordCompare .lt
    (.list [.bit false, .error (.user "unselected")])
    (.list [.bit true, .error (.user "unselected")]) : ClosedExpr [] .bit).start.run 500 =
      .inl (.ok (.bit true)) := rfl

example : (Expr.wordCompare .le
    (.error (.user "left") : ClosedExpr [] (wordTy 0))
    (.error (.user "right"))).start.run 100 = .inl (.error (.user "left")) := rfl

example : (Expr.indexEnd (.error (.user "source") : ClosedExpr [] (wordTy 2))
    (.error (.user "index"))).start.run 100 = .inl (.error (.user "source")) := rfl

example : (Expr.indexEnd (Expr.word (3#2)) (.integer (-1)) : ClosedExpr [] .bit).start.run 200 =
    .inl (.error (.invalidIndex (-1))) := rfl

example : (Expr.index (Expr.updateEnd
    (.error (.user "source") : ClosedExpr [] (wordTy 2)) (.integer 0) (.bit true))
    (.integer 1)).start.run 200 = .inl (.ok (.bit true)) := rfl

example : (Expr.force (Expr.join .infinite 0
    (.error (.user "source") : ClosedExpr [] (.seq .infinite (wordTy 0))))
    (.integer 17)).start.run 100 = .inl (.ok (.integer 17)) := rfl

example : (Expr.index (Expr.index (Expr.transpose (.finite 2) (.finite 2)
    (.list [.list [.bit true, .error (.user "column")], .error (.user "row")]))
    (.integer 0)) (.integer 0) : ClosedExpr [] .bit).start.run 400 =
      .inl (.ok (.bit true)) := rfl

example : (Expr.index (Expr.reverse (Expr.word (1#4))) (.integer 0) :
    ClosedExpr [] .bit).start.run 100 = .inl (.ok (.bit true)) := rfl

example : (Expr.index (Expr.drop 1 .infinite
    (.append (Expr.list [.bit false]) (.generate Length.infinite (.bit true))))
    (.integer 4) : ClosedExpr [] .bit).start.run 300 = .inl (.ok (.bit true)) := rfl
