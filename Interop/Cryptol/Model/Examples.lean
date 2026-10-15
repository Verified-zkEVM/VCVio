/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.ResolvedSequences
public import Interop.Cryptol.Model.Records
public import Interop.Cryptol.Model.Comprehensions
public import Interop.Cryptol.Model.Operational

/-!
# Executable Cryptol model examples

Programs are finite descriptions even when they denote infinite streams.
The fixtures include suspended failures, recursive streams, higher-order
application, mutual recursion, and concrete word operations. They are shared
by Lean regressions and the external evaluator comparison.
-/

public section

namespace Interop.Cryptol.Examples

/-- A productive recursive stream: each demand reduces the index. -/
@[expose] def naturals : ClosedExpr [] (.seq .infinite .integer) :=
  .fix (.generate Length.infinite (.ite (.intEq (.var .zero) (.integer 0)) (.integer 0)
    (.intOp .add (.integer 1)
      (.index (.var (.succ .zero)) (.intOp .sub (.var .zero) (.integer 1))))))

/-- Mutually recursive even and odd streams, represented by a lazy product. -/
@[expose] def evenOdd : ClosedExpr []
    (.prod (.seq .infinite .integer) (.seq .infinite .integer)) :=
  .fix (.pair
    (.generate Length.infinite (.ite (.intEq (.var .zero) (.integer 0)) (.integer 0)
      (.intOp .add (.integer 1) (.index (.snd (.var (.succ .zero)))
        (.intOp .sub (.var .zero) (.integer 1))))))
    (.generate Length.infinite (.intOp .add (.integer 1)
      (.index (.fst (.var (.succ .zero))) (.var .zero)))))

/-- A recursively defined higher-order function. -/
@[expose] def factorial : ClosedExpr [] (.arrow .integer .integer) :=
  .fix (.lam (.ite (.intLt (.var .zero) (.integer 2)) (.integer 1)
    (.intOp .mul (.var .zero) (.app (.var (.succ .zero))
      (.intOp .sub (.var .zero) (.integer 1))))))

/-- Both numeric and value-type parameters survive in a polymorphic map. -/
@[expose] def mapSchema : Schema where
  numericArity := 1
  typeArity := 2
  constraints := []
  body := .arrow (.arrow (.var 0) (.var 1))
    (.arrow (.seq (.var 0) (.var 0)) (.seq (.var 0) (.var 1)))

/-- A schema body with explicit type abstraction, prior to instantiation. -/
@[expose] def polymorphicMap : Definition mapSchema where
  body := .lam (.lam (.generate (NumExpr.var (0 : Fin 1)) (.app (.var (.succ (.succ .zero)))
    (.index (.var (.succ .zero)) (.var .zero)))))

/-- Instantiate polymorphic map at an infinite integer stream. -/
@[expose] def mapArguments : mapSchema.Instantiation where
  numbers _ := .infinite
  types _ := .integer
  valid _ h := nomatch h

/-- Add one to each element through the instantiated polymorphic definition. -/
@[expose] def incremented : ClosedExpr [] (.seq .infinite .integer) :=
  .app (.app (polymorphicMap.instantiate mapArguments)
    (.lam (.intOp .add (.var .zero) (.integer 1)))) naturals

/-- A second generator depends on the first; the body retains both bindings. -/
@[expose] def dependentRows : Resolved.Term [] (.seq (.finite 4) .integer) :=
  .flatMap 2 (.lam (.map
    (.lam (.intOp .add (.var (.succ .zero)) (.var .zero)))
    (.sequence 2 (fun i => if i.val = 0 then .var .zero
      else .intOp .add (.var .zero) (.integer 10))))) (.range 0 2)

/-- Parallel generators stop before the unused erroneous tail. -/
@[expose] def parallelRows : Resolved.Term [] (.seq (.finite 2) .integer) :=
  .zipWith (.lam (.lam (.intOp .add (.var (.succ .zero)) (.var .zero))))
    (.range 0 2) (.sequence 3 (fun i => if i.val = 2 then .error (.user "tail")
      else .integer (10 + (i.val : Int))))

/-- An ignored parallel generator may have an erroneous outer constructor. -/
@[expose] def ignoredParallel : Resolved.Term [] (.seq (.finite 2) .integer) :=
  Resolved.Term.zipWith (l := .finite 2) (m := .infinite)
    (a := .integer) (b := .integer) (.lam (.lam (.integer 23)))
    (.error (.user "left")) (.error (.user "right"))

/-- A named scalar observation and its expected outcome. -/
structure Fixture where
  /-- Identifier used by the fixture CLI. -/
  name : String
  /-- A closed integer observation. -/
  source : Resolved.Term [] .integer
  /-- Expected terminating value or error. `none` means an intentional fuel cutoff. -/
  expected : Option (Except EvalError Int)
  /-- Per-fixture execution budget. -/
  fuel : Nat := 5000

/-- The machine executes the verified lowering of the fixture's source. -/
@[expose] def Fixture.term (fixture : Fixture) : ClosedExpr [] .integer :=
  Resolved.lower fixture.source

/-- A fixture from core syntax whose source representation is statically checked. -/
@[expose] def Fixture.core (name : String) (term : ClosedExpr [] .integer)
    (expected : Option (Except EvalError Int)) (fuel : Nat)
    (supported : (Resolved.ofCore? term).toOption.isSome = true) : Fixture :=
  ⟨name, Resolved.ofCore term supported, expected, fuel⟩

/-- Observe only the integer result, retaining a cutoff as a distinct result. -/
@[expose] def runInteger (fuel : Nat) (e : ClosedExpr [] .integer) :
    Option (Except EvalError Int) :=
  match e.start.run fuel with
  | .inr _ => none
  | .inl (.error err) => some (.error err)
  | .inl (.ok (.integer i)) => some (.ok i)

/-- The regression corpus shared with the Cryptol executable tests. -/
@[expose] def fixtures : List Fixture := [
  ⟨"structural_function_demand_order", .ite (.app
      (.app (.app (.primitive (.logic (.arrow .integer .bit) .xor))
        (.lam (.error (.user "left-result")))) (.error (.user "right-function"))) (.integer 0))
      (.integer 1) (.integer 0),
      some (.error (.user "right-function")), 200⟩,
  ⟨"structural_logic_tuple", .ite (.fst
      (.app (.app (.primitive (.logic (.prod .bit .bit) .xor))
        (.pair (.bit true) (.error (.user "unused-left"))))
        (.pair (.bit false) (.error (.user "unused-right")))))
      (.integer 1) (.integer 0), some (.ok 1), 200⟩,
  ⟨"structural_ring_function", .app
      (.app (.app (.primitive (.ring (.arrow .integer .integer) .add))
        (.lam (.integer 7))) (.lam (.integer 3))) (.error (.user "unused")),
      some (.ok 10), 200⟩,
  ⟨"structural_ring_empty_error", .index
      (.app (.app (.primitive (.ring (.seq (.finite 0) .integer) .add))
        (.error (.user "outer"))) (.sequence 0 Fin.elim0)) (.integer 0),
      some (.error (.user "outer")), 200⟩,
  Fixture.core "record_update_bypasses_error"
    (.ite (Record.select (.succ .zero) (Record.update (.succ .zero)
      (.error (.user "original") : ClosedExpr [] (Record.type [.integer, .bit])) (.bit true)))
      (.integer 1) (.integer 0)) (some (.ok 1)) 100 (by rfl),
  Fixture.core "sequential_infinite_inner"
    (.index (Expr.flatMap (a := .integer) (b := .integer) (outer := .infinite) .infinite
      (.lam (.generate Length.infinite (.var (.succ .zero))))
      (.generate Length.infinite (.var .zero))) (.integer 1000)) (some (.ok 0)) 100 (by rfl),
  ⟨"sequential_generator_first_row", .index dependentRows (.integer 1), some (.ok 10), 2000⟩,
  ⟨"sequential_generator_second_row", .index dependentRows (.integer 2), some (.ok 2), 2000⟩,
  ⟨"parallel_generator_prefix", .index parallelRows (.integer 1), some (.ok 12), 1000⟩,
  ⟨"parallel_generator_bounds", .index parallelRows (.integer 2),
    some (.error (.invalidIndex 2)), 1000⟩,
  ⟨"parallel_generator_ignored", .index ignoredParallel (.integer 1), some (.ok 23), 1000⟩,
  Fixture.core "lazy_argument" (.app (.lam (.integer 7)) (.diverge (a := .integer)))
    (some (.ok 7)) 50 (by rfl),
  Fixture.core "lazy_error_argument"
    (.app (.lam (.integer 7)) (.error (a := .bit) (.user "unused")))
    (some (.ok 7)) 50 (by rfl),
  Fixture.core "lazy_tuple" (.fst (.pair (.integer 9) (.diverge (a := .integer))))
    (some (.ok 9)) 50 (by rfl),
  Fixture.core "lazy_branch" (.ite (.bit true) (.integer 11) .diverge) (some (.ok 11)) 50 (by rfl),
  Fixture.core "lazy_sequence" (.index (.list [.integer 3, .diverge]) (.integer 0))
    (some (.ok 3)) 50 (by rfl),
  Fixture.core "productive_stream" (.index naturals (.integer 8)) (some (.ok 8)) 1000 (by rfl),
  Fixture.core "mutual_recursion" (.index (.snd evenOdd) (.integer 4)) (some (.ok 9)) 2000 (by rfl),
  Fixture.core "polymorphic_stream" (.index incremented (.integer 6)) (some (.ok 7)) 2000 (by rfl),
  Fixture.core "factorial" (.app factorial (.integer 6)) (some (.ok 720)) 2000 (by rfl),
  Fixture.core "higher_order" (.app (.lam (.app (.var .zero) (.integer 3)))
    (.lam (.intOp .mul (.var .zero) (.integer 4)))) (some (.ok 12)) 100 (by rfl),
  Fixture.core "empty_sequence" (.app (.lam (.integer 17)) (.generate (.finite 0)
    (.diverge (a := .integer)))) (some (.ok 17)) 50 (by rfl),
  Fixture.core "negative_quotient" (.intOp .div (.integer (-7)) (.integer 3))
    (some (.ok (-2))) 50 (by rfl),
  Fixture.core "negative_remainder" (.intOp .mod (.integer (-7)) (.integer 3))
    (some (.ok (-1))) 50 (by rfl),
  ⟨"word_big_endian", .toInteger (.word (0x96#8)), some (.ok 150), 3000⟩,
  ⟨"word_wrap", .toInteger (.wordArithmetic .add (.word (0xff#8)) (.word (0x02#8))),
    some (.ok 1), 100000⟩,
  ⟨"negative_word", .toInteger (.fromInteger 8 (.integer (-1))), some (.ok 255), 5000⟩,
  ⟨"word_rotate", .toInteger (.shift .rotateLeft (.word (0x96#8)) (.integer 3)),
    some (.ok 180), 4000⟩,
  ⟨"word_shift", .toInteger (.shift .right (.word (0x96#8)) (.integer 3)), some (.ok 18), 4000⟩,
  ⟨"zero_width", .toInteger (.shift .rotateLeft (.word (0#0)) (.integer 7)), some (.ok 0), 50⟩,
  Fixture.core "out_of_bounds" (.index (.generate (.finite 0) (.integer 1)) (.integer 0))
    (some (.error (.invalidIndex 0))) 50 (by rfl),
  Fixture.core "negative_index" (.index naturals (.integer (-1)))
    (some (.error (.invalidIndex (-1)))) 50 (by rfl),
  Fixture.core "division_error" (.intOp .div (.integer 1) (.integer 0))
    (some (.error .divideByZero)) 50 (by rfl),
  Fixture.core "strict_bit_error" (.ite (.bitOp .and (.bit false) (.error (.user "demanded")))
    (.integer 1) (.integer 0)) (some (.error (.user "demanded"))) 50 (by rfl),
  Fixture.core "literal_index_error" (.error (.invalidIndex 3))
    (some (.error (.invalidIndex 3))) 50 (by rfl),
  Fixture.core "literal_division_error" (.error .divideByZero)
    (some (.error .divideByZero)) 50 (by rfl),
  Fixture.core "divergence" (.diverge) (none) 100 (by rfl)]

end Interop.Cryptol.Examples
