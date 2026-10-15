/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Model.Syntax

/-!
# Concrete primitive operations

The domain semantics and the abstract machine share the meanings of primitive
operations. Control flow, laziness, binding, and recursion are interpreted
separately. Integer division truncates toward zero, as in Cryptol 3.6.0.
-/

public section

namespace Interop.Cryptol

/-- Concrete meaning of an integer primitive, including its error cases. -/
@[expose] def IntOp.eval : IntOp → Int → Int → Except EvalError Int
  | .add, x, y => .ok (x + y)
  | .sub, x, y => .ok (x - y)
  | .mul, x, y => .ok (x * y)
  | .div, x, y => if y = 0 then .error .divideByZero else .ok (x.tdiv y)
  | .mod, x, y => if y = 0 then .error .divideByZero else .ok (x.tmod y)

/-- Concrete meaning of a bit primitive; both operands are demanded. -/
@[expose] def BitOp.eval : BitOp → Bool → Bool → Bool
  | .and, x, y => x && y
  | .or, x, y => x || y
  | .xor, x, y => Bool.xor x y

end Interop.Cryptol
