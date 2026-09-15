/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import VCVioTest.InnerProduct.Checks

/-!
# Inner-product replay regression runner

Runs the finite-field folding and retained-work checks as part of `lake test`.
-/

public section

def main : IO Unit := InnerProduct.Checks.run
