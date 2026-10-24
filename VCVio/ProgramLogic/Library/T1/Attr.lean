/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Mathlib.Tactic.Attr.Register

/-!
# The `simulateQ_nf` simp set

`simulateQ_nf` rewrites the run of a simulated program, `(simulateQ impl oa).run s`,
`(simulateQ impl oa).run' s`, or the run of a `WriterT` simulation, into the base monad: the
simulation is pushed through `pure`, `>>=`, `<$>`, `if` and the queries, sum handlers dispatch to
their summands, and the `StateT` and `WriterT` layers are run step by step. The result is a chain
of binds over the one-step handler runs `(impl t).run s`, the shape consumed by the support
calculus of `VCVio.ProgramLogic.Library.T1.Support`.

The set is registered here, apart from its lemmas, because `register_simp_attr` does not take
effect in the file that declares it. Its members are tagged in
`VCVio.ProgramLogic.Library.T1.RunNF`.
-/

public section

/-- Rewrite rules running a simulated program into its base monad. -/
register_simp_attr simulateQ_nf
