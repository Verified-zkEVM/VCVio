/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVioFoxglove

/-!
# Canaries for the Foxglove bridge

* **Import closure.** The bridge imports Foxglove's logic, not its worked examples or
  counterexamples, which cost build time and add nothing to the bridge.
* **Instances.** `BernoulliM` keeps Foxglove's own (identity) interpretation: the
  `OracleComp` instance must not capture it.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for m in [`Foxglove.Example, `Foxglove.Interp.Bernoulli.Example,
      `Foxglove.Rules.WP.Counterexamples, `Foxglove] do
    if env.header.moduleNames.contains m then
      throwError "closure canary: the bridge imports {m}"

open Foxglove Interp in
example {α : Type} (t : BernoulliM α) : BernoulliInterpretable.interp t = t := rfl
