/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/
module

public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed.Residual

/-! # Repeated and adaptive queries to residual tables -/

public section
open OracleSpec OracleComp SecretEncoding
open scoped OracleSpec.PrimitiveQuery
namespace VCVioTest.RandomOracleResidualTables

abbrev Table := Bool →ₒ Bool
abbrev World := (Table + Table).withDerivations (Bool ⊕ Bool) Bool

/-- A public reply selects a private start, and an auxiliary reply chooses a residual key twice. -/
@[expose] def mixed : OracleComp World (Bool × Bool × Bool × Bool × Bool) := do
  let a ← liftM (World.query (.inl (.inr (.inl false))))
  let b ← liftM (World.query (.inl (.inr (.inr false))))
  let c ← liftM (World.query (.inr (.inl a)))
  let d ← liftM (World.query (.inr (.inr b)))
  let again ← liftM (World.query (.inr (.inr b)))
  pure (a, b, c, d, again)

example (s : Residual.Source Table Table Bool Bool Bool) :
    (simulateQ (idealImpl Table Bool Bool)
      ((simulateQ (Residual.handler (pub := Table) (aux := Table)
        (X := Bool) (Z := Bool) (R := Bool)) mixed).run (Residual.localState _ _ s))).run
          (Residual.baseState _ _ s) =
    (fun w => ((w.1, Residual.localState _ _ w.2), Residual.baseState _ _ w.2)) <$>
      (simulateQ (idealImpl (Table + Table) (Bool ⊕ Bool) Bool) mixed).run s :=
  Residual.run _ _ _ _ _ mixed s

/-- Four warm tables can return conflicting bits at the same underlying Boolean key. -/
example :
    let s : Residual.Source Table Table Bool Bool Bool :=
      (.ofFn (Sum.rec (fun _ => some false) fun _ => some true),
       .ofFn (Sum.elim (fun _ => some true) fun _ => some false))
    (simulateQ (idealImpl (Table + Table) (Bool ⊕ Bool) Bool) mixed).run s =
      pure ((false, true, true, false, false), s) := by
  simp [mixed, idealImpl]

end VCVioTest.RandomOracleResidualTables
