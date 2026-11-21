/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/
module

public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed.Reindex

/-! # Reindexing two independent classes of private derivations -/
public section
open OracleSpec OracleComp SecretEncoding
open scoped OracleSpec.PrimitiveQuery
namespace VCVioTest.RandomOracleDerivationKeys

abbrev Public := Unit →ₒ Bool
abbrev Key := Nat ⊕ Bool
abbrev TargetKey := Bool ⊕ Nat
abbrev Source := Public.withDerivations Key Bool
abbrev perm := Equiv.sumComm Nat Bool

/-- A public query can choose a private slot, and its private reply can select a residual slot. -/
@[expose] def adaptive : OracleComp Source Bool := do
  let choose ← liftM (Source.query (.inl (.inr ())))
  let response ← liftM (Source.query (.inr (.inl (if (choose : Bool) = true then 7 else 11))))
  liftM (Source.query (.inr (.inr response)))

example (s : SplitCache Public Key Bool) :
    Prod.map id (reindexState Public perm) <$>
      (simulateQ (idealImpl Public Key Bool) adaptive).run s =
      (simulateQ (idealImpl Public TargetKey Bool)
        (simulateQ (reindexQueries Public perm) adaptive)).run (reindexState Public perm s) :=
  reindex_ideal Public perm adaptive s

/-- Distinct private slots stay distinct even when both tables were already populated. -/
example :
    let s : SplitCache Public Key Bool :=
      (.ofFn (fun _ => some true), .ofFn (Sum.elim (fun _ => some false) fun _ => some true))
    let v := reindexState Public perm s
    v.1 () = some true ∧ v.2 (.inl true) = some true ∧ v.2 (.inr 7) = some false :=
  ⟨rfl, rfl, rfl⟩

end VCVioTest.RandomOracleDerivationKeys
