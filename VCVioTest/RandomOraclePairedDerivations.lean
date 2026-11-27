/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.Derivations

/-!
# Independent warm public and private words at the same key

The public and private tables may contain different words at the same key. Splitting their
rows keeps both tables and the auxiliary reply in an adaptive run.
-/

public section
open OracleSpec OracleComp RandomOraclePairedValue.Derivations
open scoped OracleSpec.PrimitiveQuery

namespace VCVioTest.RandomOraclePairedDerivations
/-- A single auxiliary address returning one Boolean. -/
abbrev Auxiliary := Unit →ₒ Bool
/-- Public and private tables of Boolean pairs together with the auxiliary oracle. -/
abbrev Source := World Auxiliary Nat Nat (Bool × Bool)

/-- A private draw and the public and private answers determine the last key. -/
@[expose] def adaptive : OracleComp Source (Bool × Bool) := do
  let coin ← liftM (Source.query (.inl (.inl 1)))
  let publicBits ← liftM (Source.query (.inl (.inr (.inl 7))))
  let privateBits ← liftM (Source.query (.inr 7))
  let extra ← liftM (Source.query (.inl (.inr (.inr ()))))
  let k := if (coin.val == 0) == (publicBits.1 && privateBits.2 && extra) then 7 else 12
  liftM (Source.query (.inr k))

/-- The full caller observation, auxiliary cache and both word tables have one joint law. -/
example (initial : Cache Auxiliary Nat Nat (Bool × Bool)) :
    let e := Equiv.prodComm Bool Bool
    (fun z => (z.1, z.2, splitState Auxiliary e z.2)) <$>
      (simulateQ (SecretEncoding.idealImpl ((Nat →ₒ Bool × Bool) + Auxiliary)
        Nat (Bool × Bool))
        adaptive).run initial =ᵈ
    (fun z => (z.1, joinState Auxiliary e z.2, z.2)) <$>
      (simulateQ (SecretEncoding.idealImpl (((Nat ⊕ Nat) →ₒ Bool) + Auxiliary)
        (Nat ⊕ Nat) Bool)
        (simulateQ (expand Auxiliary e) adaptive)).run (splitState Auxiliary e initial) :=
  run_joint Auxiliary (Equiv.prodComm Bool Bool) adaptive initial

/-- The same key can store opposite words in the two tables while the auxiliary row stays warm. -/
example :
    let c : (Nat →ₒ Bool × Bool).QueryCache := .ofFn (fun _ => some (false, true))
    let p : (Nat →ₒ Bool × Bool).QueryCache := .ofFn (fun _ => some (true, false))
    let a : Auxiliary.QueryCache := .ofFn (fun _ => some true)
    let s := splitState Auxiliary (Equiv.refl _) (QueryCache.addEquiv _ Auxiliary (c, a), p)
    s.1 (.inl (.inl 7)) = some false ∧ s.1 (.inl (.inr 7)) = some true ∧
    s.2 (.inl 7) = some true ∧ s.2 (.inr 7) = some false ∧ s.1 (.inr ()) = some true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end VCVioTest.RandomOraclePairedDerivations
