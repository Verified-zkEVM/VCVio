/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VCVio Contributors
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue

/-!
# Adaptive paired-cache controls
-/

public section
open OracleComp OracleSpec OracleComp.RandomOraclePairedValue
open scoped OracleSpec.PrimitiveQuery

namespace VCVioTest.RandomOraclePairedValue

/-- Each public label returns a full two-bit word. -/
abbrev Words := Nat →ₒ Bool × Bool
/-- Two copies of the labels index the two individual bits. -/
abbrev Halves := (Nat ⊕ Nat) →ₒ Bool
/-- The caller also has its own private randomness. -/
abbrev World := unifSpec + Words

/-- A private draw and the first public answer select which public label is read next. -/
@[expose] def adaptive : OracleComp World (Bool × Bool) := do
  let coin ← liftM (World.query (.inl 1))
  let first ← liftM (World.query (.inr 7))
  let key := if (coin.val == 0) == first.1 then 7 else 99
  liftM (World.query (.inr key))

/-- An adaptive lookup retains the full caller result and both complete final caches. -/
theorem adaptive_joint :
    let e := Equiv.prodComm Bool Bool
    let initial : Words.QueryCache := (∅ : Words.QueryCache).cacheQuery 99 (false, true)
    (fun z : (Bool × Bool) × Words.QueryCache => (z.1, z.2, splitCache e z.2)) <$>
      (simulateQ Words.romImpl adaptive).run initial =ᵈ
    (fun z : (Bool × Bool) × Halves.QueryCache => (z.1, joinCache e z.2, z.2)) <$>
      (simulateQ Halves.romImpl (simulateQ (readHalves e) adaptive)).run
        (splitCache e initial) := by
  intro e initial
  exact evalDist_world_run_joint e adaptive initial

/-- A warm answer selects its own label again and returns the same asymmetric word twice. -/
theorem warm_repeat :
    let e := Equiv.prodComm Bool Bool
    let initial : Words.QueryCache :=
      ((∅ : Words.QueryCache).cacheQuery 99 (false, true)).cacheQuery 7 (true, false)
    let program : OracleComp World ((Bool × Bool) × Bool × Bool) := do
      let a ← liftM (World.query (.inr 7))
      let b ← liftM (World.query (.inr (if a.1 then 7 else 99)))
      pure (a, b)
    (simulateQ Halves.romImpl (simulateQ (readHalves e) program)).run (splitCache e initial) =
      pure (((true, false), (true, false)), splitCache e initial) := by
  intro e initial program
  simp [program, readHalves, romImpl, simulateQ_bind, StateT.run_bind, splitCache, initial, e]

end VCVioTest.RandomOraclePairedValue
