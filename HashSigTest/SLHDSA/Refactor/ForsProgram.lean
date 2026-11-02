/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Graph.Fors.Program
public import HashSig.SLHDSA.Concrete.FIPS
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# Ordinary consumers of the generic effectful FORS traversal

Both actual SHAKE parameter sets use one core-parametric free programme and retain arbitrary
outer state and ordered additive cost. A nonfinite Nat carrier with Bool secret keys exercises
the same effectful theorem under a nonconstant state-sensitive handler.
-/

public section

universe u

open OracleComp OracleSpec SLHDSA SLHDSA.Graph SLHDSA.Concrete

namespace SLHDSA.Refactor.ForsProgramTest

local notation "vp128s" => FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams
local notation "vp192f" => FipsParameterSet.SLHDSA_SHAKE_192f.validatedParams

/-- The actual SHAKE-128s callback signer consumes the common structural programme theorem. -/
theorem shake128s_program (seed : (shakePrimitives (vp128s).params).Y)
    (key : ForsKey (vp128s).params) (md : List Byte)
    (cells : Node (vp128s).params → (shakePrimitives (vp128s).params).Y)
    (sameSeed : cells .secretSeed = seed) :
    forsSignWithSecret (shakePrimitives (vp128s).params).core
      (fun address value => query (spec := (Adrs × List (shakePrimitives (vp128s).params).Y) →ₒ
        (shakePrimitives (vp128s).params).Y) (address, [value]))
      (fun address left right => query (spec := (Adrs × List (shakePrimitives (vp128s).params).Y) →ₒ
        (shakePrimitives (vp128s).params).Y) (address, [left, right]))
      (fun address => query (spec := (Adrs × List (shakePrimitives (vp128s).params).Y) →ₒ
        (shakePrimitives (vp128s).params).Y) (address, [seed])) md key.address =
      Fors.reconstruct (shakePrimitives (vp128s).params).core key md <$>
        RandomOracleTraversal.evaluate (StructuralNode.input (vp128s).valid) updateCell
          (ForsSchedule.signing key md) cells :=
  Fors.forsSignWithSecret_eq_evaluate (vp128s).params (vp128s).valid
    (shakePrimitives (vp128s).params).core seed key md cells sameSeed

/-- The SHAKE-128s client retains every final outer state and noncommutative ordered cost. -/
theorem shake128s_observation (seed : (shakePrimitives (vp128s).params).Y)
    (key : ForsKey (vp128s).params) (md : List Byte)
    (cells : Node (vp128s).params → (shakePrimitives (vp128s).params).Y)
    (sameSeed : cells .secretSeed = seed) (m : Type → Type u) [Monad m]
    (State C : Type) [AddMonoid C]
    (handler : QueryImpl ((Adrs × List (shakePrimitives (vp128s).params).Y) →ₒ
      (shakePrimitives (vp128s).params).Y) (StateT State m))
    (cost : Adrs × List (shakePrimitives (vp128s).params).Y → C) (state : State) :
    ((simulateQ (handler.withAddCost cost)
      (forsSignWithSecret (shakePrimitives (vp128s).params).core
        (fun address value => query (spec := (Adrs × List (shakePrimitives (vp128s).params).Y) →ₒ
          (shakePrimitives (vp128s).params).Y) (address, [value]))
        (fun address left right => query (spec := (Adrs × List (shakePrimitives
            (vp128s).params).Y) →ₒ
          (shakePrimitives (vp128s).params).Y) (address, [left, right]))
        (fun address => query (spec := (Adrs × List (shakePrimitives (vp128s).params).Y) →ₒ
          (shakePrimitives (vp128s).params).Y) (address, [seed])) md key.address)).runAdd).run
              state =
      ((simulateQ (handler.withAddCost cost)
        (Fors.reconstruct (shakePrimitives (vp128s).params).core key md <$>
          RandomOracleTraversal.evaluate (StructuralNode.input (vp128s).valid) updateCell
            (ForsSchedule.signing key md) cells)).runAdd).run state :=
  congrArg (fun program => ((simulateQ (handler.withAddCost cost) program).runAdd).run state)
    (shake128s_program seed key md cells sameSeed)
/-- The actual SHAKE-192f callback signer consumes the common structural programme theorem. -/
theorem shake192f_program (seed : (shakePrimitives (vp192f).params).Y)
    (key : ForsKey (vp192f).params) (md : List Byte)
    (cells : Node (vp192f).params → (shakePrimitives (vp192f).params).Y)
    (sameSeed : cells .secretSeed = seed) :
    forsSignWithSecret (shakePrimitives (vp192f).params).core
      (fun address value => query (spec := (Adrs × List (shakePrimitives (vp192f).params).Y) →ₒ
        (shakePrimitives (vp192f).params).Y) (address, [value]))
      (fun address left right => query (spec := (Adrs × List (shakePrimitives (vp192f).params).Y) →ₒ
        (shakePrimitives (vp192f).params).Y) (address, [left, right]))
      (fun address => query (spec := (Adrs × List (shakePrimitives (vp192f).params).Y) →ₒ
        (shakePrimitives (vp192f).params).Y) (address, [seed])) md key.address =
      Fors.reconstruct (shakePrimitives (vp192f).params).core key md <$>
        RandomOracleTraversal.evaluate (StructuralNode.input (vp192f).valid) updateCell
          (ForsSchedule.signing key md) cells :=
  Fors.forsSignWithSecret_eq_evaluate (vp192f).params (vp192f).valid
    (shakePrimitives (vp192f).params).core seed key md cells sameSeed

/-- The SHAKE-192f client retains every final outer state and noncommutative ordered cost. -/
theorem shake192f_observation (seed : (shakePrimitives (vp192f).params).Y)
    (key : ForsKey (vp192f).params) (md : List Byte)
    (cells : Node (vp192f).params → (shakePrimitives (vp192f).params).Y)
    (sameSeed : cells .secretSeed = seed) (m : Type → Type u) [Monad m]
    (State C : Type) [AddMonoid C]
    (handler : QueryImpl ((Adrs × List (shakePrimitives (vp192f).params).Y) →ₒ
      (shakePrimitives (vp192f).params).Y) (StateT State m))
    (cost : Adrs × List (shakePrimitives (vp192f).params).Y → C) (state : State) :
    ((simulateQ (handler.withAddCost cost)
      (forsSignWithSecret (shakePrimitives (vp192f).params).core
        (fun address value => query (spec := (Adrs × List (shakePrimitives (vp192f).params).Y) →ₒ
          (shakePrimitives (vp192f).params).Y) (address, [value]))
        (fun address left right => query (spec := (Adrs × List (shakePrimitives
            (vp192f).params).Y) →ₒ
          (shakePrimitives (vp192f).params).Y) (address, [left, right]))
        (fun address => query (spec := (Adrs × List (shakePrimitives (vp192f).params).Y) →ₒ
          (shakePrimitives (vp192f).params).Y) (address, [seed])) md key.address)).runAdd).run
              state =
      ((simulateQ (handler.withAddCost cost)
        (Fors.reconstruct (shakePrimitives (vp192f).params).core key md <$>
          RandomOracleTraversal.evaluate (StructuralNode.input (vp192f).valid) updateCell
            (ForsSchedule.signing key md) cells)).runAdd).run state :=
  congrArg (fun program => ((simulateQ (handler.withAddCost cost) program).runAdd).run state)
    (shake192f_program seed key md cells sameSeed)

/-! ## A nonfinite node carrier and different secret-seed carrier -/

/-- A small arithmetic-valid FORS component contains two one-level trees. -/
@[expose] def params : Params :=
  { n := 1, h := 1, d := 1, hp := 1, a := 1, k := 2, lgw := 1 }

/-- Node values are unrestricted naturals while secret keys have a different carrier. -/
@[expose, reducible] def core : CorePrimitives params where
  PkSeed := Unit
  SkSeed := Bool
  SkPrf := Unit
  Y := Nat
  AdrsKey := Adrs
  adrsToKey := id
  PRF := fun _ secret address => address.word3 + if secret then 1 else 0
  PRFmsg := fun _ randomizer message => randomizer + message.length
  yToBytes := fun value => Vector.replicate params.n (UInt8.ofNat value)

/-- The origin identifies the actual bottom-layer FORS component. -/
@[expose] def key : ForsKey params := ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩

/-- Nonseed initial values are arbitrary and independent of the supplied secret value. -/
@[expose] def initial : Node params → Nat
  | .secretSeed => 7
  | .structural node => 1000 + node.address.word3

/-- The existing FORS body queries an explicit provider and ordered one/two-child payloads. -/
@[expose] def actual : OracleComp ((Adrs × List Nat) →ₒ Nat) (ForsSigCore params core) :=
  forsSignWithSecret core
    (fun address value => query (spec := (Adrs × List Nat) →ₒ Nat) (address, [value]))
    (fun address left right => query (spec := (Adrs × List Nat) →ₒ Nat) (address, [left, right]))
    (fun address => query (spec := (Adrs × List Nat) →ₒ Nat) (address, [7])) [] key.address

/-- The ordinary functional-cell traversal has only the existing signature readback projection. -/
@[expose] def graph : OracleComp ((Adrs × List Nat) →ₒ Nat) (ForsSigCore params core) :=
  Fors.reconstruct core key [] <$>
    RandomOracleTraversal.evaluate (StructuralNode.input (by decide : params.Valid))
      updateCell (ForsSchedule.signing key []) initial

/-- The Nat/Bool client is an actual instance of the same free-program theorem. -/
theorem nonfinite_program : actual = graph :=
  Fors.forsSignWithSecret_eq_evaluate params (by decide) core 7 key [] initial rfl

/-- Every actual label is retained, and its response depends on the payload and previous state. -/
@[expose] def handler : QueryImpl ((Adrs × List Nat) →ₒ Nat)
    (StateT (Nat × List (Adrs × List Nat)) Id) := fun label => do
  let state ← get
  set (state.1 + 1, state.2 ++ [label])
  return label.1.word3 + label.2.sum + state.1 + 1

/-- The same interpreted theorem retains the entire signature and nonconstant handler state. -/
theorem nonfinite_observation :
    ((simulateQ handler actual).run (0, [])) =
      ((simulateQ handler graph).run (0, [])) := by
  have interpreted := Fors.forsSignWithSecret_eq_simulateQ_evaluate params (by decide)
    core 7 key [] initial rfl (StateT (Nat × List (Adrs × List Nat)) Id) handler
  have natural := forsSignWithSecret_natural core (simulateQ' handler)
    (fun address value => query (spec := (Adrs × List Nat) →ₒ Nat) (address, [value]))
    (fun address value => handler (address, [value]))
    (fun address left right => query (spec := (Adrs × List Nat) →ₒ Nat) (address, [left, right]))
    (fun address left right => handler (address, [left, right]))
    (fun address => query (spec := (Adrs × List Nat) →ₒ Nat) (address, [7]))
    (fun address => handler (address, [7]))
    (fun _ _ => simulateQ_spec_query _ _) (fun _ _ _ => simulateQ_spec_query _ _)
    (fun _ _ => simulateQ_spec_query _ _) [] key.address
  exact congrArg (fun computation => computation.run (0, []))
    (natural.trans (interpreted.trans (simulateQ_map _ _ _).symm))

private theorem actual_six_queries : actual = (do
    let first ← query (spec := (Adrs × List Nat) →ₒ Nat) (forsSkAdrs key.address 0, [7])
    let firstSibling ← query (spec := (Adrs × List Nat) →ₒ Nat) (forsSkAdrs key.address 1, [7])
    let firstAuth ← query (spec := (Adrs × List Nat) →ₒ Nat)
      (forsNodeAdrs key.address 0 1, [firstSibling])
    let second ← query (spec := (Adrs × List Nat) →ₒ Nat) (forsSkAdrs key.address 2, [7])
    let secondSibling ← query (spec := (Adrs × List Nat) →ₒ Nat) (forsSkAdrs key.address 3, [7])
    let secondAuth ← query (spec := (Adrs × List Nat) →ₒ Nat)
      (forsNodeAdrs key.address 0 3, [secondSibling])
    return (⟨#[⟨first, ⟨#[firstAuth], by rfl⟩⟩,
      ⟨second, ⟨#[secondAuth], by rfl⟩⟩], by rfl⟩ : ForsSigCore params core)) := by
  simp only [actual, forsSignWithSecret, params, Vector.ofFnM_succ, Vector.ofFnM_zero,
    bind_pure_comp, pure_bind, PerfectMerkleTree.intrinsicAuthPathM,
    PerfectMerkleTree.merkleRootM, forsLeafWithSecret]
  rfl

/-- The interpreted nonfinite client makes all six calls and returns the complete expected trace. -/
theorem nonfinite_six_calls :
    ((simulateQ handler actual).run (0, [])).2.1 = 6 ∧
    (((simulateQ handler actual).run (0, [])).1.toList.map
      (fun signature => (signature.sk, signature.auth.toList))) = [(8, [14]), (13, [24])] ∧
    (((simulateQ handler actual).run (0, [])).2.2.map
      (fun label => (label.1.type, label.1.word3, label.2))) =
        [(6, 0, [7]), (6, 1, [7]), (3, 1, [10]),
          (6, 2, [7]), (6, 3, [7]), (3, 3, [15])] := by
  rw [actual_six_queries]
  simp only [simulateQ_bind, StateT.run_bind, bind_pure_comp]
  exact ⟨rfl, rfl, rfl⟩

end SLHDSA.Refactor.ForsProgramTest
