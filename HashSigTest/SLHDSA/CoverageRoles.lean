/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.CoverageRoles
public import HashSigTest.SLHDSA.Target

/-!
# Role tagging and per-class budgets of the secret-free SLH-DSA experiment, checked

* **The class map.** An `H_msg` query is class `F` on the forger copy and class `S` on the signer
  copy; a tweakable-hash query and a derivation are class `N` on either copy.
* **The budgets at a concrete forger.** `replayForger` evaluates `H_msg` once and asks for one
  signature, so its role experiment makes at most two class-`F` queries, one class-`S` query and
  one randomizer derivation.
* **The signing and verification bounds are attained.** With a fixed `opt_rand`, signing makes an
  `H_msg` query and a randomizer derivation, and verification makes an `H_msg` query, so none of
  the bounds `1` drops to `0`.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.Security.CoverageRolesTest

open Coverage TargetTest

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-! ## The class map -/

example (r : core.Y) (s : core.PkSeed) (root : core.Y) (msg : List Byte) :
    tau core (.inl (.inl (.inl (.hmsg r s root msg)))) = .F := rfl

example (r : core.Y) (s : core.PkSeed) (root : core.Y) (msg : List Byte) :
    tau core (.inr (.inl (.inl (.hmsg r s root msg)))) = .S := rfl

example (s : core.PkSeed) (k : core.AdrsKey) (xs : List core.Y) :
    tau core (.inr (.inl (.inl (.thash s k xs)))) = .N := rfl

example (x : DeriveQuery core) : tau core (.inl (.inr x)) = .N := rfl

/-- The forger's role sends an `H_msg` query to class `F`. -/
example (r : core.Y) (s : core.PkSeed) (root : core.Y) (msg : List Byte) :
    IsClsQuery core .F (roleFQuery core (.inl (.inr (.inl (.hmsg r s root msg))))) :=
  (isClsQuery_F_roleFQuery_iff core _).2 trivial

/-! ## The budgets at a concrete forger -/

variable [SampleableType core.Y] [DecidableEq core.Y]
  (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed)

section Budgets

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf] (e : core.SkSeed ≃ core.Y)
  (pkSeedDist : ProbComp core.PkSeed)

example : IsQueryBoundP (roleExperiment core (replayForger core e optRand pkSeedDist) pkSeed)
    (IsClsQuery core .F) 2 :=
  isQueryBoundP_roleExperiment_F core (romQueryBound_replayForger core e optRand pkSeedDist)
    pkSeed

example : IsQueryBoundP (roleExperiment core (replayForger core e optRand pkSeedDist) pkSeed)
    (IsClsQuery core .S) 1 :=
  isQueryBoundP_roleExperiment_S core (romQueryBound_replayForger core e optRand pkSeedDist)
    pkSeed

example : IsQueryBoundP (roleExperiment core (replayForger core e optRand pkSeedDist) pkSeed)
    (IsRoleRandQuery core) 1 :=
  isQueryBoundP_roleExperiment_rand core (romQueryBound_replayForger core e optRand pkSeedDist)
    pkSeed

/-- Collapsing the roles of the replay forger's experiment gives its secret-free experiment. -/
example : simulateQ (SecretEncoding.collapseFwd (hashSpec core) (DeriveQuery core) core.Y)
      (roleExperiment core (replayForger core e optRand pkSeedDist) pkSeed) =
    unforgeableTranscriptExperiment (deriveAdversary core (replayForger core e optRand pkSeedDist)
      pkSeed) :=
  simulateQ_collapseFwd_roleExperiment core _ pkSeed

end Budgets

/-! ## The signing and verification bounds are attained -/

/-- Signing makes an `H_msg` query. -/
theorem not_isQueryBoundP_deriveScheme_sign_hmsg_zero (y : core.Y) (pk sk : PublicKeyCore core)
    (msg : List Byte) :
    ¬ IsQueryBoundP ((deriveScheme core (fun _ => pure y) pkSeed).sign pk sk msg)
      (IsHmsgQuery core) 0 := fun h =>
  Nat.lt_irrefl 0 (((isQueryBoundP_query_bind_iff _ _ _ _).1
    (((isQueryBoundP_query_bind_iff _ _ _ _).1 h).2 y)).1.resolve_left (not_not.2 trivial))

/-- Signing makes a randomizer derivation. -/
theorem not_isQueryBoundP_deriveScheme_sign_rand_zero (y : core.Y) (pk sk : PublicKeyCore core)
    (msg : List Byte) :
    ¬ IsQueryBoundP ((deriveScheme core (fun _ => pure y) pkSeed).sign pk sk msg)
      (IsRandQuery core) 0 := fun h =>
  Nat.lt_irrefl 0 (((isQueryBoundP_query_bind_iff _ _ _ _).1 h).1.resolve_left
    (not_not.2 trivial))

/-- Verification makes an `H_msg` query. -/
theorem not_isQueryBoundP_deriveScheme_verify_hmsg_zero (pk : PublicKeyCore core)
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp core) :
    ¬ IsQueryBoundP ((deriveScheme core optRand pkSeed).verify pk msg sig)
      (IsHmsgQuery core) 0 := fun h =>
  Nat.lt_irrefl 0 (((isQueryBoundP_query_bind_iff _ _ _ _).1 h).1.resolve_left
    (not_not.2 trivial))

end SLHDSA.Security.CoverageRolesTest
