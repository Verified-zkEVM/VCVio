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

* **The class map.** An `H_msg` query is of class `forger` on the forger copy and `signer` on the
  signer copy; a tweakable-hash query and a derivation are of class `other` on either copy. The
  signer's role never reaches class `forger`, and a randomizer derivation stays one in either
  role.
* **The budgets at a concrete forger.** `replayForger` evaluates `H_msg` once and asks for one
  signature, so its role experiment makes at most two queries of class `forger`, one of class
  `signer` and one randomizer derivation. The lifted forger makes no derivation query.
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
    tapeClass core (.inl (.inl (.inl (.hmsg r s root msg)))) = .forger := rfl

example (r : core.Y) (s : core.PkSeed) (root : core.Y) (msg : List Byte) :
    tapeClass core (.inr (.inl (.inl (.hmsg r s root msg)))) = .signer := rfl

example (s : core.PkSeed) (k : core.AdrsKey) (xs : List core.Y) :
    tapeClass core (.inr (.inl (.inl (.thash s k xs)))) = .other := rfl

example (x : DeriveQuery core) : tapeClass core (.inl (.inr x)) = .other := rfl

/-- The forger's role sends an `H_msg` query to class `forger`. -/
example (r : core.Y) (s : core.PkSeed) (root : core.Y) (msg : List Byte) :
    AnswerTape.classOf (tapeClass core)
      (roleQuery core .forger (.inl (.inr (.inl (.hmsg r s root msg))))) = some .forger :=
  (classOf_roleQuery_eq_some_iff core .forger .forger _).2 ⟨rfl, trivial⟩

/-- The signer's role sends no query to class `forger`. -/
example (t : (deriveSpec core).Domain) :
    AnswerTape.classOf (tapeClass core) (roleQuery core .signer t) ≠ some .forger :=
  fun h => nomatch ((classOf_roleQuery_eq_some_iff core .signer .forger t).1 h).1

/-- A randomizer derivation is a randomizer point on either copy. -/
example (o : core.Y) (msg : List Byte) (r : Role) :
    IsRoleRandQuery core (roleQuery core r (.inr (.inr (o, msg)))) :=
  (isRoleRandQuery_roleQuery_iff core r _).2 trivial

/-! ## The budgets at a concrete forger -/

variable [SampleableType core.Y] [DecidableEq core.Y]
  (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed)

section Budgets

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf] (e : core.SkSeed ≃ core.Y)
  (pkSeedDist : ProbComp core.PkSeed)

example : IsQueryBoundP (roleExperiment core (replayForger core e optRand pkSeedDist) pkSeed)
    (fun t => AnswerTape.classOf (tapeClass core) t = some .forger) 2 :=
  isQueryBoundP_roleExperiment_forger core (romQueryBound_replayForger core e optRand pkSeedDist)
    pkSeed

example : IsQueryBoundP (roleExperiment core (replayForger core e optRand pkSeedDist) pkSeed)
    (fun t => AnswerTape.classOf (tapeClass core) t = some .signer) 1 :=
  isQueryBoundP_roleExperiment_signer core (romQueryBound_replayForger core e optRand pkSeedDist)
    pkSeed

example : IsQueryBoundP (roleExperiment core (replayForger core e optRand pkSeedDist) pkSeed)
    (IsRoleRandQuery core) 1 :=
  isQueryBoundP_roleExperiment_rand core (romQueryBound_replayForger core e optRand pkSeedDist)
    pkSeed

/-- The lifted replay forger makes no derivation query. -/
example (pk : PublicKeyCore core) :
    AllQueriesSatisfy
      ((deriveAdversary core (replayForger core e optRand pkSeedDist) pkSeed).main pk)
      (Sum.elim (fun t => t.isLeft = true) fun _ => True) :=
  allQueriesSatisfy_deriveAdversary_main core _ pkSeed pk

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
