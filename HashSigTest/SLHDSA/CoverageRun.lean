/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.CoverageRun
public import HashSigTest.SLHDSA.Target

/-!
# The instrumented role run of the secret-free SLH-DSA experiment, checked

* **Hits.** A randomizer drawn at `(opt_rand, M)` hits the `H_msg` points at that randomizer and
  message under every public key, and no point at another randomizer, another message or of
  another kind.
* **Frame queries.** A forger-copy `H_msg` query, a tweakable-hash query and a secret derivation
  are frame queries; a signer-copy `H_msg` query and a randomizer derivation on either copy are
  not.
* **Coverer slots.** A signer slot reads the signer tape, and the forger slots and the designated
  positions skip the target position; a witness matches only where its slots read digests.
* **Covered points.** A covered point is cached; a cached hit point is covered.
* **The run at a concrete forger.** `replayForger` has budgets `(1, 1)`, so on its instrumented
  runs every point of class `signer` is logged, every logged point is of class `signer` or hit,
  and coverage of a fresh forgery yields a witness over a family with two forger-side answers
  and one signer-side answer.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.Security.CoverageRunTest

open Coverage TargetTest

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-! ## Hits -/

/-- A randomizer drawn as `u` at `(a, M)` hits the `H_msg` point at `u` and `M` under any key. -/
example (a u : core.Y) (M : List Byte) (pk : PublicKeyCore core) :
    randRel core (.inr (.inr (a, M))) u (hmsgPoint core pk u M) :=
  ⟨rfl, rfl⟩

/-- It hits no `H_msg` point at another message. -/
example (a u : core.Y) {M M' : List Byte} (h : M' ≠ M) (pk : PublicKeyCore core) :
    ¬ randRel core (.inr (.inr (a, M))) u (hmsgPoint core pk u M') :=
  fun hit => h hit.2

/-- It hits no `H_msg` point at another randomizer. -/
example (a : core.Y) {u u' : core.Y} (h : u' ≠ u) (M : List Byte) (pk : PublicKeyCore core) :
    ¬ randRel core (.inr (.inr (a, M))) u (hmsgPoint core pk u' M) :=
  fun hit => h hit.1

/-- It hits no derivation point. -/
example (a u : core.Y) (M : List Byte) (x : DeriveQuery core) :
    ¬ randRel core (.inr (.inr (a, M))) u (.inr x) :=
  nofun

/-- An `H_msg` answer hits nothing. -/
example (u : Bytes vp.params.m) (R : core.Y) (s : core.PkSeed) (root : core.Y)
    (M : List Byte) (p : (jointSpec core).Domain) :
    ¬ randRel core (.inl (.inl (.hmsg R s root M))) u p :=
  nofun

/-- Under one key, distinct messages give distinct `H_msg` points. -/
example (pk : PublicKeyCore core) (R : core.Y) {M M' : List Byte} (h : M ≠ M') :
    hmsgPoint core pk R M ≠ hmsgPoint core pk R M' :=
  fun e => h ((hmsgPoint_inj core pk).1 e).2

/-! ## Frame queries -/

/-- A forger-copy `H_msg` query is a frame query. -/
example (r : core.Y) (s : core.PkSeed) (root : core.Y) (msg : List Byte) :
    IsFrameQuery core (roleQuery core .forger (.inl (.inr (.inl (.hmsg r s root msg))))) :=
  ⟨id, nofun⟩

/-- A signer-copy tweakable-hash query is a frame query. -/
example (s : core.PkSeed) (k : core.AdrsKey) (xs : List core.Y) :
    IsFrameQuery core (roleQuery core .signer (.inl (.inr (.inl (.thash s k xs))))) :=
  ⟨id, nofun⟩

/-- A signer-copy `H_msg` query is not a frame query. -/
example (r : core.Y) (s : core.PkSeed) (root : core.Y) (msg : List Byte) :
    ¬ IsFrameQuery core (roleQuery core .signer (.inl (.inr (.inl (.hmsg r s root msg))))) :=
  fun h => h.2 rfl

/-- A randomizer derivation is not a frame query in either role. -/
example (r : Role) (o : core.Y) (msg : List Byte) :
    ¬ IsFrameQuery core (roleQuery core r (.inr (.inr (o, msg)))) :=
  fun h => h.1 ((isRoleRandQuery_roleQuery_iff core r _).2 trivial)

/-! ## Coverer slots -/

/-- A signer slot reads the signer tape. -/
example (lF lS : List (Bytes vp.params.m)) (n : Fin 2) :
    coverValue (qs := 1) (qh := 1) lF lS n (.inl 0) = lS[0]? :=
  rfl

/-- With the target at forger position `0`, the forger slot `0` reads forger position `1`. -/
example (lF lS : List (Bytes vp.params.m)) :
    coverValue (qs := 1) (qh := 1) lF lS 0 (.inr 0) = lF[1]? :=
  rfl

/-- With the target at forger position `1`, the forger slot `0` reads forger position `0`. -/
example (lF lS : List (Bytes vp.params.m)) :
    coverValue (qs := 1) (qh := 1) lF lS 1 (.inr 0) = lF[0]? :=
  rfl

/-- A witness whose single digit is covered by the signer tape matches when the signer digest
equals the target digest. -/
example (d : Bytes vp.params.m) (f : Fin vp.params.k → Fin 1 ⊕ Fin 1) (hf : ∀ i, f i = .inl 0) :
    TapeMatchOn ((0 : Fin 2), f) [d, d] [d] :=
  fun i => ⟨d, d, rfl, by simp only [hf i]; rfl, rfl, rfl⟩

/-- A witness whose signer slot reads past the signer tape does not match. -/
example (d : Bytes vp.params.m) [NeZero vp.params.k] :
    ¬ TapeMatchOn ((0 : Fin 2), fun _ => (.inl 0 : Fin 1 ⊕ Fin 1)) [d, d] [] :=
  fun h => by obtain ⟨_, _, _, hc, _⟩ := h 0; cases hc

/-- The designated positions skip the target: with the target at `0`, the forger slot `0` is
position `1`. -/
example (f : Fin vp.params.k → Fin 1 ⊕ Fin 1) (i : Fin vp.params.k) (hi : f i = .inr 0) :
    1 ∈ desigPos (vp := vp) ((0 : Fin 2), f) := by
  simp only [desigPos, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨0, ⟨i, hi⟩, rfl⟩

/-- The replay budget `(1, 1)` draws two forger-side answers, one signer-side answer and no
other tape. -/
example : tapeLength 1 1 .forger = 2 ∧ tapeLength 1 1 .signer = 1 ∧ tapeLength 1 1 .other = 0 :=
  ⟨rfl, rfl, rfl⟩

/-! ## The run at a concrete forger -/

variable [SampleableType core.Y] [DecidableEq core.Y] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf] [SampleableType core.SkSeed]
  [SampleableType core.SkPrf] (e : core.SkSeed ≃ core.Y)
  (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeedDist : ProbComp core.PkSeed)
  (pkSeed : core.PkSeed) (L : (j : TapeClass) → List (tapeClassRange core j))

/-- A point is covered exactly when it is cached and of class `signer` or hit; an uncached point
is not covered, whatever its class. -/
example (s : RoleState core) (p : (jointSpec core).Domain) (h : s.1.1 p = none) :
    ¬ Covered core s p :=
  fun hc => hc.1 h

/-- A cached hit point is covered. -/
example (s : RoleState core) (p : (jointSpec core).Domain) (u : (jointSpec core).Range p)
    (hc : s.1.1 p = some u) (hp : p ∈ s.2.2) : Covered core s p :=
  ⟨by rw [hc]; exact Option.some_ne_none u, .inr hp⟩

/-- The run starts with every point unclassified, so the invariant holds with the empty log. -/
example (pk : PublicKeyCore core) :
    RunInv core pk [] ((∅, L), (AnswerTape.ClassPos.init, ∅)) :=
  RunInv.init core pk L

/-- On a run of the replay forger, every point of class `signer` is a logged `H_msg` point. -/
example {z : DeriveOutcome core × RoleState core}
    (hz : z ∈ support (roleRun core (replayForger core e optRand pkSeedDist) pkSeed L))
    (p : (jointSpec core).Domain) (hp : z.2.2.1.cls p = some .signer) :
    ∃ en ∈ z.1.log, p = hmsgPoint core z.1.pk en.2.randomness en.1 :=
  exists_mem_log_of_cls_eq_signer hz p hp

/-- On a run of the replay forger, every logged `H_msg` point is of class `signer` or hit. -/
example {z : DeriveOutcome core × RoleState core}
    (hz : z ∈ support (roleRun core (replayForger core e optRand pkSeedDist) pkSeed L))
    {en : (t : (List Byte →ₒ GeneralScheme.SignatureCore vp core).Domain) ×
      (List Byte →ₒ GeneralScheme.SignatureCore vp core).Range t} (hen : en ∈ z.1.log) :
    z.2.2.1.cls (hmsgPoint core z.1.pk en.2.randomness en.1) = some .signer ∨
      hmsgPoint core z.1.pk en.2.randomness en.1 ∈ z.2.2.2 :=
  cls_eq_signer_or_mem_hits_of_mem_log hz hen

/-- On a run of the replay forger, the signing key is the public key. -/
example {z : DeriveOutcome core × RoleState core}
    (hz : z ∈ support (roleRun core (replayForger core e optRand pkSeedDist) pkSeed L)) :
    z.1.pk = z.1.sk :=
  (runInv_of_mem_support_roleRun hz).1

/-- On a run of the replay forger over a family drawn at its budget, coverage of a fresh forgery
yields a witness with a forger position among two and a coverer slot per FORS tree. -/
example (s : core.SkSeed × core.SkPrf)
    (hL : L ∈ support (AnswerTape.tapeFamily (tapeClassRange core) (tapeLength 1 1)))
    (z : DeriveOutcome core × RoleState core)
    (hz : z ∈ support (roleRun core (replayForger core e optRand pkSeedDist) pkSeed L))
    (hcov : RunItsrCovered core (DeriveOutcome.fill core s z.1, z.2.1.1.fst)) :
    ∃ w : Fin 2 × (Fin vp.params.k → Fin 1 ⊕ Fin 1),
      TapeMatch core w L ∧ AnswerTape.HitAll (randRel core) .forger (desigPos w) z.2 :=
  exists_witness_of_runItsrCovered core (romQueryBound_replayForger core e optRand pkSeedDist)
    pkSeed s L hL z hz hcov

end SLHDSA.Security.CoverageRunTest
