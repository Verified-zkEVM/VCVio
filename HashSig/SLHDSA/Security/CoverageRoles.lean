/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.AddressDiscipline
public import HashSig.SLHDSA.Security.SeedCoupling
public import VCVio.CryptoFoundations.SignatureAlg.Tagged
public import VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape.Position
public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeedCollapse

/-!
# Role tagging of the secret-free SLH-DSA experiment and its per-class budgets

The ideal game of the secret-free run of SLH-DSA caches the hash queries and the derivations
on one joint interface, `jointSpec core = hashSpec core + (DeriveQuery core →ₒ core.Y)`. This
module runs the transcript experiment of `deriveScheme` with every query tagged by the role
that issues it, over the duplicated forwarded interface
`roleSpec core = unifSpec + (jointSpec core + jointSpec core)`: the forger copy (`inl`) carries
the forger's queries and verification, the signer copy (`inr`) carries key generation and
signing, and uniform draws are forwarded.

* *Roles.* `roleImpl core r` sends every query of `deriveSpec core` to the copy of the role
  `r : Role`, as the query `roleQuery core r t`. `roleScheme core optRand pkSeed` interprets key
  generation and signing in the signer's role and verification in the forger's role, so the
  verifier's `H_msg` query is on the forger copy, and `roleExperiment core adv pkSeed` is the
  transcript experiment of `roleScheme` against the forger interpreted in the forger's role.
  Collapsing the copies with `SecretEncoding.collapseFwd` gives the secret-free experiment back
  (`simulateQ_collapseFwd_roleExperiment`). The lifted forger itself makes no derivation query
  (`allQueriesSatisfy_deriveAdversary_main`).
* *Tape classes.* `TapeClass` names three classes of queries of the duplicated joint interface:
  forger-copy `H_msg` (`forger`), signer-copy `H_msg` (`signer`) and every other query (`other`).
  `tapeClass core` classifies, `tapeClassRange core` gives the answer type of each class, and
  `range_eq_tapeClassRange` matches the two. A query of the role-tagged interface is of class
  `j` when `AnswerTape.classOf (tapeClass core) t = some j`.
* *Query predicates.* `IsHmsgQuery core` and `IsRandQuery core` select the `H_msg` queries and
  the randomizer derivations of `deriveSpec core`; `IsRandPoint core` selects the randomizer
  derivations of `jointSpec core`, and `IsRoleRandQuery core` those of either copy.
* *Query shapes of the honest programs.* Signing draws `opt_rand`, makes the randomizer
  derivation, then the `H_msg` query, then `signTail` (`deriveScheme_sign_eq`). The tail and key
  generation make no `H_msg` query and no randomizer derivation, verification makes at most one
  `H_msg` query and no randomizer derivation, and a signature makes at most one of each. These
  are instances of the address discipline of `HashSig.SLHDSA.AddressDiscipline`.
* *Per-class budgets.* For a forger with hash budget `qh` and signing budget `qs`
  (`UnforgeableAdversary.RomQueryBound`), the role experiment makes at most `qh + 1` queries of
  class `forger` (`isQueryBoundP_roleExperiment_forger`), at most `qs` of class `signer`
  (`isQueryBoundP_roleExperiment_signer`) and at most `qs` randomizer derivations
  (`isQueryBoundP_roleExperiment_rand`). Cached and uncached queries count alike: the budgets
  are of the program, before any handler answers it.

## Scope

* The statements are per public seed `pkSeed`.
* This module states equations of programs and query budgets; it bounds no probability.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.Security.Coverage

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-! ## The role-tagged interface -/

/-- The joint cached interface of the ideal game: the hash oracles and the derivations. -/
abbrev jointSpec := hashSpec core + (DeriveQuery core →ₒ core.Y)

/-- The role-tagged interface: uniform draws, the forger copy (`inl`) and the signer copy
(`inr`) of the joint interface. -/
abbrev roleSpec := unifSpec + (jointSpec core + jointSpec core)

/-- The tape classes of a query of the duplicated joint interface. -/
inductive TapeClass
  /-- An `H_msg` query on the forger copy. -/
  | forger
  /-- An `H_msg` query on the signer copy. -/
  | signer
  /-- Any other query. -/
  | other
  deriving DecidableEq

/-- There are three tape classes. -/
instance : Finite TapeClass :=
  Finite.of_surjective ![TapeClass.forger, .signer, .other]
    fun | .forger => ⟨0, rfl⟩ | .signer => ⟨1, rfl⟩ | .other => ⟨2, rfl⟩

/-- The tape classes as a finite type, obtained from `Finite` so that no enumeration is
compiled. -/
noncomputable instance : Fintype TapeClass := Fintype.ofFinite TapeClass

/-- The answer type of each tape class: a digest for the two `H_msg` classes, a node otherwise. -/
abbrev tapeClassRange : TapeClass → Type
  | .forger | .signer => Bytes vp.params.m
  | .other => core.Y

/-- Each tape class draws its answers from the global sampler of its answer type. -/
instance instSampleableTypeTapeClassRange [SampleableType core.Y] :
    (j : TapeClass) → SampleableType (tapeClassRange core j)
  | .forger | .signer => inferInstanceAs (SampleableType (Bytes vp.params.m))
  | .other => inferInstanceAs (SampleableType core.Y)

/-- The class of a query of the duplicated joint interface: an `H_msg` query is of class
`forger` on the forger copy and `signer` on the signer copy; every other query is of class
`other`. -/
@[expose] def tapeClass : (jointSpec core + jointSpec core).Domain → TapeClass
  | .inl (.inl (.inl (.hmsg _ _ _ _))) => .forger
  | .inr (.inl (.inl (.hmsg _ _ _ _))) => .signer
  | _ => .other

/-- Every query of the duplicated joint interface is answered in the answer type of its class. -/
theorem range_eq_tapeClassRange : ∀ t : (jointSpec core + jointSpec core).Domain,
    (jointSpec core + jointSpec core).Range t = tapeClassRange core (tapeClass core t) := by
  rintro (((t | t) | x) | ((t | t) | x)) <;> (try cases t) <;> rfl

/-- A randomizer derivation of the joint interface. -/
@[expose] def IsRandPoint : (jointSpec core).Domain → Prop
  | .inr (.inr _) => True
  | _ => False

instance : DecidablePred (IsRandPoint core) := by
  rintro ((t | t) | (k | x)) <;> simp only [IsRandPoint] <;> infer_instance

/-- A randomizer derivation on either copy of the role-tagged interface. -/
@[expose] def IsRoleRandQuery : (roleSpec core).Domain → Prop
  | .inl _ => False
  | .inr (.inl t) | .inr (.inr t) => IsRandPoint core t

instance : DecidablePred (IsRoleRandQuery core) := by
  rintro (n | (t | t)) <;> simp only [IsRoleRandQuery] <;> infer_instance

/-! ## Query predicates of the secret-free interface -/

/-- An `H_msg` query of the secret-free interface. -/
@[expose] def IsHmsgQuery : (deriveSpec core).Domain → Prop
  | .inl (.inr (.inl (.hmsg _ _ _ _))) => True
  | _ => False

/-- A randomizer derivation of the secret-free interface. -/
@[expose] def IsRandQuery : (deriveSpec core).Domain → Prop
  | .inr (.inr _) => True
  | _ => False

instance : DecidablePred (IsHmsgQuery core) := by
  rintro ((n | ((t | t) | t)) | x) <;> (try cases t) <;> simp only [IsHmsgQuery] <;>
    infer_instance

instance : DecidablePred (IsRandQuery core) := by
  rintro ((n | t) | (k | x)) <;> simp only [IsRandQuery] <;> infer_instance

/-! ## Roles -/

/-- The two roles of the experiment: the forger, whose queries and verification go to the forger
copy, and the signer, whose key generation and signing go to the signer copy. -/
inductive Role
  /-- The forger and the verifier. -/
  | forger
  /-- Key generation and signing. -/
  | signer
  deriving DecidableEq

/-- The tape class of the `H_msg` queries of a role. -/
@[expose] def Role.tapeClass : Role → TapeClass
  | .forger => .forger
  | .signer => .signer

/-- The query of the role-tagged interface that role `r` issues for a query `t` of the
secret-free interface: a uniform draw is forwarded, and any other query goes to the copy of
`r`. -/
@[expose] def roleQuery : Role → (deriveSpec core).Domain → (roleSpec core).Domain
  | _, .inl (.inl n) => .inl n
  | .forger, .inl (.inr t) => .inr (.inl (.inl t))
  | .forger, .inr x => .inr (.inl (.inr x))
  | .signer, .inl (.inr t) => .inr (.inr (.inl t))
  | .signer, .inr x => .inr (.inr (.inr x))

/-- Role `r` answers a query `t` of the secret-free interface by the one query
`roleQuery core r t`. -/
@[expose] def roleImpl : Role → QueryImpl (deriveSpec core) (OracleComp (roleSpec core))
  | _, .inl (.inl n) => liftM ((roleSpec core).query (.inl n))
  | .forger, .inl (.inr t) => liftM ((roleSpec core).query (.inr (.inl (.inl t))))
  | .forger, .inr x => liftM ((roleSpec core).query (.inr (.inl (.inr x))))
  | .signer, .inl (.inr t) => liftM ((roleSpec core).query (.inr (.inr (.inl t))))
  | .signer, .inr x => liftM ((roleSpec core).query (.inr (.inr (.inr x))))

/-- A role answers a query by one query, `roleQuery core r t`. -/
theorem isQueryBoundP_roleImpl_iff (r : Role) (t : (deriveSpec core).Domain)
    {q : (roleSpec core).Domain → Prop} [DecidablePred q] {n : ℕ} :
    IsQueryBoundP (roleImpl core r t) q n ↔ (q (roleQuery core r t) → 0 < n) := by
  rcases r with _ | _ <;> rcases t with ((n | t) | x) <;> exact isQueryBoundP_query_iff _ _ _

/-- Collapsing the copies undoes a role. -/
theorem collapseFwd_comp_roleImpl (r : Role) :
    SecretEncoding.collapseFwd (hashSpec core) (DeriveQuery core) core.Y ∘ₛ roleImpl core r =
      QueryImpl.id' (deriveSpec core) := by
  rcases r with _ | _ <;> ext ((n | t) | x) <;> rfl

/-- A role read through the lift of the forger's queries into the derivation world. -/
theorem roleImpl_comp_withDerivationsLift_apply (r : Role) (t : (unifSpec + hashSpec core).Domain) :
    (roleImpl core r ∘ₛ (hashSpec core).withDerivationsLift (DeriveQuery core) core.Y) t =
      roleImpl core r (.inl t) := by
  simp only [QueryImpl.apply_compose, OracleSpec.withDerivationsLift, simulateQ_spec_query]

/-- **Budget transfer through a role.** If every `q`-query that role `r` issues comes from a
`p`-query of the secret-free interface, then a program with at most `n` `p`-queries, run in role
`r`, makes at most `n` `q`-queries: the role answers each query by exactly one query. -/
theorem isQueryBoundP_simulateQ_roleImpl (r : Role) {α : Type}
    {oa : OracleComp (deriveSpec core) α} {p : (deriveSpec core).Domain → Prop} [DecidablePred p]
    {q : (roleSpec core).Domain → Prop} [DecidablePred q] {n : ℕ}
    (h : IsQueryBoundP oa p n) (hq : ∀ t, q (roleQuery core r t) → p t) :
    IsQueryBoundP (simulateQ (roleImpl core r) oa) q n :=
  h.simulateQ_of_step (fun t _ => (isQueryBoundP_roleImpl_iff core r t).2 fun _ => Nat.one_pos)
    fun t ht => (isQueryBoundP_roleImpl_iff core r t).2 fun h => absurd (hq t h) ht

/-- Role `r` issues a query of the `H_msg` class of role `s` exactly at an `H_msg` query, and
only when `r = s`. -/
theorem classOf_roleQuery_eq_some_iff (r s : Role) (t : (deriveSpec core).Domain) :
    AnswerTape.classOf (tapeClass core) (roleQuery core r t) = some s.tapeClass ↔
      r = s ∧ IsHmsgQuery core t := by
  rcases r with _ | _ <;> rcases s with _ | _ <;> rcases t with ((n | ((t | t) | t)) | x) <;>
    (try cases t) <;> simp [AnswerTape.classOf, roleQuery, tapeClass, Role.tapeClass, IsHmsgQuery]

/-- Every role issues exactly the randomizer derivations as randomizer derivations. -/
theorem isRoleRandQuery_roleQuery_iff (r : Role) (t : (deriveSpec core).Domain) :
    IsRoleRandQuery core (roleQuery core r t) ↔ IsRandQuery core t := by
  rcases r with _ | _ <;> rcases t with ((n | t) | (k | x)) <;>
    simp [IsRoleRandQuery, IsRandPoint, roleQuery, IsRandQuery]

/-! ## Query shapes of the honest programs -/

section Programs

/-- A tweakable-hash query makes no `p`-query when no tweakable-hash query is a `p`-query. -/
private theorem isQueryBoundP_tl {p : (deriveSpec core).Domain → Prop} [DecidablePred p]
    (hp : ∀ s k xs, ¬ p (.inl (.inr (.inl (.thash s k xs))))) (s : core.PkSeed) (a : Adrs)
    (xs : List core.Y) :
    IsQueryBoundP (PublicHash.tl core s a xs : OracleComp (deriveSpec core) core.Y) p 0 :=
  (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hp _ _ _)

variable [SampleableType core.Y]

/-- Signing after the `H_msg` query at randomizer `R` has returned `digest`: FORS signing, FORS
public-key recovery and hypertree signing at public seed `pkSeed`, with every secret value a
derivation. -/
@[expose] def signTail (pkSeed : core.PkSeed) (R : core.Y) (digest : Bytes vp.params.m) :
    OracleComp (deriveSpec core) (GeneralScheme.SignatureCore vp core) := do
  let parts := splitDigest vp.params digest
  let forsSig ← forsSignWithSecretM core (deriveSecret core) parts.md.toList pkSeed parts.forsAdrs
  let forsPk ← forsPkFromSigM core forsSig parts.md.toList pkSeed parts.forsAdrs
  let htSig ← GeneralHypertree.signWithSecretM core (deriveSecret core) forsPk pkSeed parts
  return ⟨R, forsSig, htSig⟩

/-- At a secret-key address the derivation-backed secret makes no `p`-query when no secret
derivation is a `p`-query. -/
private theorem isQueryBoundP_deriveSecret {p : (deriveSpec core).Domain → Prop}
    [DecidablePred p] (hp : ∀ k, ¬ p (.inr (.inl k))) (a : Adrs) (ha : a.IsSecretKey) :
    IsQueryBoundP (deriveSecret core a) p 0 := by
  simp only [deriveSecret, ha, ↓reduceDIte]
  exact (isQueryBoundP_query_iff _ _ _).2 fun h => absurd h (hp _)

/-- `signTail` makes no `H_msg` query and no randomizer derivation: its public queries are
tweakable-hash queries and its secret values are derivations at secret-key addresses. -/
theorem isQueryBoundP_signTail (pkSeed : core.PkSeed) (R : core.Y)
    (digest : Bytes vp.params.m) :
    IsQueryBoundP (signTail core pkSeed R digest)
      (fun t => IsHmsgQuery core t ∨ IsRandQuery core t) 0 :=
  have htl := isQueryBoundP_tl core
    (p := fun t => IsHmsgQuery core t ∨ IsRandQuery core t) (fun _ _ _ h => h.elim id id) pkSeed
  have hs := isQueryBoundP_deriveSecret core
    (p := fun t => IsHmsgQuery core t ∨ IsRandQuery core t) fun _ h => h.elim id id
  have hf := fun a (_ : a.type ≤ 4) x => htl a [x]
  have hh := fun a (_ : a.type ≤ 4) l r => htl a [l, r]
  have htl := fun a (_ : a.type ≤ 4) => htl a
  isQueryBoundP_bind_zero _ _ (forsSignWithSecret_pred (IsQueryBoundP · _ 0)
    (isQueryBoundP_pure _ · 0) isQueryBoundP_bind_zero core hf hh hs _ _) fun _ =>
    isQueryBoundP_bind_zero _ _ (forsPkFromSigWith_pred (IsQueryBoundP · _ 0)
      (isQueryBoundP_pure _ · 0) isQueryBoundP_bind_zero core hf htl hh _ _ _) fun _ =>
      isQueryBoundP_bind_zero _ _ (GeneralHypertree.signFromPositionWithSecret_pred
        (IsQueryBoundP · _ 0) (isQueryBoundP_pure _ · 0) isQueryBoundP_bind_zero core hf htl hh
        hs _ _ _ _ _) fun _ => isQueryBoundP_pure _ _ _

variable [DecidableEq core.Y] (optRand : PublicKeyCore core → ProbComp core.Y)
  (pkSeed : core.PkSeed)

/-- Signing draws `opt_rand`, makes the randomizer derivation at `(opt_rand, M)`, then the
`H_msg` query at the derived randomizer, then `signTail`. -/
theorem deriveScheme_sign_eq (pk sk : PublicKeyCore core) (msg : List Byte) :
    (deriveScheme core optRand pkSeed).sign pk sk msg = (do
      let addrnd ← (optRand pk : ProbComp core.Y)
      let R ← (query (spec := deriveSpec core) (.inr (.inr (addrnd, msg))) :
        OracleComp (deriveSpec core) core.Y)
      let digest ← (PublicHash.hmsg core R sk.pkSeed sk.pkRoot msg :
        OracleComp (deriveSpec core) (Bytes vp.params.m))
      signTail core sk.pkSeed R digest) :=
  rfl

/-- Key generation makes no `H_msg` query and no randomizer derivation. -/
theorem isQueryBoundP_deriveScheme_keygen_hmsg_rand :
    IsQueryBoundP (deriveScheme core optRand pkSeed).keygen
      (fun t => IsHmsgQuery core t ∨ IsRandQuery core t) 0 :=
  isQueryBoundP_bind_zero _ _ (GeneralScheme.keygenInternalWithSecretM_pred
    (IsQueryBoundP · _ 0) (isQueryBoundP_pure _ · 0) isQueryBoundP_bind_zero core
    (isQueryBoundP_deriveSecret core fun _ h => h.elim id id) pkSeed
    fun a _ => isQueryBoundP_tl core (fun _ _ _ h => h.elim id id) pkSeed a) fun _ =>
    isQueryBoundP_pure _ _ _

/-- A signature makes at most one `H_msg` query. -/
theorem isQueryBoundP_deriveScheme_sign_hmsg (pk sk : PublicKeyCore core) (msg : List Byte) :
    IsQueryBoundP ((deriveScheme core optRand pkSeed).sign pk sk msg) (IsHmsgQuery core) 1 :=
  isQueryBoundP_bind (n := 0) (m := 1) (isQueryBoundP_liftM_withDerivations (fun _ => id) _)
    fun _ _ => isQueryBoundP_bind (n := 0) (m := 1) ((isQueryBoundP_query_iff _ _ _).2 False.elim)
      fun _ _ => isQueryBoundP_bind (n := 1) (m := 0)
        ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
        fun _ _ => (isQueryBoundP_signTail core _ _ _).of_imp fun _ => Or.inl

/-- A signature makes at most one randomizer derivation. -/
theorem isQueryBoundP_deriveScheme_sign_rand (pk sk : PublicKeyCore core) (msg : List Byte) :
    IsQueryBoundP ((deriveScheme core optRand pkSeed).sign pk sk msg) (IsRandQuery core) 1 :=
  isQueryBoundP_bind (n := 0) (m := 1) (isQueryBoundP_liftM_withDerivations (fun _ => id) _)
    fun _ _ => isQueryBoundP_bind (n := 1) (m := 0)
      ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
      fun _ _ => isQueryBoundP_bind (n := 0) (m := 0) ((isQueryBoundP_query_iff _ _ _).2 False.elim)
        fun _ _ => (isQueryBoundP_signTail core _ _ _).of_imp fun _ => Or.inr

/-- Verification makes `p`-queries only at its `H_msg` query when no tweakable-hash query is a
`p`-query: a budget `n` that covers that query covers verification. -/
private theorem isQueryBoundP_deriveScheme_verify_of {p : (deriveSpec core).Domain → Prop}
    [DecidablePred p] (hp : ∀ s k xs, ¬ p (.inl (.inr (.inl (.thash s k xs))))) {n : ℕ}
    (pk : PublicKeyCore core) (msg : List Byte) (sig : GeneralScheme.SignatureCore vp core)
    (hn : p (.inl (.inr (.inl (.hmsg sig.randomness pk.pkSeed pk.pkRoot msg)))) → 0 < n) :
    IsQueryBoundP ((deriveScheme core optRand pkSeed).verify pk msg sig) p n :=
  have htl := isQueryBoundP_tl core hp pk.pkSeed
  have hf := fun a (_ : a.type ≤ 4) x => htl a [x]
  have hh := fun a (_ : a.type ≤ 4) l r => htl a [l, r]
  have htl := fun a (_ : a.type ≤ 4) => htl a
  isQueryBoundP_bind (n := n) (m := 0) ((isQueryBoundP_query_iff _ _ _).2 hn) fun _ _ =>
    isQueryBoundP_bind_zero _ _ (forsPkFromSigWith_pred (IsQueryBoundP · _ 0)
      (isQueryBoundP_pure _ · 0) isQueryBoundP_bind_zero core hf htl hh _ _ _) fun _ =>
      isQueryBoundP_bind_zero _ _ (GeneralHypertree.recoverFromPositionWith_pred
        (IsQueryBoundP · _ 0) (isQueryBoundP_pure _ · 0) isQueryBoundP_bind_zero core hf htl hh
        _ _ _ _ _ _) fun _ => isQueryBoundP_pure _ _ _

/-- Verification makes at most one `H_msg` query. -/
theorem isQueryBoundP_deriveScheme_verify_hmsg (pk : PublicKeyCore core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp core) :
    IsQueryBoundP ((deriveScheme core optRand pkSeed).verify pk msg sig) (IsHmsgQuery core) 1 :=
  isQueryBoundP_deriveScheme_verify_of core optRand pkSeed (fun _ _ _ => id) pk msg sig
    fun _ => Nat.one_pos

/-- Verification makes no randomizer derivation. -/
theorem isQueryBoundP_deriveScheme_verify_rand (pk : PublicKeyCore core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp core) :
    IsQueryBoundP ((deriveScheme core optRand pkSeed).verify pk msg sig) (IsRandQuery core) 0 :=
  isQueryBoundP_deriveScheme_verify_of core optRand pkSeed (fun _ _ _ => id) pk msg sig
    False.elim

end Programs

variable [SampleableType core.Y] [DecidableEq core.Y]

/-- The secret-free scheme at public seed `pkSeed` with each algorithm run in its role: key
generation and signing in the signer's role, and verification in the forger's role. -/
@[expose] def roleScheme (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed) :
    SignatureAlg (OracleComp (roleSpec core)) (List Byte) (PublicKeyCore core)
      (PublicKeyCore core) (GeneralScheme.SignatureCore vp core) where
  keygen := simulateQ (roleImpl core .signer) (deriveScheme core optRand pkSeed).keygen
  sign pk sk msg :=
    simulateQ (roleImpl core .signer) ((deriveScheme core optRand pkSeed).sign pk sk msg)
  verify pk msg sig :=
    simulateQ (roleImpl core .forger) ((deriveScheme core optRand pkSeed).verify pk msg sig)

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf]

/-- The lifted forger makes no derivation query: each of its ambient queries is a uniform draw
or a hash query. -/
theorem allQueriesSatisfy_deriveAdversary_main {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) (pkSeed : core.PkSeed)
    (pk : PublicKeyCore core) :
    AllQueriesSatisfy ((deriveAdversary core adv pkSeed).main pk)
      (Sum.elim (fun t => t.isLeft = true) fun _ => True) :=
  allQueriesSatisfy_mapOracles (sigAlg' := deriveScheme core optRand pkSeed)
    ((hashSpec core).withDerivationsLift (DeriveQuery core) core.Y) adv
    (allowed := fun t => t.isLeft = true) (fun _ => (allQueriesSatisfy_query_iff _ _).2 rfl) pk

/-- The role-tagged secret-free experiment: the transcript experiment of `roleScheme` against
the lifted forger with its queries interpreted in the forger's role. -/
@[expose] noncomputable def roleExperiment {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) (pkSeed : core.PkSeed) :
    OracleComp (roleSpec core) (DeriveOutcome core) :=
  unforgeableTranscriptExperiment ((deriveAdversary core adv pkSeed).mapOracles
    (roleImpl core .forger) (sigAlg' := roleScheme core optRand pkSeed))

/-- Collapsing the two copies of the role-tagged experiment gives the transcript experiment of
`deriveScheme` against the lifted forger. -/
theorem simulateQ_collapseFwd_roleExperiment {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) (pkSeed : core.PkSeed) :
    simulateQ (SecretEncoding.collapseFwd (hashSpec core) (DeriveQuery core) core.Y)
        (roleExperiment core adv pkSeed) =
      unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed) := by
  have hsig : (roleScheme core optRand pkSeed).map
      (simulateQ' (SecretEncoding.collapseFwd (hashSpec core) (DeriveQuery core) core.Y)) =
        deriveScheme core optRand pkSeed := by
    ext <;> simp only [SignatureAlg.map, roleScheme, ← QueryImpl.simulateQ_compose,
      collapseFwd_comp_roleImpl, simulateQ_id']
  have key : ∀ (A : SignatureAlg (OracleComp (deriveSpec core)) (List Byte)
      (PublicKeyCore core) (PublicKeyCore core) (GeneralScheme.SignatureCore vp core))
      (_ : A = deriveScheme core optRand pkSeed) (f : PublicKeyCore core → _),
      unforgeableTranscriptExperiment (sigAlg := A) ⟨f⟩ =
        unforgeableTranscriptExperiment (sigAlg := deriveScheme core optRand pkSeed) ⟨f⟩ := by
    rintro A rfl f; rfl
  rw [roleExperiment, simulateQ_unforgeableTranscriptExperiment,
    UnforgeableAdversary.mapOracles_mapOracles, collapseFwd_comp_roleImpl]
  exact (key _ hsig _).trans (congrArg _ (congrArg UnforgeableAdversary.mk
    (UnforgeableAdversary.mapOracles_id'_main (sigAlg' := (roleScheme core optRand pkSeed).map
      (simulateQ' (SecretEncoding.collapseFwd (hashSpec core) (DeriveQuery core) core.Y))) _)))

/-! ## Per-class budgets -/

variable {e : core.SkSeed ≃ core.Y} {optRand : PublicKeyCore core → ProbComp core.Y}
  {pkSeedDist : ProbComp core.PkSeed}
  {adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)} {qh qs : ℕ}

/-- **Forger-side `H_msg` budget.** The role experiment makes at most `qh + 1` queries of class
`forger`: one per forger hash query and one for verification; key generation and signing run in
the signer's role and make none. -/
theorem isQueryBoundP_roleExperiment_forger (hadv : adv.RomQueryBound qh qs)
    (pkSeed : core.PkSeed) :
    IsQueryBoundP (roleExperiment core adv pkSeed)
      (fun t => AnswerTape.classOf (tapeClass core) t = some .forger) (qh + 1) := by
  have hS0 : ∀ t, IsQueryBoundP (roleImpl core .signer t)
      (fun t => AnswerTape.classOf (tapeClass core) t = some .forger) 0 := fun t =>
    (isQueryBoundP_roleImpl_iff core _ t).2 fun h =>
      absurd ((classOf_roleQuery_eq_some_iff core .signer .forger t).1 h).1 nofun
  rw [roleExperiment, deriveAdversary, UnforgeableAdversary.mapOracles_mapOracles]
  refine isQueryBoundP_unforgeableTranscriptExperiment_mapOracles_add _ (fun pk => (hadv pk).1)
    (fun t _ => ?_) (fun t ht => ?_) (isQueryBoundP_simulateQ_zero _ hS0) (fun _ _ _ h => h.elim)
    (fun _ _ _ _ => isQueryBoundP_simulateQ_zero _ hS0) fun pk msg sig =>
      isQueryBoundP_simulateQ_roleImpl core .forger
        (isQueryBoundP_deriveScheme_verify_hmsg core optRand pkSeed pk msg sig)
        fun t h => ((classOf_roleQuery_eq_some_iff core .forger .forger t).1 h).2
  · rw [roleImpl_comp_withDerivationsLift_apply]
    exact (isQueryBoundP_roleImpl_iff core _ _).2 fun _ => Nat.one_pos
  · rcases t with n | t
    · rw [roleImpl_comp_withDerivationsLift_apply]
      exact (isQueryBoundP_roleImpl_iff core _ _).2 nofun
    · exact (ht trivial).elim

/-- **Signer `H_msg` budget.** The role experiment makes at most `qs` queries of class `signer`,
one per signature: the forger and verification run in the forger's role and make none, and key
generation makes no `H_msg` query. -/
theorem isQueryBoundP_roleExperiment_signer (hadv : adv.RomQueryBound qh qs)
    (pkSeed : core.PkSeed) :
    IsQueryBoundP (roleExperiment core adv pkSeed)
      (fun t => AnswerTape.classOf (tapeClass core) t = some .signer) qs := by
  have hF0 : ∀ t, IsQueryBoundP (roleImpl core .forger t)
      (fun t => AnswerTape.classOf (tapeClass core) t = some .signer) 0 := fun t =>
    (isQueryBoundP_roleImpl_iff core _ t).2 fun h =>
      absurd ((classOf_roleQuery_eq_some_iff core .forger .signer t).1 h).1 nofun
  have hS : ∀ t, AnswerTape.classOf (tapeClass core) (roleQuery core .signer t) = some .signer →
      IsHmsgQuery core t := fun t h =>
    ((classOf_roleQuery_eq_some_iff core .signer .signer t).1 h).2
  rw [roleExperiment, deriveAdversary, UnforgeableAdversary.mapOracles_mapOracles]
  exact isQueryBoundP_unforgeableTranscriptExperiment_mapOracles_sign _ (fun pk => (hadv pk).2)
    (fun _ => trivial) (fun t => roleImpl_comp_withDerivationsLift_apply core _ t ▸ hF0 _)
    (isQueryBoundP_simulateQ_roleImpl core .signer
      (isQueryBoundP_deriveScheme_keygen_hmsg_rand core optRand pkSeed) fun t h => .inl (hS t h))
    (fun pk sk msg => isQueryBoundP_simulateQ_roleImpl core .signer
      (isQueryBoundP_deriveScheme_sign_hmsg core optRand pkSeed pk sk msg) hS)
    fun _ _ _ => isQueryBoundP_simulateQ_zero _ hF0

/-- **Randomizer budget.** The role experiment makes at most `qs` randomizer derivations, one
per signature, whether or not the derivation is cached: the forger, key generation and
verification make none. -/
theorem isQueryBoundP_roleExperiment_rand (hadv : adv.RomQueryBound qh qs)
    (pkSeed : core.PkSeed) :
    IsQueryBoundP (roleExperiment core adv pkSeed) (IsRoleRandQuery core) qs := by
  have hR (r : Role) (t) : IsRoleRandQuery core (roleQuery core r t) → IsRandQuery core t :=
    (isRoleRandQuery_roleQuery_iff core r t).1
  rw [roleExperiment, deriveAdversary, UnforgeableAdversary.mapOracles_mapOracles]
  exact isQueryBoundP_unforgeableTranscriptExperiment_mapOracles_sign _ (fun pk => (hadv pk).2)
    (fun _ => trivial)
    (fun t => roleImpl_comp_withDerivationsLift_apply core _ t ▸
      (isQueryBoundP_roleImpl_iff core _ _).2 fun h => (hR _ _ h).elim)
    (isQueryBoundP_simulateQ_roleImpl core .signer
      (isQueryBoundP_deriveScheme_keygen_hmsg_rand core optRand pkSeed)
      fun t h => .inr (hR _ t h))
    (fun pk sk msg => isQueryBoundP_simulateQ_roleImpl core .signer
      (isQueryBoundP_deriveScheme_sign_rand core optRand pkSeed pk sk msg) (hR _))
    fun pk msg sig => isQueryBoundP_simulateQ_roleImpl core .forger
      (isQueryBoundP_deriveScheme_verify_rand core optRand pkSeed pk msg sig) (hR _)

end SLHDSA.Security.Coverage
