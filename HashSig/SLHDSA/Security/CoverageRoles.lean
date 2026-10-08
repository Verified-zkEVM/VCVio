/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.AddressDiscipline
public import HashSig.SLHDSA.Security.SeedCoupling
public import VCVio.CryptoFoundations.SignatureAlg.Tagged
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

* *Tagging.* `roleF core` and `roleS core` send every query of `deriveSpec core` to the forger
  and signer copies. `roleScheme core optRand pkSeed` interprets key generation and signing
  through `roleS` and verification through `roleF`, so the verifier's `H_msg` query is on the
  forger copy, and `roleExperiment core adv pkSeed` is the transcript experiment of
  `roleScheme` against the forger interpreted through `roleF`. Collapsing the copies with
  `SecretEncoding.collapseFwd` gives the secret-free experiment back
  (`simulateQ_collapseFwd_roleExperiment`).
* *Tape classes.* `Cls` names three classes of queries of the joint interface: forger-copy
  `H_msg` (`F`), signer-copy `H_msg` (`S`) and every other query (`N`). `tau core` classifies,
  `ClsR core` gives the answer type of each class, and `range_eq_clsR` matches the two.
  `IsClsQuery core j` and `IsRoleRandQuery core` select the class-`j` queries and the randomizer
  derivations of the role-tagged interface; `IsHmsgQuery core` and `IsRandQuery core` select the
  `H_msg` queries and the randomizer derivations of `deriveSpec core`.
* *Query shapes of the honest programs.* Signing draws `opt_rand`, makes the randomizer
  derivation, then the `H_msg` query, then `signTail` (`deriveScheme_sign_eq`). The tail and key
  generation make no `H_msg` query and no randomizer derivation, verification makes at most one
  `H_msg` query and no randomizer derivation, and a signature makes at most one of each. These
  are instances of the address discipline of `HashSig.SLHDSA.AddressDiscipline`.
* *Per-class budgets.* For a forger with hash budget `qh` and signing budget `qs`
  (`UnforgeableAdversary.RomQueryBound`), the role experiment makes at most `qh + 1` class-`F`
  queries (`isQueryBoundP_roleExperiment_F`), at most `qs` class-`S` queries
  (`isQueryBoundP_roleExperiment_S`) and at most `qs` randomizer derivations
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
inductive Cls
  /-- An `H_msg` query on the forger copy. -/
  | F
  /-- An `H_msg` query on the signer copy. -/
  | S
  /-- Any other query. -/
  | N
  deriving DecidableEq

instance : Fintype Cls := ⟨{.F, .S, .N}, by rintro (_ | _ | _) <;> simp⟩

/-- The answer type of each tape class: a digest for the two `H_msg` classes, a node otherwise. -/
abbrev ClsR : Cls → Type
  | .F => Bytes vp.params.m
  | .S => Bytes vp.params.m
  | .N => core.Y

/-- Each tape class draws its answers from the global sampler of its answer type. -/
instance instSampleableTypeClsR [SampleableType core.Y] :
    (j : Cls) → SampleableType (ClsR core j)
  | .F | .S => inferInstanceAs (SampleableType (Bytes vp.params.m))
  | .N => inferInstanceAs (SampleableType core.Y)

/-- The class of a query of the duplicated joint interface: an `H_msg` query is class `F` on the
forger copy and class `S` on the signer copy; every other query is class `N`. -/
@[expose] def tau : (jointSpec core + jointSpec core).Domain → Cls
  | .inl (.inl (.inl (.hmsg _ _ _ _))) => .F
  | .inr (.inl (.inl (.hmsg _ _ _ _))) => .S
  | _ => .N

/-- Every query of the duplicated joint interface is answered in the answer type of its class. -/
theorem range_eq_clsR : ∀ t : (jointSpec core + jointSpec core).Domain,
    (jointSpec core + jointSpec core).Range t = ClsR core (tau core t) := by
  rintro (((t | t) | x) | ((t | t) | x)) <;> (try cases t) <;> rfl

/-- A query of the role-tagged interface on either copy, of tape class `j`. -/
@[expose] def IsClsQuery (j : Cls) : (roleSpec core).Domain → Prop
  | .inl _ => False
  | .inr t => tau core t = j

instance (j : Cls) : DecidablePred (IsClsQuery core j) := by
  rintro (n | t) <;> simp only [IsClsQuery] <;> infer_instance

/-- A randomizer derivation, on either copy of the role-tagged interface. -/
@[expose] def IsRoleRandQuery : (roleSpec core).Domain → Prop
  | .inr (.inl (.inr (.inr _))) | .inr (.inr (.inr (.inr _))) => True
  | _ => False

instance : DecidablePred (IsRoleRandQuery core) := by
  rintro (n | (((t | t) | (k | x)) | ((t | t) | (k | x)))) <;> simp only [IsRoleRandQuery] <;>
    infer_instance

/-! ## Roles -/

/-- The forger's role: every query of the secret-free interface goes to the forger copy, and a
uniform draw is forwarded. -/
@[expose] def roleF : QueryImpl (deriveSpec core) (OracleComp (roleSpec core))
  | .inl (.inl n) => liftM ((roleSpec core).query (.inl n))
  | .inl (.inr t) => liftM ((roleSpec core).query (.inr (.inl (.inl t))))
  | .inr x => liftM ((roleSpec core).query (.inr (.inl (.inr x))))

/-- The signer's role: every query of the secret-free interface goes to the signer copy, and a
uniform draw is forwarded. -/
@[expose] def roleS : QueryImpl (deriveSpec core) (OracleComp (roleSpec core))
  | .inl (.inl n) => liftM ((roleSpec core).query (.inl n))
  | .inl (.inr t) => liftM ((roleSpec core).query (.inr (.inr (.inl t))))
  | .inr x => liftM ((roleSpec core).query (.inr (.inr (.inr x))))

/-- The query of the role-tagged interface that `roleF` issues for a query `t`. -/
@[expose] def roleFQuery : (deriveSpec core).Domain → (roleSpec core).Domain
  | .inl (.inl n) => .inl n
  | .inl (.inr t) => .inr (.inl (.inl t))
  | .inr x => .inr (.inl (.inr x))

/-- The query of the role-tagged interface that `roleS` issues for a query `t`. -/
@[expose] def roleSQuery : (deriveSpec core).Domain → (roleSpec core).Domain
  | .inl (.inl n) => .inl n
  | .inl (.inr t) => .inr (.inr (.inl t))
  | .inr x => .inr (.inr (.inr x))

/-- The forger's role answers a query by one query, `roleFQuery core t`. -/
theorem isQueryBoundP_roleF_iff (t : (deriveSpec core).Domain) {q : (roleSpec core).Domain → Prop}
    [DecidablePred q] {n : ℕ} :
    IsQueryBoundP (roleF core t) q n ↔ (q (roleFQuery core t) → 0 < n) := by
  rcases t with ((n | t) | x) <;> exact isQueryBoundP_query_iff _ _ _

/-- The signer's role answers a query by one query, `roleSQuery core t`. -/
theorem isQueryBoundP_roleS_iff (t : (deriveSpec core).Domain) {q : (roleSpec core).Domain → Prop}
    [DecidablePred q] {n : ℕ} :
    IsQueryBoundP (roleS core t) q n ↔ (q (roleSQuery core t) → 0 < n) := by
  rcases t with ((n | t) | x) <;> exact isQueryBoundP_query_iff _ _ _

/-- Collapsing the copies undoes the forger's role. -/
theorem collapseFwd_comp_roleF :
    SecretEncoding.collapseFwd (hashSpec core) (DeriveQuery core) core.Y ∘ₛ roleF core =
      QueryImpl.id' (deriveSpec core) := by
  ext ((n | t) | x) <;> rfl

/-- Collapsing the copies undoes the signer's role. -/
theorem collapseFwd_comp_roleS :
    SecretEncoding.collapseFwd (hashSpec core) (DeriveQuery core) core.Y ∘ₛ roleS core =
      QueryImpl.id' (deriveSpec core) := by
  ext ((n | t) | x) <;> rfl

/-- `roleF` read through the lift of the forger's queries into the derivation world. -/
theorem roleF_comp_withDerivationsLift_apply (t : (unifSpec + hashSpec core).Domain) :
    (roleF core ∘ₛ (hashSpec core).withDerivationsLift (DeriveQuery core) core.Y) t =
      roleF core (.inl t) := by
  simp only [QueryImpl.apply_compose, OracleSpec.withDerivationsLift, simulateQ_spec_query]

/-- A query of the secret-free interface at which the role experiment charges a budget is
charged on the copy of its role: `roleF` and `roleS` answer the query by one query, and the
simulation spends one charged query on each `p`-query and none on any other. -/
theorem isQueryBoundP_simulateQ_roleF {α : Type} {oa : OracleComp (deriveSpec core) α}
    {p : (deriveSpec core).Domain → Prop} [DecidablePred p]
    {q : (roleSpec core).Domain → Prop} [DecidablePred q] {n : ℕ}
    (h : IsQueryBoundP oa p n) (hq : ∀ t, q (roleFQuery core t) → p t) :
    IsQueryBoundP (simulateQ (roleF core) oa) q n :=
  h.simulateQ_of_step (fun t _ => (isQueryBoundP_roleF_iff core t).2 fun _ => Nat.one_pos)
    fun t ht => (isQueryBoundP_roleF_iff core t).2 fun h => absurd (hq t h) ht

/-- The signer-role counterpart of `isQueryBoundP_simulateQ_roleF`. -/
theorem isQueryBoundP_simulateQ_roleS {α : Type} {oa : OracleComp (deriveSpec core) α}
    {p : (deriveSpec core).Domain → Prop} [DecidablePred p]
    {q : (roleSpec core).Domain → Prop} [DecidablePred q] {n : ℕ}
    (h : IsQueryBoundP oa p n) (hq : ∀ t, q (roleSQuery core t) → p t) :
    IsQueryBoundP (simulateQ (roleS core) oa) q n :=
  h.simulateQ_of_step (fun t _ => (isQueryBoundP_roleS_iff core t).2 fun _ => Nat.one_pos)
    fun t ht => (isQueryBoundP_roleS_iff core t).2 fun h => absurd (hq t h) ht

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

/-- The forger's role sends exactly the `H_msg` queries to class `F`. -/
theorem isClsQuery_F_roleFQuery_iff (t : (deriveSpec core).Domain) :
    IsClsQuery core .F (roleFQuery core t) ↔ IsHmsgQuery core t := by
  rcases t with ((n | ((t | t) | t)) | x) <;> (try cases t) <;>
    simp [IsClsQuery, roleFQuery, tau, IsHmsgQuery]

/-- The signer's role sends exactly the `H_msg` queries to class `S`. -/
theorem isClsQuery_S_roleSQuery_iff (t : (deriveSpec core).Domain) :
    IsClsQuery core .S (roleSQuery core t) ↔ IsHmsgQuery core t := by
  rcases t with ((n | ((t | t) | t)) | x) <;> (try cases t) <;>
    simp [IsClsQuery, roleSQuery, tau, IsHmsgQuery]

/-- The forger's role sends no query to class `S`. -/
theorem not_isClsQuery_S_roleFQuery (t : (deriveSpec core).Domain) :
    ¬ IsClsQuery core .S (roleFQuery core t) := by
  rcases t with ((n | ((t | t) | t)) | x) <;> (try cases t) <;> simp [IsClsQuery, roleFQuery, tau]

/-- The signer's role sends no query to class `F`. -/
theorem not_isClsQuery_F_roleSQuery (t : (deriveSpec core).Domain) :
    ¬ IsClsQuery core .F (roleSQuery core t) := by
  rcases t with ((n | ((t | t) | t)) | x) <;> (try cases t) <;> simp [IsClsQuery, roleSQuery, tau]

/-- The forger's role sends exactly the randomizer derivations to randomizer derivations. -/
theorem isRoleRandQuery_roleFQuery_iff (t : (deriveSpec core).Domain) :
    IsRoleRandQuery core (roleFQuery core t) ↔ IsRandQuery core t := by
  rcases t with ((n | t) | (k | x)) <;> simp [IsRoleRandQuery, roleFQuery, IsRandQuery]

/-- The signer's role sends exactly the randomizer derivations to randomizer derivations. -/
theorem isRoleRandQuery_roleSQuery_iff (t : (deriveSpec core).Domain) :
    IsRoleRandQuery core (roleSQuery core t) ↔ IsRandQuery core t := by
  rcases t with ((n | t) | (k | x)) <;> simp [IsRoleRandQuery, roleSQuery, IsRandQuery]

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

/-- Internal signing with derivation-backed secrets is the `H_msg` query followed by
`signTail`. -/
theorem signInternalWithSecretRandomizerM_deriveSecret_eq (msg : List Byte)
    (pkSeed : core.PkSeed) (pkRoot R : core.Y) :
    GeneralScheme.signInternalWithSecretRandomizerM core (deriveSecret core) msg pkSeed pkRoot R =
      (PublicHash.hmsg core R pkSeed pkRoot msg : OracleComp (deriveSpec core) _) >>=
        signTail core pkSeed R :=
  rfl

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

/-- The secret-free scheme at public seed `pkSeed` with each algorithm tagged by its role: key
generation and signing play the signer, and verification plays the forger. -/
@[expose] def roleScheme (optRand : PublicKeyCore core → ProbComp core.Y) (pkSeed : core.PkSeed) :
    SignatureAlg (OracleComp (roleSpec core)) (List Byte) (PublicKeyCore core)
      (PublicKeyCore core) (GeneralScheme.SignatureCore vp core) where
  keygen := simulateQ (roleS core) (deriveScheme core optRand pkSeed).keygen
  sign pk sk msg := simulateQ (roleS core) ((deriveScheme core optRand pkSeed).sign pk sk msg)
  verify pk msg sig :=
    simulateQ (roleF core) ((deriveScheme core optRand pkSeed).verify pk msg sig)

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf]

/-- The role-tagged secret-free experiment: the transcript experiment of `roleScheme` against
the lifted forger with its queries interpreted through the forger's role. -/
@[expose] noncomputable def roleExperiment {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)) (pkSeed : core.PkSeed) :
    OracleComp (roleSpec core) (DeriveOutcome core) :=
  unforgeableTranscriptExperiment ((deriveAdversary core adv pkSeed).mapOracles (roleF core)
    (sigAlg' := roleScheme core optRand pkSeed))

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
      collapseFwd_comp_roleF, collapseFwd_comp_roleS, simulateQ_id']
  have key : ∀ (A : SignatureAlg (OracleComp (deriveSpec core)) (List Byte)
      (PublicKeyCore core) (PublicKeyCore core) (GeneralScheme.SignatureCore vp core))
      (_ : A = deriveScheme core optRand pkSeed) (f : PublicKeyCore core → _),
      unforgeableTranscriptExperiment (sigAlg := A) ⟨f⟩ =
        unforgeableTranscriptExperiment (sigAlg := deriveScheme core optRand pkSeed) ⟨f⟩ := by
    rintro A rfl f; rfl
  rw [roleExperiment, simulateQ_unforgeableTranscriptExperiment,
    UnforgeableAdversary.mapOracles_mapOracles, collapseFwd_comp_roleF]
  exact (key _ hsig _).trans (congrArg _ (congrArg UnforgeableAdversary.mk
    (UnforgeableAdversary.mapOracles_id'_main _)))

/-! ## Per-class budgets -/

variable {e : core.SkSeed ≃ core.Y} {optRand : PublicKeyCore core → ProbComp core.Y}
  {pkSeedDist : ProbComp core.PkSeed}
  {adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)} {qh qs : ℕ}

/-- **Forger-side `H_msg` budget.** The role experiment makes at most `qh + 1` class-`F` queries:
one per forger hash query and one for verification; key generation and signing play the signer
and make none. -/
theorem isQueryBoundP_roleExperiment_F (hadv : adv.RomQueryBound qh qs)
    (pkSeed : core.PkSeed) :
    IsQueryBoundP (roleExperiment core adv pkSeed) (IsClsQuery core .F) (qh + 1) := by
  have hS0 : ∀ t, IsQueryBoundP (roleS core t) (IsClsQuery core .F) 0 := fun t =>
    (isQueryBoundP_roleS_iff core t).2 fun h => absurd h (not_isClsQuery_F_roleSQuery core t)
  rw [roleExperiment, deriveAdversary, UnforgeableAdversary.mapOracles_mapOracles]
  refine isQueryBoundP_unforgeableTranscriptExperiment_mapOracles_add _ (fun pk => (hadv pk).1)
    (fun t _ => ?_) (fun t ht => ?_) (isQueryBoundP_simulateQ_zero _ hS0) (fun _ _ _ h => h.elim)
    (fun _ _ _ _ => isQueryBoundP_simulateQ_zero _ hS0) fun pk msg sig =>
      isQueryBoundP_simulateQ_roleF core
        (isQueryBoundP_deriveScheme_verify_hmsg core optRand pkSeed pk msg sig)
        fun t => (isClsQuery_F_roleFQuery_iff core t).1
  · rw [roleF_comp_withDerivationsLift_apply]
    exact (isQueryBoundP_roleF_iff core _).2 fun _ => Nat.one_pos
  · rcases t with n | t
    · rw [roleF_comp_withDerivationsLift_apply]
      exact (isQueryBoundP_roleF_iff core _).2 False.elim
    · exact (ht trivial).elim

/-- **Signer `H_msg` budget.** The role experiment makes at most `qs` class-`S` queries, one per
signature: the forger and verification play the forger and make none, and key generation makes
no `H_msg` query. -/
theorem isQueryBoundP_roleExperiment_S (hadv : adv.RomQueryBound qh qs)
    (pkSeed : core.PkSeed) :
    IsQueryBoundP (roleExperiment core adv pkSeed) (IsClsQuery core .S) qs := by
  have hF0 : ∀ t, IsQueryBoundP (roleF core t) (IsClsQuery core .S) 0 := fun t =>
    (isQueryBoundP_roleF_iff core t).2 fun h => absurd h (not_isClsQuery_S_roleFQuery core t)
  rw [roleExperiment, deriveAdversary, UnforgeableAdversary.mapOracles_mapOracles]
  exact isQueryBoundP_unforgeableTranscriptExperiment_mapOracles_sign _ (fun pk => (hadv pk).2)
    (fun _ => trivial) (fun t => roleF_comp_withDerivationsLift_apply core t ▸ hF0 _)
    (isQueryBoundP_simulateQ_roleS core
      (isQueryBoundP_deriveScheme_keygen_hmsg_rand core optRand pkSeed)
      fun t ht => .inl ((isClsQuery_S_roleSQuery_iff core t).1 ht))
    (fun pk sk msg => isQueryBoundP_simulateQ_roleS core
      (isQueryBoundP_deriveScheme_sign_hmsg core optRand pkSeed pk sk msg)
      fun t => (isClsQuery_S_roleSQuery_iff core t).1)
    fun _ _ _ => isQueryBoundP_simulateQ_zero _ hF0

/-- **Randomizer budget.** The role experiment makes at most `qs` randomizer derivations, one
per signature, whether or not the derivation is cached: the forger, key generation and
verification make none. -/
theorem isQueryBoundP_roleExperiment_rand (hadv : adv.RomQueryBound qh qs)
    (pkSeed : core.PkSeed) :
    IsQueryBoundP (roleExperiment core adv pkSeed) (IsRoleRandQuery core) qs := by
  rw [roleExperiment, deriveAdversary, UnforgeableAdversary.mapOracles_mapOracles]
  exact isQueryBoundP_unforgeableTranscriptExperiment_mapOracles_sign _ (fun pk => (hadv pk).2)
    (fun _ => trivial)
    (fun t => roleF_comp_withDerivationsLift_apply core t ▸ (isQueryBoundP_roleF_iff core _).2
      fun h => ((isRoleRandQuery_roleFQuery_iff core _).1 h).elim)
    (isQueryBoundP_simulateQ_roleS core
      (isQueryBoundP_deriveScheme_keygen_hmsg_rand core optRand pkSeed)
      fun t ht => .inr ((isRoleRandQuery_roleSQuery_iff core t).1 ht))
    (fun pk sk msg => isQueryBoundP_simulateQ_roleS core
      (isQueryBoundP_deriveScheme_sign_rand core optRand pkSeed pk sk msg)
      fun t => (isRoleRandQuery_roleSQuery_iff core t).1)
    fun pk msg sig => isQueryBoundP_simulateQ_roleF core
      (isQueryBoundP_deriveScheme_verify_rand core optRand pkSeed pk msg sig)
      fun t => (isRoleRandQuery_roleFQuery_iff core t).1

end SLHDSA.Security.Coverage
