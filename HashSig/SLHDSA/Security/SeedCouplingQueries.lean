/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.SeedCoupling
public import HashSig.SLHDSA.AddressDiscipline

/-!
# Derivable public queries of the secret-free run of SLH-DSA

In the secret-free run of SLH-DSA (`HashSig.SLHDSA.Security.SeedCoupling`) every secret value
and every message randomizer is a derivation query, answered under secret seeds `s` by the
public query `(secretEncoding core e pkSeed).enc s x`. Every such public query is a
*derivable public query* (`IsDerivablePublicQuery core pkSeed`, `isDerivablePublicQuery_enc`).
This module bounds the derivable public queries of the transcript experiment of `deriveScheme`
against a lifted forger by the forger's hash budget.

* Under key separation (`CorePrimitives.KeySeparated core`, from
  `HashSig.SLHDSA.AddressDiscipline`: no address of type at most `4` shares its oracle key with a
  secret-key address; the bundles that satisfy it are in `HashSig.SLHDSA.Security.KeySeparation`),
  key generation, signing and verification of `deriveScheme` make no derivable public query
  (`isQueryBoundP_deriveScheme_keygen`, `isQueryBoundP_deriveScheme_sign`,
  `isQueryBoundP_deriveScheme_verify`). They are instances of the address discipline of
  `HashSig.SLHDSA.AddressDiscipline`: a tweakable-hash query at an address of type at most `4` is
  not derivable under key separation, `H_msg` is never derivable, and the secret values and the
  randomizer are derivation queries.
* `isQueryBoundP_unforgeableTranscriptExperiment_deriveAdversary`: a forger with hash budget `qh`
  (`UnforgeableAdversary.RomQueryBound`) makes the transcript experiment of `deriveScheme`
  against `deriveAdversary core adv pkSeed` issue at most `qh` derivable public queries. It is
  an instance of `SignatureAlg.isQueryBoundP_unforgeableTranscriptExperiment_mapOracles`.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA

namespace Security

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-! ## Derivable public queries -/

/-- The public queries of `deriveSpec core` that can encode a derivation at public seed `pkSeed`:
every tweakable-hash query at `pkSeed` whose key is the oracle key of a secret-key address,
whatever its input, and every `PRF_msg` query. -/
@[expose] def IsDerivablePublicQuery (pkSeed : core.PkSeed) : (deriveSpec core).Domain → Prop
  | .inl (.inr (.inl (.thash s k _))) =>
      s = pkSeed ∧ ∃ a : Adrs, a.IsSecretKey ∧ core.adrsToKey a = k
  | .inl (.inr (.inr _)) => True
  | _ => False

/-- Membership of a key in the keys of secret-key addresses is decided classically. -/
noncomputable instance instDecidablePredIsDerivablePublicQuery (pkSeed : core.PkSeed) :
    DecidablePred (IsDerivablePublicQuery core pkSeed) :=
  fun _ => Classical.dec _

/-- Every encoding of a derivation at public seed `pkSeed` is a derivable public query. -/
theorem isDerivablePublicQuery_enc (e : core.SkSeed ≃ core.Y) (pkSeed : core.PkSeed)
    (s : core.SkSeed × core.SkPrf) (x : DeriveQuery core) :
    IsDerivablePublicQuery core pkSeed (.inl (.inr ((secretEncoding core e pkSeed).enc s x))) := by
  rcases x with k | ⟨o, msg⟩
  · exact ⟨rfl, k.2⟩
  · trivial

/-! ## The secret-free scheme and its experiment -/

variable {core}

/-- Under key separation, a tweakable-hash query at an address of type at most `4` is not
derivable. -/
private theorem isQueryBoundP_publicHash_tl (hsep : core.KeySeparated) (pkSeed s : core.PkSeed)
    (a : Adrs) (ha : a.type ≤ 4) (xs : List core.Y) :
    IsQueryBoundP (PublicHash.tl core s a xs : OracleComp (deriveSpec core) core.Y)
      (IsDerivablePublicQuery core pkSeed) 0 :=
  (isQueryBoundP_query_iff _ _ _).2 fun ⟨_, b, hb, hk⟩ => (hsep b a hb ha hk).elim

/-- An `H_msg` query is not derivable. -/
private theorem isQueryBoundP_publicHash_hmsg (pkSeed : core.PkSeed) (r : core.Y)
    (s : core.PkSeed) (pkRoot : core.Y) (msg : List Byte) :
    IsQueryBoundP (PublicHash.hmsg core r s pkRoot msg :
      OracleComp (deriveSpec core) (Bytes vp.params.m)) (IsDerivablePublicQuery core pkSeed) 0 :=
  (isQueryBoundP_query_iff _ _ _).2 False.elim

variable [SampleableType core.Y]

/-- At a secret-key address the derivation-backed secret provider makes a derivation query, which
is not a derivable public query. -/
private theorem isQueryBoundP_deriveSecret (pkSeed : core.PkSeed) (a : Adrs) (ha : a.IsSecretKey) :
    IsQueryBoundP (deriveSecret core a) (IsDerivablePublicQuery core pkSeed) 0 := by
  simp only [deriveSecret, ha, ↓reduceDIte]
  exact (isQueryBoundP_query_iff _ _ _).2 False.elim

variable [DecidableEq core.Y] (hsep : core.KeySeparated) (pkSeed : core.PkSeed)
include hsep

section Programs

variable (optRand : PublicKeyCore core → ProbComp core.Y)

/-- Key generation of `deriveScheme` makes no derivable public query. -/
theorem isQueryBoundP_deriveScheme_keygen :
    IsQueryBoundP (deriveScheme core optRand pkSeed).keygen
      (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_bind_zero _ _ (GeneralScheme.keygenInternalWithSecretM_pred
    (IsQueryBoundP · (IsDerivablePublicQuery core pkSeed) 0) (isQueryBoundP_pure _ · 0)
    isQueryBoundP_bind_zero core (isQueryBoundP_deriveSecret pkSeed) pkSeed
    (isQueryBoundP_publicHash_tl hsep pkSeed pkSeed)) fun _ => isQueryBoundP_pure _ _ _

/-- Signing with `deriveScheme` makes no derivable public query: the randomizer is a derivation
query, every secret value a derivation query, and every public query an `H_msg` query or a
tweakable-hash query at an address of type at most `4`. -/
theorem isQueryBoundP_deriveScheme_sign (pk sk : PublicKeyCore core) (msg : List Byte) :
    IsQueryBoundP ((deriveScheme core optRand pkSeed).sign pk sk msg)
      (IsDerivablePublicQuery core pkSeed) 0 :=
  isQueryBoundP_bind_zero _ _ (isQueryBoundP_liftM_withDerivations (fun _ => id) _) fun _ =>
    isQueryBoundP_bind_zero _ _ ((isQueryBoundP_query_iff _ _ _).2 False.elim) fun _ =>
      GeneralScheme.signInternalWithSecretRandomizerM_pred
        (IsQueryBoundP · (IsDerivablePublicQuery core pkSeed) 0) (isQueryBoundP_pure _ · 0)
        isQueryBoundP_bind_zero core (isQueryBoundP_deriveSecret pkSeed) _ _ _ _
        (isQueryBoundP_publicHash_tl hsep pkSeed _) (isQueryBoundP_publicHash_hmsg pkSeed _ _ _ _)

/-- Verification with `deriveScheme` makes no derivable public query. -/
theorem isQueryBoundP_deriveScheme_verify (pk : PublicKeyCore core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp core) :
    IsQueryBoundP ((deriveScheme core optRand pkSeed).verify pk msg sig)
      (IsDerivablePublicQuery core pkSeed) 0 :=
  GeneralScheme.verifyInternalM_pred (IsQueryBoundP · (IsDerivablePublicQuery core pkSeed) 0)
    (isQueryBoundP_pure _ · 0) isQueryBoundP_bind_zero core msg sig pk
    (isQueryBoundP_publicHash_tl hsep pkSeed _) (isQueryBoundP_publicHash_hmsg pkSeed _ _ _ _)

end Programs

/-- **Every derivable public query of the secret-free experiment is a forger hash query.** If the
forger makes at most `qh` hash queries, the transcript experiment of `deriveScheme` against the
lifted forger makes at most `qh` derivable public queries: the lift spends one derivable public
query on a hash query and none on a sampling query, and key generation, signing and verification
make none. -/
theorem isQueryBoundP_unforgeableTranscriptExperiment_deriveAdversary
    [SampleableType core.SkSeed] [SampleableType core.SkPrf] {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    {adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)} {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    IsQueryBoundP (unforgeableTranscriptExperiment (deriveAdversary core adv pkSeed))
      (IsDerivablePublicQuery core pkSeed) qh :=
  isQueryBoundP_unforgeableTranscriptExperiment_mapOracles _ (fun pk => (hadv pk).1)
    (fun _ _ => (isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
    (fun | .inl _, _ => (isQueryBoundP_query_iff _ _ _).2 False.elim
         | .inr _, ht => (ht trivial).elim)
    (isQueryBoundP_deriveScheme_keygen hsep pkSeed optRand)
    (isQueryBoundP_deriveScheme_sign hsep pkSeed optRand)
    (isQueryBoundP_deriveScheme_verify hsep pkSeed optRand)

end Security

end SLHDSA
