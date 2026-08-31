/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Security.Notions
public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# SLH-DSA Security Oracle Surface

Separate dependent query languages for the adversary-visible interface and the complete honest
execution trace.  The specifications are indexed by the attacked public key, so `F`, `H`,
`T_l`, `PRF`, and `H_msg` are interpreted with that key's `PK.seed` and `PK.root`; there is no
independent public-seed theorem parameter.  In particular, the public language has no constructor
for `PRF` or `PRF_msg`, so secrecy is enforced by the type rather than a zero-query hypothesis.

`SigningBound` and `HashQueryBound` are structural predicates on the actual adversary program.
They use `OracleComp.IsQueryBoundP` and therefore constrain every branch rather than merely
appearing as natural numbers in a numerical loss.  The attacked signature scheme is an explicit
interface parameter: this architecture does not silently instantiate the repository's transitional
single-layer construction when `p.d > 1`.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SLHDSA.Security

/-- A generated SLH-DSA key pair with the public material shared by both views. -/
structure GeneratedKeyPair {p : Params} (prims : Primitives p) where
  publicKey : PublicKeyCore prims.core
  secretKey : SecretKeyCore prims.core
  seed_eq : secretKey.pkSeed = publicKey.pkSeed
  root_eq : secretKey.pkRoot = publicKey.pkRoot

namespace GeneratedKeyPair

/-- The public seed owned by this generated key pair. -/
def publicSeed {p : Params} {prims : Primitives p} (keys : GeneratedKeyPair prims) : prims.PkSeed :=
  keys.publicKey.pkSeed

@[simp]
theorem secretKey_pkSeed {p : Params} {prims : Primitives p}
    (keys : GeneratedKeyPair prims) : keys.secretKey.pkSeed = keys.publicSeed :=
  keys.seed_eq

@[simp]
theorem secretKey_pkRoot {p : Params} {prims : Primitives p}
    (keys : GeneratedKeyPair prims) : keys.secretKey.pkRoot = keys.publicKey.pkRoot :=
  keys.root_eq

end GeneratedKeyPair

/-- An abstract signature-scheme experiment boundary.  The fields share one carrier, but this bare
bundle deliberately supplies no refinement or correctness law coupling key generation, signing,
verification, and the randomizer projection to the general SLH-DSA construction.  That construction
witness remains a later S08/S09 obligation. -/
structure SchemeInterface {p : Params} (prims : Primitives p) where
  Signature : Type
  randomizer : Signature → prims.Y
  keygen : ProbComp (GeneratedKeyPair prims)
  sign : SecretKeyCore prims.core → MessageInput → ProbComp Signature
  verify : PublicKeyCore prims.core → MessageInput → Signature → Bool

/-! ## Named queries -/

/-- The eight construction roles whose static target families occur in the repaired theorem.
Keeping the role in the trace prevents, for example, a FORS `F` call from being accepted as a
WOTS+ `F` target merely because both use the same primitive. -/
inductive ConstructionRole where
  | forsF
  | forsH
  | forsTl
  | wotsFUd
  | wotsFTcr
  | wotsFPre
  | wotsTl
  | xmssH
deriving Repr, DecidableEq

instance : Fintype ConstructionRole where
  elems := {.forsF, .forsH, .forsTl, .wotsFUd, .wotsFTcr, .wotsFPre, .wotsTl, .xmssH}
  complete role := by cases role <;> simp

@[simp]
theorem constructionRole_card : Fintype.card ConstructionRole = 8 := by decide

/-- Whether a public primitive call came from a particular honest-construction role or directly
from the adversary-facing collection interface.  Address-separation obligations inspect this
tag, while target provenance additionally inspects the construction role. -/
inductive QueryOrigin where
  | construction (role : ConstructionRole)
  | adversary
deriving Repr, DecidableEq

/-- The complete classical oracle trace vocabulary for an execution under public key `pk`.
`pk` is a phantom index: primitive query constructors do not accept a second public seed. -/
inductive Query {p : Params} (prims : Primitives p) (scheme : SchemeInterface prims)
    (_pk : PublicKeyCore prims.core) where
  | sign (request : MessageInput)
  | prf (secretSeed : prims.SkSeed) (address : Adrs)
  | prfMsg (secretPrf : prims.SkPrf) (optionalRandomness : prims.Y)
      (request : MessageInput)
  | f (origin : QueryOrigin) (address : Adrs) (input : prims.Y)
  | h (origin : QueryOrigin) (address : Adrs) (left right : prims.Y)
  | tlFors (origin : QueryOrigin) (address : Adrs) (inputs : Vector prims.Y p.k)
  | tlWots (origin : QueryOrigin) (address : Adrs) (inputs : Vector prims.Y p.len)
  | hmsg (origin : QueryOrigin) (randomizer : prims.Y) (request : MessageInput)

/-- Result family for the named SLH-DSA execution queries. -/
@[reducible] def oracleSpec {p : Params} (prims : Primitives p)
    (scheme : SchemeInterface prims) (pk : PublicKeyCore prims.core) :
    OracleSpec (Query prims scheme pk) :=
  OracleSpec.ofFn fun
    | .sign _ => scheme.Signature
    | .prf _ _ => prims.Y
    | .prfMsg _ _ _ => prims.Y
    | .f _ _ _ => prims.Y
    | .h _ _ _ _ => prims.Y
    | .tlFors _ _ _ => prims.Y
    | .tlWots _ _ _ => prims.Y
    | .hmsg _ _ _ => Bytes p.m

/-- The adversary-visible classical interface.  Secret-key primitive roles are intentionally
absent.  Signing is visible as a single query; a later implementation refinement exposes the
honest signer's internal primitive trace without changing this public type. -/
inductive AdversaryQuery {p : Params} (prims : Primitives p) (scheme : SchemeInterface prims)
    (_pk : PublicKeyCore prims.core) where
  | sign (request : MessageInput)
  | f (address : Adrs) (input : prims.Y)
  | h (address : Adrs) (left right : prims.Y)
  | tlFors (address : Adrs) (inputs : Vector prims.Y p.k)
  | tlWots (address : Adrs) (inputs : Vector prims.Y p.len)
  | hmsg (randomizer : prims.Y) (request : MessageInput)

/-- Result family for adversary-visible queries. -/
@[reducible] def adversaryOracleSpec {p : Params} (prims : Primitives p)
    (scheme : SchemeInterface prims) (pk : PublicKeyCore prims.core) :
    OracleSpec (AdversaryQuery prims scheme pk) :=
  OracleSpec.ofFn fun
    | .sign _ => scheme.Signature
    | .f _ _ => prims.Y
    | .h _ _ _ => prims.Y
    | .tlFors _ _ => prims.Y
    | .tlWots _ _ => prims.Y
    | .hmsg _ _ => Bytes p.m

/-- Embed the public interface into the complete execution trace.  This operation introduces no
secret query: it only relabels each public constructor with its execution-trace counterpart. -/
def adversaryQueryImpl {p : Params} (prims : Primitives p) (scheme : SchemeInterface prims)
    (pk : PublicKeyCore prims.core) :
    QueryImpl (adversaryOracleSpec prims scheme pk) (OracleComp (oracleSpec prims scheme pk))
  | .sign request => liftM ((oracleSpec prims scheme pk).query (.sign request))
  | .f address input => liftM ((oracleSpec prims scheme pk).query (.f .adversary address input))
  | .h address left right =>
      liftM ((oracleSpec prims scheme pk).query (.h .adversary address left right))
  | .tlFors address inputs =>
      liftM ((oracleSpec prims scheme pk).query (.tlFors .adversary address inputs))
  | .tlWots address inputs =>
      liftM ((oracleSpec prims scheme pk).query (.tlWots .adversary address inputs))
  | .hmsg randomizer request =>
      liftM ((oracleSpec prims scheme pk).query (.hmsg .adversary randomizer request))

/-- Exactly the public signing-query variant. -/
def isSigningQuery {p : Params} {prims : Primitives p} {scheme : SchemeInterface prims}
    {pk : PublicKeyCore prims.core} : AdversaryQuery prims scheme pk → Prop
  | .sign _ => True
  | _ => False

instance {p : Params} {prims : Primitives p} {scheme : SchemeInterface prims}
    {pk : PublicKeyCore prims.core} :
    DecidablePred (isSigningQuery (prims := prims) (scheme := scheme) (pk := pk)) := fun query => by
  cases query <;> simp only [isSigningQuery] <;> infer_instance

/-- Public hash-family queries counted by the explicit `qH` accounting convention.  It
counts explicit `F`, `H`, both arities of `T_l`, and `H_msg` calls made by the adversary.  The
repaired EasyCrypt master inequality has no extra additive `qH` loss. -/
def isHashQuery {p : Params} {prims : Primitives p} {scheme : SchemeInterface prims}
    {pk : PublicKeyCore prims.core} : AdversaryQuery prims scheme pk → Prop
  | .f _ _ | .h _ _ _ | .tlFors _ _ | .tlWots _ _ | .hmsg _ _ => True
  | _ => False

instance {p : Params} {prims : Primitives p} {scheme : SchemeInterface prims}
    {pk : PublicKeyCore prims.core} :
    DecidablePred (isHashQuery (prims := prims) (scheme := scheme) (pk := pk)) := fun query => by
  cases query <;> simp only [isHashQuery] <;> infer_instance

/-! ## Seed-coupled interpretation -/

/-- Interpret every primitive query using the public seed/root in `keys`.  `encode` is the
future external-API encoding boundary and `sign` is the honest signing implementation; neither
can substitute a different public seed in a primitive call. -/
def queryImpl {p : Params} {prims : Primitives p} (scheme : SchemeInterface prims)
    (keys : GeneratedKeyPair prims) (encode : MessageInput → List Byte) :
    QueryImpl (oracleSpec prims scheme keys.publicKey) ProbComp
  | .sign request => scheme.sign keys.secretKey request
  | .prf secretSeed address => pure (prims.PRF keys.publicSeed secretSeed address)
  | .prfMsg secretPrf optionalRandomness request =>
      pure (prims.PRFmsg secretPrf optionalRandomness (encode request))
  | .f _ address input => pure (prims.F keys.publicSeed address input)
  | .h _ address left right => pure (prims.H keys.publicSeed address left right)
  | .tlFors _ address inputs => pure (prims.Tl keys.publicSeed address inputs.toList)
  | .tlWots _ address inputs => pure (prims.Tl keys.publicSeed address inputs.toList)
  | .hmsg _ randomizer request =>
      pure (prims.Hmsg randomizer keys.publicSeed keys.publicKey.pkRoot (encode request))

/-! ## Adversaries and actual query predicates -/

/-- A classical adversary against the seed-indexed public oracle interface. -/
structure ClassicalAdversary {p : Params} (prims : Primitives p)
    (scheme : SchemeInterface prims) where
  main (pk : PublicKeyCore prims.core) :
    OracleComp (adversaryOracleSpec prims scheme pk) (MessageInput × scheme.Signature)

/-- Pathwise signing-query bound on an actual adversary computation. -/
def SigningBound {p : Params} {prims : Primitives p} {scheme : SchemeInterface prims}
    {pk : PublicKeyCore prims.core} {α : Type}
    (program : OracleComp (adversaryOracleSpec prims scheme pk) α) (qS : ℕ) : Prop :=
  program.IsQueryBoundP isSigningQuery qS

/-- Pathwise public-hash-query bound on an actual adversary computation. -/
def HashQueryBound {p : Params} {prims : Primitives p} {scheme : SchemeInterface prims}
    {pk : PublicKeyCore prims.core} {α : Type}
    (program : OracleComp (adversaryOracleSpec prims scheme pk) α) (qH : ℕ) : Prop :=
  program.IsQueryBoundP isHashQuery qH

/-- The complete `qS`/`qH` contract, quantified over every public key passed to the adversary. -/
def AdversaryBounds {p : Params} {prims : Primitives p}
    {scheme : SchemeInterface prims} (adversary : ClassicalAdversary prims scheme)
    (qS qH : ℕ) : Prop :=
  ∀ pk, SigningBound (adversary.main pk) qS ∧
    HashQueryBound (adversary.main pk) qH

/-! ## Zero-budget regression lemmas -/

@[simp]
theorem signingBound_query_iff {p : Params} {prims : Primitives p}
    (scheme : SchemeInterface prims) (pk : PublicKeyCore prims.core)
    (request : MessageInput) (qS : ℕ) :
    SigningBound
      (liftM ((adversaryOracleSpec prims scheme pk).query (.sign request)) :
        OracleComp (adversaryOracleSpec prims scheme pk) scheme.Signature) qS ↔ 0 < qS := by
  simp [SigningBound, isSigningQuery, OracleComp.isQueryBoundP_query_iff]

@[simp]
theorem hashQueryBound_f_iff {p : Params} {prims : Primitives p}
    (scheme : SchemeInterface prims) (pk : PublicKeyCore prims.core)
    (address : Adrs) (input : prims.Y) (qH : ℕ) :
    HashQueryBound
      (liftM ((adversaryOracleSpec prims scheme pk).query (.f address input)) :
        OracleComp (adversaryOracleSpec prims scheme pk) prims.Y) qH ↔ 0 < qH := by
  simp [HashQueryBound, isHashQuery, OracleComp.isQueryBoundP_query_iff]

theorem not_signingBound_zero {p : Params} {prims : Primitives p}
    (scheme : SchemeInterface prims) (pk : PublicKeyCore prims.core)
    (request : MessageInput) :
    ¬ SigningBound
      (liftM ((adversaryOracleSpec prims scheme pk).query (.sign request)) :
        OracleComp (adversaryOracleSpec prims scheme pk) scheme.Signature) 0 := by
  simp

theorem not_hashQueryBound_f_zero {p : Params} {prims : Primitives p}
    (scheme : SchemeInterface prims) (pk : PublicKeyCore prims.core)
    (address : Adrs) (input : prims.Y) :
    ¬ HashQueryBound
      (liftM ((adversaryOracleSpec prims scheme pk).query (.f address input)) :
        OracleComp (adversaryOracleSpec prims scheme pk) prims.Y) 0 := by
  simp

@[simp]
theorem signingBound_pure_zero {p : Params} {prims : Primitives p}
    (scheme : SchemeInterface prims) (pk : PublicKeyCore prims.core)
    {α : Type} (value : α) :
    SigningBound (pure value : OracleComp (adversaryOracleSpec prims scheme pk) α) 0 := by
  simp [SigningBound]

@[simp]
theorem hashQueryBound_pure_zero {p : Params} {prims : Primitives p}
    (scheme : SchemeInterface prims) (pk : PublicKeyCore prims.core)
    {α : Type} (value : α) :
    HashQueryBound (pure value : OracleComp (adversaryOracleSpec prims scheme pk) α) 0 := by
  simp [HashQueryBound]

end SLHDSA.Security
