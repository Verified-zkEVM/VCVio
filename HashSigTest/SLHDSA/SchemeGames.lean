/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.SchemeGames

/-!
# SLH-DSA scheme game canaries

Executable checks that the two selectors of `HashSig.SLHDSA.Security.SchemeGames` read what their
statements say they read — the internal message and not the external one, the FORS half and not the
hypertree half, the public key's seed and not the secret key's, the log at one message and not
across it — and that internalising a signing log moves the `H_msg` transcript without moving any
per-message reading of it.  All evaluated at values.

## Nothing probabilistic is checkable here, and that is a property of the subject

Every probability in the library module is `noncomputable`: `Pr[…]`, both instrumented experiments,
all four halves, both splits.  So the four probabilistic statements — the two splits, the library's
exact partition at the canonical runtime, and the four-term bound — have no runtime coverage at all
and cannot be given any.  They are pinned by elaboration, in `Pins`, and their content is checked by
mutation testing and by the two pairs of `example`s the library module carries beside the halves.
A reader of the lane's other fixtures will expect runtime coverage of the headline; there cannot
be any, and every executable check below is therefore about the *deterministic* data
the two splits are instrumented with.

## The profile is the SUF residual fixture's, with one deliberate change to its `H_msg`

The block below is the one `HashSigTest.SLHDSA.SufResidual` builds — the same seven parameters, the
same address maps, the same collapsing `Thash`, the same three honest seeds — copied rather than
imported for the reason that file gives: a `lean_exe` root must own its `main`, and a module that
imports another fixture cannot declare one.

**The change, and why it is not optional.**  That file's `H_msg` and `PRF_msg` read a message
through `byteFold`, the exclusive-or of its bytes.  FIPS 205's empty-context encoding prefixes two
`0x00` bytes, and an exclusive-or fold cannot see them: `byteFold (emptyContextMessage m)` is
`byteFold m` for *every* `m`, which `checkFixture` asserts directly at two messages.  At that
bundle the internal-message canary below would pass against a selector that dropped
`emptyContextMessage` entirely — the one mutation this fixture exists to catch.  `byteMix`, which
folds the same bytes through the block's own nonlinear mix and starts from the message length,
does see them, and `checkFixture` asserts that too, at all three messages.  `byteFold` is kept,
used by nothing in the bundle, so that the blindness can be asserted rather than described.

Four further hunks, all forced by what the library module needs: `SampleableType` on `SkSeed` and
on `SkPrf` as well as on `PkSeed` and `Y`, because `generalAlg` samples all three seeds;
`otherPkSeed`, which that file dropped, because the selector reads two public seeds and separating
them needs a second one; `mismatchedSk`, a secret key whose public seed is not its public key's;
and the honest signatures are taken at `emptyContextMessage msg`, because that is what
`generalAlg.sign` signs.

## What this fixture adds over the SUF residual one

An internalised log, which no earlier fixture has needed, and two mutant readers offered beside the
real ones: `forsArmRaw`, the selector with `emptyContextMessage` dropped, and `forsArmSkSeed`, the
selector reading its public seed off the secret key.  Each is asserted to *disagree* with the real
reader at fixture data, which is what makes the corresponding mutation caught rather than merely
described.  A third mutant, `internalLogOne`, prefixes one zero byte rather than two: it is
injective, so every per-message transport still holds of it, and only the transcript's value
separates them.

Five forgeries.  `sigD` and `sigE` differ **only** in the FORS half — `sigD.hypertree ==
sigE.hypertree` and their randomizers agree, so they split to one digest at one instance address —
and take opposite arms.  `sigH` differs from the honest signature only in the hypertree half and
takes the same arm as it, which exhibits the selector's structural blindness rather than hiding it.
`sigLate` carries the log's *second* randomizer at the twice-signed message, and `forgeryCross` the
randomizer the log recorded at the *other* message.

## The reader-by-log matrix

Five readers, three logs.  `forsArm` reads no log, so its row is blank by construction and is
listed rather than omitted.

The three logs: **L1** `signingLog`, three entries, two distinct randomizers at `msgP`, separated
by `msgQ`; **L2** `deterministicLog`, the FIPS 205 §9.2 variant's three entries, one randomizer per
message; **L3** `thriceSignedLog`, four entries, `msgP` three times with its first entry repeated.

**R1**, `forsArm`, at L1, L2 and L3 — *blank, at all three*.  It takes a key pair, a message and a
signature; there is no log in its argument list.

**R2**, `randomizerLogged log msg sig`.

* At **L1** it catches a reader that ignores the message — `forgeryCross`'s randomizer is logged at
  the *other* message, and must read `false` here and `true` there; one that keeps only the first
  signature at a message — `sigLate` carries the randomizer of the log's *last* entry at `msgP`; one
  that keeps only the last — `sigD` carries the *first* entry's; and one that drops the head, that
  first entry being `msgP`'s only occurrence of its randomizer in this log.
* At **L2** it catches a reader that reports membership only where a message carries two *distinct*
  randomizers: L2's list at `msgP` is one value twice, and `detSigP` must still read `true`.
* At **L3** it catches a truncation that bites only at four entries: `sigP1`'s randomizer occurs at
  `msgP` only in L3's fourth entry.

**R3**, `loggedSignatures (internalLog log) (emptyContextMessage msg)`.

* At **L1** the list is pinned as `[sigP1, sigP2]`, which catches first-only and last-only readers,
  reordering — it differs from its reverse — truncation, and an identity internalisation, since the
  raw log lists nothing at the internal message.
* At **L2** it catches de-duplication: the list at `msgP` is one signature twice, which L1 cannot
  show because its two differ.
* At **L3** it catches reordering and collapsing together at three entries, a length neither other
  log reaches at one message.

**R4**, `logQueries (internalLog log)` and its embedding.

* At **L1** one pinned value catches reordering, truncation, an identity internalisation, and a
  one-byte prefix.
* At **L2** its three entries carry a repeat, which catches de-duplication.
* At **L3** its four entries catch a truncation that bites only there.

**R5**, `SignatureAlg.signingLogContains (internalLog log) (emptyContextMessage msg) sig`.

* At **L1** it catches a head-only reader and a message-blind one — `(msgP, sigP2)` is the log's
  last entry and `(msgQ, sigP2)` is no entry — an identity internalisation, and a reader that drops
  its first entry: `(msgP, sigP1)` is this log's first entry and occurs nowhere else in it, so the
  predicate reads `true` here and `false` under a head-drop.
* At **L2**, *blank*: nothing this predicate can show there that L1 and L3 do not.
* At **L3** it catches truncation at four entries, that pair being in the last entry only.

**Cells that cannot discriminate, and why.**  Two kinds, kept apart.

*No fixture could ever discriminate these.*

- **R2 and R5 × every log, for reordering and for de-duplication.**  R2 is `∈` on a list and R5 is
  membership of one pair.  Both are invariant under permutation and under `eraseDups`, so no log can
  make either visible.  This is a property of the two predicates, not a gap in the data, and is why
  R3 and R4 — which read lists rather than membership — carry those two readings instead.
- **R1 × the hypertree half.**  `forsArm` is a function of the key pair, the message, the
  randomizer and the FORS half.  No signature pair differing only in the hypertree half can move it
  at any profile; `sigH` exhibits exactly such a pair.
- **R1 × the two public seeds, at any key pair whose seeds agree.**  `pk.pkSeed` and `sk.pkSeed`
  are the same value on every key pair key generation produces, so the mutation is invisible on all
  of them.  `mismatchedSk` is the fixture's answer, and it is not a key pair the experiment can
  sample.

*This fixture cannot discriminate these; another could.*

- **R2 and R5 × L3, for a reader that drops its first entry.**  L3's first pair, `(msgP, detSigP)`,
  recurs at its third entry, so dropping the head changes nothing there for either reader.  This is
  a property of L3's shape, and L1 is where both readers catch a head-drop instead.
- **R2 × L2, for message-blindness.**  L2's two messages carry different randomizers, so a
  message-blind reader is caught there as well — but only because of that choice.  A later edit that
  made them coincide would take this cell dark without failing anything.
- **R1 × `otherPk` with the honest secret key.**  Both the real selector and the `sk.pkSeed` mutant
  read `false` there, so that pair separates nothing; it is asserted anyway, so that the one pair
  that *does* separate them is not mistaken for the only arrangement that could.
- **Every reader × a fifth log entry, or a fourth signature at one message.**  No list any reader
  here produces is longer than four.

## What is not checked, and cannot be

The dispatch bit is not compared against any bound, and no half is evaluated: they are
`noncomputable`.  Whether the two names `forsHalf` and `hypertreeHalf` are attached to the right
branches is settled inside the library module, by four `example`s — two per split — that see the
unexposed bodies, and not here: an importing module cannot state that equation at all.  That the
halves are events of the success bit at all is settled there too, and by theorems rather than by
those `example`s, for a reason this file cannot repair: an `example … := rfl` moves with the body
it is `rfl` against, so a paired weakening of all four halves survives it, survives every check
below, and survives this executable.  Nothing here says that any honest value was recorded as a
game target, that any execution produced any log below, or that either half is bounded by
anything.

## The pins

Every one of the forty-eight declarations the library module exports appears as an `example` at
this bundle's types, with generic arguments where the statement has them.  Seven further `example`s
are the profile's own `decide` pins, inherited with the copied block.
-/

public section

namespace SLHDSA.SchemeGamesTest

open Security Security.CanonicalGames KeyedHash OracleSpec

/-- Throw on a failed check, naming it. -/
def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"Scheme game check failed: {label}")

/-! ## The toy profile

Two hypertree layers of height two, two FORS trees of height one, `w = 16`, `len = 4`. -/

-- Exposed, and what that attribute is for was read off the errors its removal produces in this
-- file: 58 errors, no error ceiling reached, the first inside the bundle at `yToBytes := id`,
-- `Type mismatch: id has type ?m → ?m but is expected to have type Bytes 1 → Bytes toyParams.n`.
/-- Two layers of height two, two FORS trees of height one. -/
@[expose] def toyParams : Params :=
  { n := 1, h := 4, d := 2, hp := 2, a := 1, k := 2, lgw := 4 }

/-- The toy parameters are valid. -/
theorem toyValid : toyParams.Valid := by decide

-- Exposed, because this file states three `DecidableEq` instances whose types are written at
-- `toy.params`, and every signature and digest it builds is at `toy`: without the attribute the
-- build runs into Lean's hundred-error ceiling
-- — a hundred errors and the line saying `maximum number of errors (100; from option 'maxErrors')
-- reached`, so the count is a floor and not a total — the first at the `ForsTreeSigCore` instance,
-- `Application type mismatch: the argument toyPrimitives.core has type CorePrimitives toyParams
-- but is expected to have type CorePrimitives toy.params`.
/-- The validated form of `toyParams`. -/
@[expose] def toy : ValidatedParams := ⟨toyParams, toyValid⟩

example : toyParams.w = 16 := by decide
example : toyParams.len = 4 := by decide
example : toyParams.m = 3 := by decide
example : toyParams.digestBytes = 1 := by decide
example : toyParams.treeIdxBytes = 1 := by decide
example : toyParams.leafIdxBytes = 1 := by decide
example : toyParams.t = 2 := by decide

/-- The exclusive-or fold the SUF residual fixture's `H_msg` reads a message through.  Nothing in
this bundle uses it.  It is here so that `checkFixture` can assert what it cannot see: prefixing two
`0x00` bytes leaves it unchanged, at every message, so at that fixture's bundle the external-message
canary below would be blind. -/
def byteFold (m : List Byte) : UInt8 := m.foldl (fun acc b => acc ^^^ b) 0

/-- A nonlinear byte mix.  Without it the digest bytes are linear in their inputs and their low bits
— the two hypertree indices — collapse to constants at a fixed key pair, which would make the
digest-derived position inert. -/
def mixByte (x : UInt8) : UInt8 := ((x * (181 : UInt8)) ^^^ (x >>> (3 : UInt8))) + 97

/-- The fold this bundle's `H_msg` and `PRF_msg` read a message through: the same bytes, folded
through `mixByte` from the message's own length.  Both the position of a byte and the number of
bytes reach the result, so the FIPS 205 §10 encoding moves it and the internal message is a
different `H_msg` input from the external one. -/
def byteMix (m : List Byte) : UInt8 :=
  m.foldl (fun acc b => mixByte (acc ^^^ b)) (UInt8.ofNat (m.length % 256))

/-- The per-address secret values the toy `PRF` hands out.  Both seeds and all six address words
enter, so no two addresses and no two key pairs share secret material. -/
def toySecret (seed sk : UInt8) (a : Adrs) : UInt8 :=
  UInt8.ofNat ((seed.toNat * 19 + sk.toNat * 23 + a.layer * 101 + a.tree * 53 + a.type * 61 +
    a.word1 * 37 + a.word2 * 11 + a.word3 * 7 + 5) % 256)

/-- A per-address byte mixed into every `Thash` output, taking the public seed and all six address
words, so the same children at two different layers, trees, types or nodes hash differently. -/
def toyTweak (seed : UInt8) (a : Adrs) : UInt8 :=
  UInt8.ofNat ((seed.toNat * 17 + a.layer * 131 + a.tree * 71 + a.type * 41 + a.word1 * 29 +
    a.word2 * 43 + a.word3 * 97) % 256)

/-- The toy `PRF_msg`: the message randomizer FIPS 205 Algorithm 19 line 3 derives.  It reads the
per-signature `addrnd` and the message through `byteMix`. -/
def toyRandomizer (skPrf addrnd : UInt8) (msg : List Byte) : UInt8 :=
  mixByte (UInt8.ofNat
    ((skPrf.toNat * 13 + addrnd.toNat * 47 + (byteMix msg).toNat * 5 + 1) % 256))

/-- Byte `i` of the toy `H_msg` digest.  All four FIPS inputs enter every byte — the randomizer, the
public seed, the published root and the message fold — and the fold is `byteMix`, so the two zero
bytes of the empty-context encoding move the digest. -/
def toyDigestByte (r seed root : UInt8) (msg : List Byte) (i : ℕ) : UInt8 :=
  mixByte (UInt8.ofNat ((r.toNat * (6 * i + 37) + seed.toNat * (10 * i + 53) +
    root.toNat * (14 * i + 89) + (byteMix msg).toNat * (22 * i + 149) + (30 * i + 7)) % 256))

-- Exposed and `@[reducible]`, for two different reasons, each read off the errors that removing
-- that attribute alone produces in this file.  Exposed, for code generation: without it the build
-- runs into Lean's hundred-error ceiling — a hundred errors and the line saying the ceiling was
-- reached, so the count is a floor — the first at `instance : DecidableEq toyPrimitives.Y` just
-- below, `Compilation failed, locally inferred compilation type differs from type that would be
-- inferred in other modules`.  Reducible, because its carrier types have to unfold to `Bytes 1` for
-- instance resolution to reach them: without it, 12 errors and only these — one `GetElem
-- toyPrimitives.Y ℕ` at `byteOf`, and the failure to prove its index valid; two `BEq
-- (ITSRTranscript toyPrimitives.Y (HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y))` and one
-- `BEq (toyPrimitives.Y × HmsgITSRInput …)`, the three transcript value pins in `checkBranches`;
-- four `Decidable (… ∈ embeddedTargets)` in the same group; two `DecidableEq (HmsgITSRInput
-- toyPrimitives.PkSeed toyPrimitives.Y)`, one there and one in the pins; and one `DecidableEq
-- toyPrimitives.PkSeed`, in the pins.  Nothing outside this executable consumes it.
/-- The toy bundle: one byte per node, a collapsing order- and address-sensitive `Thash`, and an
`H_msg` that depends on all four of its arguments and reads its message through `byteMix`. -/
@[expose, reducible] def toyPrimitives : Primitives toyParams where
  PkSeed := Bytes 1
  SkSeed := Bytes 1
  SkPrf := Bytes 1
  Y := Bytes 1
  AdrsKey := Adrs
  adrsToKey := id
  PRF := fun pk sk adrs => Vector.replicate 1 (toySecret pk[0] sk[0] adrs)
  PRFmsg := fun skPrf addrnd msg => Vector.replicate 1 (toyRandomizer skPrf[0] addrnd[0] msg)
  yToBytes := id
  Thash := fun pk adrs children =>
    Vector.replicate 1
      ((children.foldl (fun (acc : UInt8) (y : Bytes 1) => (acc <<< 2) ^^^ (y[0] >>> 1))
        (0 : UInt8)) ^^^ toyTweak pk[0] adrs)
  Hmsg := fun r pk root msg =>
    Vector.ofFn fun i => toyDigestByte r[0] pk[0] root[0] msg i.val

/-- Node equality, at the one-byte carrier. -/
instance : DecidableEq toyPrimitives.Y := inferInstanceAs (DecidableEq (Bytes 1))

/-- Key generation samples the public seed. -/
instance : SampleableType toyPrimitives.PkSeed := inferInstanceAs (SampleableType (Bytes 1))

/-- Key generation samples the secret seed. -/
instance : SampleableType toyPrimitives.SkSeed := inferInstanceAs (SampleableType (Bytes 1))

/-- Key generation samples the message-PRF key. -/
instance : SampleableType toyPrimitives.SkPrf := inferInstanceAs (SampleableType (Bytes 1))

/-- Signing samples the per-signature `addrnd`. -/
instance : SampleableType toyPrimitives.Y := inferInstanceAs (SampleableType (Bytes 1))

/-- The bundle's byte laws, which the extractor's completeness theorem takes. -/
theorem toyByteLaws : toyPrimitives.core.ByteLaws := ⟨fun _ _ h => h⟩

/-- A one-byte node. -/
def node (x : UInt8) : toyPrimitives.Y := Vector.replicate 1 x

/-- The byte inside a node. -/
def byteOf (y : toyPrimitives.Y) : UInt8 := y[0]

/-- The honest secret seed. -/
def skSeed : toyPrimitives.SkSeed := node 0x11

/-- The honest message-PRF key. -/
def skPrf : toyPrimitives.SkPrf := node 0x22

/-- The honest public seed, which is a byte rather than a unit, so the `pkSeed` argument of every
statement below is load-bearing. -/
def pkSeed : toyPrimitives.PkSeed := node 0x33

/-- A second public seed.  The selector reads one public seed off the public key and generates the
honest FORS material under another; separating the two needs a value that is not the honest one. -/
def otherPkSeed : toyPrimitives.PkSeed := node 0x77

/-- The published hypertree root. -/
def pkRoot : toyPrimitives.Y := GeneralHypertree.root toy toyPrimitives skSeed pkSeed

/-- The honest public key. -/
def honestPk : PublicKeyCore toyPrimitives.core := ⟨pkSeed, pkRoot⟩

/-- The honest secret key. -/
def secretKey : SecretKeyCore toyPrimitives.core := ⟨skSeed, skPrf, pkSeed, pkRoot⟩

/-- FORS tree signature equality, field by field. -/
instance : DecidableEq (ForsTreeSigCore toy.params toyPrimitives.core) := fun a b =>
  decidable_of_iff (a.sk = b.sk ∧ a.auth = b.auth)
    ⟨fun h => by cases a; cases b; simp only at h; obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl,
     fun h => h ▸ ⟨rfl, rfl⟩⟩

/-- XMSS component equality, field by field. -/
instance : DecidableEq (XmssSigCore toy.params toyPrimitives.core) := fun a b =>
  decidable_of_iff (a.wots = b.wots ∧ a.auth = b.auth)
    ⟨fun h => by cases a; cases b; simp only at h; obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl,
     fun h => h ▸ ⟨rfl, rfl⟩⟩

/-- Signature equality, field by field.  The library module carries this as a hypothesis because no
such instance exists on this branch. -/
instance : DecidableEq (GeneralScheme.SignatureCore toy toyPrimitives.core) := fun a b =>
  decidable_of_iff (a.randomness = b.randomness ∧ a.fors = b.fors ∧ a.hypertree = b.hypertree)
    ⟨fun h => by
      cases a; cases b; simp only at h
      obtain ⟨h1, h2, h3⟩ := h; subst h1; subst h2; subst h3; rfl,
     fun h => h ▸ ⟨rfl, rfl, rfl⟩⟩

/-! ## Messages and honest signatures -/

/-- The message signed twice. -/
def msgP : List Byte := [0x01, 0x02]

/-- A second signed message. -/
def msgQ : List Byte := [0x05]

/-- A message the log never carries. -/
def msgU : List Byte := [0x07, 0x09]

/-- The honest signature on the external message `msg`, under `addrnd`: what `generalAlg.sign`
returns. -/
def honestSig (msg : List Byte) (addrnd : UInt8) :
    GeneralScheme.SignatureCore toy toyPrimitives.core :=
  GeneralScheme.signInternal toy toyPrimitives (emptyContextMessage msg) secretKey (node addrnd)

/-- The first honest signature on `msgP`, under one `addrnd`. -/
def sigP1 : GeneralScheme.SignatureCore toy toyPrimitives.core := honestSig msgP 0x41

/-- The second honest signature on `msgP`, under a different `addrnd`. -/
def sigP2 : GeneralScheme.SignatureCore toy toyPrimitives.core := honestSig msgP 0x42

/-- The honest signature on `msgQ`. -/
def sigQ : GeneralScheme.SignatureCore toy toyPrimitives.core := honestSig msgQ 0x43

/-- FIPS 205 §9.2's deterministic variant on `msgP`: `opt_rand` is `PK.seed` rather than a fresh
`addrnd`, so signing `msgP` twice is the same call. -/
def detSigP : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  GeneralScheme.signInternal toy toyPrimitives (emptyContextMessage msgP) secretKey pkSeed

/-- The same variant on `msgQ`. -/
def detSigQ : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  GeneralScheme.signInternal toy toyPrimitives (emptyContextMessage msgQ) secretKey pkSeed

/-- The signing log.  The `msgQ` entry sits between the two `msgP` entries, so a reading that
stopped at the first match, or that ignored the message, would show up. -/
def signingLog : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore toy toyPrimitives.core) :=
  [⟨msgP, sigP1⟩, ⟨msgQ, sigQ⟩, ⟨msgP, sigP2⟩]

/-- The log FIPS 205's deterministic variant would produce for the same three queries: one
randomizer per message, so the list at the twice-signed message is one value twice. -/
def deterministicLog :
    QueryLog (List Byte →ₒ GeneralScheme.SignatureCore toy toyPrimitives.core) :=
  [⟨msgP, detSigP⟩, ⟨msgQ, detSigQ⟩, ⟨msgP, detSigP⟩]

/-- A longer log, and the only one that signs one message three times.  Its fourth entry is the only
place any log here carries `sigP1`'s randomizer at `msgP` beyond L1's head. -/
def thriceSignedLog :
    QueryLog (List Byte →ₒ GeneralScheme.SignatureCore toy toyPrimitives.core) :=
  [⟨msgP, detSigP⟩, ⟨msgQ, detSigQ⟩, ⟨msgP, detSigP⟩, ⟨msgP, sigP1⟩]

/-! ## The forgeries -/

/-- **The FORS-arm forgery.**  `sigP1` with tree zero's revealed value moved, which leaves the
recovered FORS public key the honest one.  It verifies and takes the FORS arm. -/
def sigD : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  { sigP1 with fors := sigP1.fors.set 0 { sigP1.fors[0] with
      sk := node (byteOf sigP1.fors[0].sk + 1) } }

/-- **The hypertree-arm forgery.**  `sigP1` with tree one's revealed value moved, which does move
the recovered FORS public key.  It verifies — the toy `Thash` is collapsing, so the moved key still
climbs to the published root — and takes the hypertree arm.  Its hypertree half is `sigD`'s, by
construction: both are `sigP1`'s. -/
def sigE : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  { sigP1 with fors := sigP1.fors.set 1 { sigP1.fors[1] with
      sk := node (byteOf sigP1.fors[1].sk + 2) } }

/-- **The hypertree-half forgery.**  `sigP1` with one authentication node of its layer-zero
component moved.  It verifies, shares `sigP1`'s FORS half and randomizer, and must take `sigP1`'s
arm: the selector reads no part of the hypertree half. -/
def sigH : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  { sigP1 with hypertree := sigP1.hypertree.set 0 { sigP1.hypertree[0] with
      auth := sigP1.hypertree[0].auth.set 1 (node (byteOf sigP1.hypertree[0].auth[1] + 3)) } }

/-- A forgery carrying the *second* logged signature's randomizer at the twice-signed message, so a
reading of the log that kept only its first entry there would call it fresh. -/
def sigLate : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  { sigP2 with fors := sigP2.fors.set 0 { sigP2.fors[0] with
      sk := node (byteOf sigP2.fors[0].sk + 1) } }

/-- A strong forgery on the *queried* message `msgP`: the honest signer run again under randomness
the log does not carry.  It verifies, and its exact pair is not in the log. -/
def forgeryFresh : GeneralScheme.SignatureCore toy toyPrimitives.core := honestSig msgP 0x51

/-- A forgery on `msgP` carrying the randomizer the log recorded at `msgQ`.  The randomizer occurs
in the log, but not paired with `msgP`, so a reading that swept the whole log would put it on the
other branch. -/
def forgeryCross : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  { sigP1 with randomness := sigQ.randomness }

/-! ## Readers, and the three mutant readers this file offers them against -/

/-- The digest split the external algorithm produces: at `emptyContextMessage msg`. -/
def internalParts (msg : List Byte) (sig : GeneralScheme.SignatureCore toy toyPrimitives.core) :
    DigestParts toyParams :=
  schemeParts toy toyPrimitives (emptyContextMessage msg) sig honestPk

/-- The digest split at the *raw* message, which is what a selector with `emptyContextMessage`
dropped would use.  Nothing in the library module computes this. -/
def rawParts (msg : List Byte) (sig : GeneralScheme.SignatureCore toy toyPrimitives.core) :
    DigestParts toyParams :=
  schemeParts toy toyPrimitives msg sig honestPk

/-- A digest split's three readable components.  `DigestParts` carries no `BEq`, and the FORS
address is a function of the two indices, so these three decide the split. -/
def partsData (parts : DigestParts toyParams) : List Byte × ℕ × ℕ :=
  (parts.md.toList, parts.idxTree, parts.idxLeaf)

/-- Verification as the external algorithm performs it. -/
def verifyAt (msg : List Byte) (sig : GeneralScheme.SignatureCore toy toyPrimitives.core) : Bool :=
  GeneralScheme.verifyInternal toy toyPrimitives (emptyContextMessage msg) sig honestPk

/-- The dispatch bit at the honest secret key. -/
def armAt (pk : PublicKeyCore toyPrimitives.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore toy toyPrimitives.core) : Bool :=
  forsArm (vp := toy) toyPrimitives pk secretKey msg sig

/-- A public key at the second seed.  Its root is the honest one, so it is not a key pair anything
generated; it exists to be a public key whose seed is not the honest secret key's. -/
def otherPk : PublicKeyCore toyPrimitives.core := ⟨otherPkSeed, pkRoot⟩

/-- **Mutant reader.**  The dispatch bit with `emptyContextMessage` dropped — the selector applied
to the raw message.  It has the same type as the real one and every statement about it elaborates;
only a bundle whose `H_msg` can see the encoding separates them. -/
def forsArmRaw (pk : PublicKeyCore toyPrimitives.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore toy toyPrimitives.core) : Bool :=
  decide (forsPkFromSig toyPrimitives sig.fors (rawParts msg sig).md.toList pk.pkSeed
      (rawParts msg sig).forsAdrs =
    forsPkGen toyPrimitives secretKey.skSeed pk.pkSeed (rawParts msg sig).forsAdrs)

/-- The dispatch bit at an arbitrary secret key. -/
def armWith (pk : PublicKeyCore toyPrimitives.core) (sk : SecretKeyCore toyPrimitives.core)
    (msg : List Byte) (sig : GeneralScheme.SignatureCore toy toyPrimitives.core) : Bool :=
  forsArm (vp := toy) toyPrimitives pk sk msg sig

/-- **Mutant reader.**  The dispatch bit reading its public seed off the *secret* key rather than
off the public key.  On every key pair key generation produces the two agree, so this is invisible
there; `mismatchedSk` is the one argument that separates them. -/
def forsArmSkSeed (pk : PublicKeyCore toyPrimitives.core)
    (sk : SecretKeyCore toyPrimitives.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore toy toyPrimitives.core) : Bool :=
  decide (forsPkFromSig toyPrimitives sig.fors
      (schemeParts toy toyPrimitives (emptyContextMessage msg) sig pk).md.toList
      sk.pkSeed
      (schemeParts toy toyPrimitives (emptyContextMessage msg) sig pk).forsAdrs =
    forsPkGen toyPrimitives sk.skSeed sk.pkSeed
      (schemeParts toy toyPrimitives (emptyContextMessage msg) sig pk).forsAdrs)

/-- A secret key whose public seed is not the honest public key's.  Key generation produces no such
key; it exists to separate the two public-seed readings. -/
def mismatchedSk : SecretKeyCore toyPrimitives.core :=
  { secretKey with pkSeed := otherPkSeed }

/-- **Mutant reader.**  An internalisation that prefixes one zero byte rather than two.  It is
injective, so every per-message transport still holds of it; only the transcript's value differs. -/
def internalLogOne
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore toy toyPrimitives.core)) :
    QueryLog (List Byte →ₒ GeneralScheme.SignatureCore toy toyPrimitives.core) :=
  log.map fun e => ⟨0x00 :: e.1, e.2⟩

/-- The forged pair read as an ITSR candidate at the honest key pair, at the *internal* message. -/
def candidateOf (msg : List Byte) (sig : GeneralScheme.SignatureCore toy toyPrimitives.core) :
    toyPrimitives.Y × HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y :=
  (sig.randomness, ⟨pkSeed, pkRoot, emptyContextMessage msg⟩)

/-- The transcript a reduction records from the internalised signing log, embedded at the honest key
pair. -/
def embeddedTargets :
    ITSRTranscript toyPrimitives.Y (HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y) :=
  embedTargets toyPrimitives pkSeed pkRoot (logQueries (internalLog signingLog))

/-! ## The checks -/

/-- The profile's own data, and the one hunk that separates it from the fixture it was copied from.

The first three properties are that hunk, asserted rather than described: the empty-context encoding
is two zero bytes, the inherited exclusive-or fold cannot see them at either signed message, and the
fold this bundle uses can, at all three messages.  Without that change the internal-message canary
of `checkInternalMessage` would pass against a selector with `emptyContextMessage` dropped.

Then the liveness of the two message-derived maps — each of `H_msg`'s four FIPS inputs moved alone
and the digest required to move with it, and `PRF_msg` moved in each of its two — the hedged and
deterministic signing shapes, which signatures verify, and that each of the five forgeries differs
from the signature it was built from in exactly the intended half.  Twenty properties. -/
def checkFixture : IO Unit := do
  ensure "the empty-context encoding prefixes two zero bytes"
    (emptyContextMessage msgP == [0x00, 0x00, 0x01, 0x02])
  ensure "the inherited exclusive-or fold cannot see that encoding"
    (byteFold msgP == byteFold (emptyContextMessage msgP) &&
      byteFold msgQ == byteFold (emptyContextMessage msgQ))
  ensure "the fold this bundle uses can, at every message it carries"
    (byteMix msgP != byteMix (emptyContextMessage msgP) &&
      byteMix msgQ != byteMix (emptyContextMessage msgQ) &&
      byteMix msgU != byteMix (emptyContextMessage msgU))
  ensure "the three messages are pairwise distinct and so are their folds"
    (msgP != msgQ && msgP != msgU && msgQ != msgU &&
      byteMix msgP != byteMix msgQ && byteMix msgP != byteMix msgU &&
      byteMix msgQ != byteMix msgU)
  ensure "H_msg moves with its randomizer"
    (toyPrimitives.Hmsg (node 1) pkSeed pkRoot msgP !=
      toyPrimitives.Hmsg (node 2) pkSeed pkRoot msgP)
  ensure "with its public seed"
    (toyPrimitives.Hmsg (node 1) pkSeed pkRoot msgP !=
      toyPrimitives.Hmsg (node 1) otherPkSeed pkRoot msgP)
  ensure "with its published root"
    (toyPrimitives.Hmsg (node 1) pkSeed pkRoot msgP !=
      toyPrimitives.Hmsg (node 1) pkSeed (node (byteOf pkRoot + 1)) msgP)
  ensure "and with its message"
    (toyPrimitives.Hmsg (node 1) pkSeed pkRoot msgP !=
      toyPrimitives.Hmsg (node 1) pkSeed pkRoot msgQ)
  ensure "PRF_msg moves with its per-signature randomness"
    (toyPrimitives.PRFmsg skPrf (node 1) msgP != toyPrimitives.PRFmsg skPrf (node 2) msgP)
  ensure "and with its message"
    (toyPrimitives.PRFmsg skPrf (node 1) msgP != toyPrimitives.PRFmsg skPrf (node 1) msgQ)
  ensure "hedged signing gives the two queries on one message different randomizers"
    (sigP1.randomness != sigP2.randomness && sigP1 != sigP2)
  ensure "the deterministic variant gives one randomizer per message, and two across them"
    (detSigP.randomness == detSigP.randomness && detSigP.randomness != detSigQ.randomness)
  ensure "every honest signature verifies at its own external message"
    (verifyAt msgP sigP1 && verifyAt msgP sigP2 && verifyAt msgQ sigQ &&
      verifyAt msgP detSigP && verifyAt msgQ detSigQ && verifyAt msgP forgeryFresh)
  ensure "the FORS-arm forgery moves the FORS half and nothing else"
    (sigD.fors != sigP1.fors && sigD.hypertree == sigP1.hypertree &&
      sigD.randomness == sigP1.randomness && sigD != sigP1)
  ensure "the hypertree-arm forgery moves the FORS half and nothing else"
    (sigE.fors != sigP1.fors && sigE.hypertree == sigP1.hypertree &&
      sigE.randomness == sigP1.randomness && sigE != sigP1)
  ensure "the hypertree-half forgery moves the hypertree half and nothing else"
    (sigH.fors == sigP1.fors && sigH.hypertree != sigP1.hypertree &&
      sigH.randomness == sigP1.randomness && sigH != sigP1)
  ensure "all three of them verify"
    (verifyAt msgP sigD && verifyAt msgP sigE && verifyAt msgP sigH)
  ensure "the late forgery carries the second logged signature's randomizer"
    (sigLate.randomness == sigP2.randomness && sigLate != sigP2)
  ensure "the cross forgery carries the randomizer the log recorded at the other message"
    (forgeryCross.randomness == sigQ.randomness &&
      forgeryCross.randomness != sigP1.randomness &&
      forgeryCross.randomness != sigP2.randomness)
  ensure "and the fresh forgery's randomizer is neither of the two at its message"
    (forgeryFresh.randomness != sigP1.randomness &&
      forgeryFresh.randomness != sigP2.randomness)

/-- The dispatch bit, and the three arguments of it that can be silently wrong.

`sigD` and `sigE` differ only in the FORS half — the whole hypertree signature is held fixed and
their randomizers agree, so they split to one digest at one instance address — and they take
opposite arms.  That is what pins that the arm is decided by the FORS public-key comparison and by
nothing else, and it is the defect #699's review record fixed in its own fixture: a pair claimed to
differ only in the FORS half must be shown to.

`sigH` is the other direction.  It differs from the honest signature only in the hypertree half and
takes the same arm, which is not a weakness to hide: the selector is a function of the key pair, the
message, the randomizer and the FORS half, so no fixture at any profile could make a hypertree-only
change move it.

The last three are the public seed.  At `mismatchedSk`, whose public seed is not its public key's,
the real selector and the `sk.pkSeed` mutant disagree; at the honest key pair they agree, and at a
public key the honest secret key was not generated under they agree as well, both reading `false`.
Only the first of those three separates the two readings, and the other two are asserted so that it
is clear how narrow that is.  Eleven properties. -/
def checkArmSelection : IO Unit := do
  ensure "the two arm-selection forgeries hold the whole hypertree signature fixed"
    (sigD.hypertree == sigE.hypertree)
  ensure "and the randomizer, so they split to one digest at one instance address"
    (sigD.randomness == sigE.randomness &&
      partsData (internalParts msgP sigD) == partsData (internalParts msgP sigE))
  ensure "they differ, and only in the FORS half"
    (sigD.fors != sigE.fors && sigD != sigE)
  ensure "the honest signature takes the FORS arm"
    (armAt honestPk msgP sigP1 && armAt honestPk msgQ sigQ)
  ensure "one of the pair takes the FORS arm and the other does not"
    (armAt honestPk msgP sigD && !armAt honestPk msgP sigE)
  ensure "so the arm is decided by the FORS half and not by the digest"
    (armAt honestPk msgP sigD != armAt honestPk msgP sigE)
  ensure "the selector reads nothing of the hypertree half"
    (sigH.hypertree != sigP1.hypertree && armAt honestPk msgP sigH == armAt honestPk msgP sigP1)
  ensure "and the forged FORS half a wrong recovered key comes from still verifies"
    (verifyAt msgP sigE)
  ensure "the selector reads the public seed off the public key, not off the secret key"
    (armWith honestPk mismatchedSk msgP sigP1 !=
      forsArmSkSeed honestPk mismatchedSk msgP sigP1)
  ensure "which is invisible wherever the key pair's two public seeds agree"
    (armWith honestPk secretKey msgP sigP1 == forsArmSkSeed honestPk secretKey msgP sigP1 &&
      armWith honestPk secretKey msgP sigE == forsArmSkSeed honestPk secretKey msgP sigE)
  ensure "and invisible again at a public key the secret key was not generated under"
    (!armWith otherPk secretKey msgP sigP1 && !forsArmSkSeed otherPk secretKey msgP sigP1)

/-- The external-message trap.  The selector splits the digest of `emptyContextMessage msg`; a
selector at the raw `msg` type-checks, is `Bool`-valued, and leaves every statement in the library
module elaborating.

The two are asserted to disagree at three places — the honest signature at each of the two signed
messages, and a forgery — and the two digests are asserted to differ at both messages, which is what
makes the disagreement possible at all.  The last property is the other side of the same fact: the
honest signature verifies at the internal message and fails at the raw one.  Five properties. -/
def checkInternalMessage : IO Unit := do
  ensure "the internal and raw digests differ at every fixture message"
    (partsData (internalParts msgP sigP1) != partsData (rawParts msgP sigP1) &&
      partsData (internalParts msgQ sigQ) != partsData (rawParts msgQ sigQ))
  ensure "the selector at the internal message disagrees with one at the raw message"
    (armAt honestPk msgP sigP1 != forsArmRaw honestPk msgP sigP1)
  ensure "at the second message too"
    (armAt honestPk msgQ sigQ != forsArmRaw honestPk msgQ sigQ)
  ensure "and at a forgery, where both arms are reachable"
    (armAt honestPk msgP sigD != forsArmRaw honestPk msgP sigD)
  ensure "the honest signature verifies at the internal message and not at the raw one"
    (verifyAt msgP sigP1 &&
      !GeneralScheme.verifyInternal toy toyPrimitives msgP sigP1 honestPk)

/-- The internalised log: that it moves the transcript and moves nothing else.

The per-message readings are asserted equal to the raw log's at the raw message, and pinned by value
besides; the raw log read at the internal message, and the internalised log read at the raw one, are
both asserted empty, which is what a reader that skipped the internalisation would fail.  The
transcript is pinned by value on all three logs: L1's three distinct entries refuse reordering and
truncation, L2's repeat refuses collapsing, and L3's four entries refuse a truncation that bites
only there.  `internalLogOne`, which prefixes one byte rather than two, is asserted to give a
different transcript while giving the same per-message list — the two are separated by the
transcript alone, because both maps are injective.  The exact-pair predicate is read at L1's first
entry as well as at its last, so a reader that drops its head is caught here rather than left to
L3, where that log's repeated first pair would hide it.  Thirteen properties. -/
def checkInternalLog : IO Unit := do
  ensure "the internalised log lists, at the internal message, what the log lists at the raw one"
    (loggedSignatures (internalLog signingLog) (emptyContextMessage msgP) ==
      loggedSignatures signingLog msgP)
  ensure "and that list is the hand-written pair, in query order"
    (loggedSignatures (internalLog signingLog) (emptyContextMessage msgP) == [sigP1, sigP2])
  ensure "reading the raw log at the internal message finds nothing"
    (loggedSignatures signingLog (emptyContextMessage msgP) == [] &&
      loggedSignatures (internalLog signingLog) msgP == [])
  ensure "a deterministic log's two entries at one message survive as two"
    (loggedSignatures (internalLog deterministicLog) (emptyContextMessage msgP) ==
      [detSigP, detSigP])
  ensure "a four-entry log's three entries at one message survive as three, in order"
    (loggedSignatures (internalLog thriceSignedLog) (emptyContextMessage msgP) ==
      [detSigP, detSigP, sigP1])
  ensure "the transcript is the hand-written projection at the internal messages"
    (logQueries (internalLog signingLog) ==
      [(sigP1.randomness, emptyContextMessage msgP), (sigQ.randomness, emptyContextMessage msgQ),
        (sigP2.randomness, emptyContextMessage msgP)])
  ensure "a deterministic log's transcript keeps its repeat"
    (logQueries (internalLog deterministicLog) ==
      [(detSigP.randomness, emptyContextMessage msgP),
        (detSigQ.randomness, emptyContextMessage msgQ),
        (detSigP.randomness, emptyContextMessage msgP)])
  ensure "a four-entry log's transcript keeps all four, repeat included"
    (logQueries (internalLog thriceSignedLog) ==
      [(detSigP.randomness, emptyContextMessage msgP),
        (detSigQ.randomness, emptyContextMessage msgQ),
        (detSigP.randomness, emptyContextMessage msgP),
        (sigP1.randomness, emptyContextMessage msgP)])
  ensure "a one-byte prefix is a different internalisation, although it is injective too"
    (logQueries (internalLogOne signingLog) != logQueries (internalLog signingLog) &&
      loggedSignatures (internalLogOne signingLog) (0x00 :: msgP) ==
        loggedSignatures signingLog msgP)
  ensure "the exact-pair predicate is unmoved by the internalisation"
    (SignatureAlg.signingLogContains (internalLog signingLog) (emptyContextMessage msgP) sigP2 ==
        SignatureAlg.signingLogContains signingLog msgP sigP2 &&
      SignatureAlg.signingLogContains (internalLog signingLog) (emptyContextMessage msgP) sigP2)
  ensure "it is exact, and per message"
    (!SignatureAlg.signingLogContains (internalLog signingLog) (emptyContextMessage msgQ) sigP2 &&
      !SignatureAlg.signingLogContains (internalLog signingLog) (emptyContextMessage msgP) sigD)
  ensure "and it sees the pair a four-entry log holds only in its last entry"
    (SignatureAlg.signingLogContains (internalLog thriceSignedLog) (emptyContextMessage msgP)
        sigP1 &&
      !SignatureAlg.signingLogContains (internalLog thriceSignedLog) (emptyContextMessage msgP)
        sigP2)
  ensure "and the pair a three-entry log holds only in its first entry, which a head-drop loses"
    (SignatureAlg.signingLogContains (internalLog signingLog) (emptyContextMessage msgP) sigP1)

/-- The same-message selector, across the three logs.

`sigD` carries the log's first randomizer at the twice-signed message and `sigLate` its last, so
neither a first-match nor a last-match reading survives; `forgeryCross` carries one the log holds at
the *other* message and must read fresh here and logged there; the deterministic log's constant
two-element list must still report membership; and the four-entry log's last entry is the only place
its randomizer appears at that message.

What no log can show, because it is a property of `∈` and not of the data: that this reader is blind
to the order of a log and to repeats in it.  `checkInternalLog`'s list and transcript pins carry
those two readings instead.  Eight properties. -/
def checkRandomizerLogged : IO Unit := do
  ensure "a forgery carrying the first logged signature's randomizer reads as logged"
    (randomizerLogged signingLog msgP sigD && randomizerLogged signingLog msgP sigH)
  ensure "one carrying the second logged signature's randomizer reads as logged too"
    (randomizerLogged signingLog msgP sigLate)
  ensure "a fresh randomizer at a queried message reads as fresh"
    (!randomizerLogged signingLog msgP forgeryFresh)
  ensure "a randomizer the log recorded at another message reads as fresh here"
    (!randomizerLogged signingLog msgP forgeryCross &&
      randomizerLogged signingLog msgQ forgeryCross)
  ensure "nothing reads as logged at a message the log never carries"
    ([sigP1, sigP2, sigQ, forgeryFresh].all fun s => !randomizerLogged signingLog msgU s)
  ensure "a message whose logged randomizers are all equal still reports membership"
    ((loggedRandomizers deterministicLog msgP).eraseDups.length == 1 &&
      randomizerLogged deterministicLog msgP detSigP)
  ensure "a randomizer a four-entry log carries only in its last entry reads as logged"
    (randomizerLogged thriceSignedLog msgP sigP1 &&
      !randomizerLogged thriceSignedLog msgP forgeryFresh)
  ensure "the two logged randomizers at the twice-signed message are distinct"
    ((loggedRandomizers signingLog msgP).eraseDups.length == 2)

/-- The residual's two branches at the embedded transcript, and each conjunct of what the logged
branch yields.

The transcript is pinned by value first, and the embedding of the *raw* log's transcript is asserted
to be a different target set — the claim that the internalisation matters, at the place it matters.
On the fresh branch the candidate is absent and the first-uncovered-index extractor returns an
index; on the logged branch it is present, the winning condition fails, and — asserted separately,
because "the winning condition fails" would otherwise not say which conjunct failed — the coverage
conjunct still holds over an index list asserted non-empty, and the extractor returns nothing.

Then the five conjuncts of what `sameRandomizer_of_randomizerLogged` concludes, one at a time: the
partner is listed at that message, carries the same randomizer, differs from the forgery, splits to
the same digest, and differs from it in one of the two halves — with `sigD` realising the FORS
disjunct alone and `sigH` the hypertree one.  Three of the five are then falsified alone: the
same-randomizer conjunct at the fresh forgery, the listing conjunct at a signature the log holds
only at the other message, and the theorem's own freshness hypothesis at a replayed pair.  Twenty
properties. -/
def checkBranches : IO Unit := do
  ensure "the embedded transcript is the internalised log's three queries at the honest key pair"
    (embeddedTargets ==
      [(sigP1.randomness, ⟨pkSeed, pkRoot, emptyContextMessage msgP⟩),
        (sigQ.randomness, ⟨pkSeed, pkRoot, emptyContextMessage msgQ⟩),
        (sigP2.randomness, ⟨pkSeed, pkRoot, emptyContextMessage msgP⟩)])
  ensure "embedding the raw log's transcript gives a different target set"
    (embedTargets toyPrimitives pkSeed pkRoot (logQueries signingLog) != embeddedTargets)
  ensure "the fresh forgery is on the fresh branch and its candidate is absent"
    (!randomizerLogged signingLog msgP forgeryFresh &&
      !decide (candidateOf msgP forgeryFresh ∈ embeddedTargets))
  ensure "so the first-uncovered-index extractor returns an index for it"
    (findUncoveredIndex toyPrimitives embeddedTargets (candidateOf msgP forgeryFresh) != none)
  ensure "the cross forgery is on the fresh branch too, at the message it is offered at"
    (!randomizerLogged signingLog msgP forgeryCross &&
      !decide (candidateOf msgP forgeryCross ∈ embeddedTargets) &&
      decide (candidateOf msgQ forgeryCross ∈ embeddedTargets))
  ensure "the FORS-arm forgery is on the logged branch and its candidate is present"
    (randomizerLogged signingLog msgP sigD &&
      decide (candidateOf msgP sigD ∈ embeddedTargets))
  ensure "the hypertree-half forgery offers that same candidate"
    (candidateOf msgP sigH == candidateOf msgP sigD)
  ensure "so its winning condition fails"
    (!decide ((hmsgItsrProblem toyPrimitives).Wins embeddedTargets (candidateOf msgP sigD)))
  ensure "the candidate selects two FORS leaves, so that quantification is not over nothing"
    (((hmsgItsrProblem toyPrimitives).indexSet (candidateOf msgP sigD)).length == 2)
  ensure "and it fails on freshness alone: every index it selects is covered"
    (((hmsgItsrProblem toyPrimitives).indexSet (candidateOf msgP sigD)).all
      fun i => decide (i ∈ (hmsgItsrProblem toyPrimitives).targetIndexSet embeddedTargets))
  ensure "so the first-uncovered-index extractor returns nothing there"
    (findUncoveredIndex toyPrimitives embeddedTargets (candidateOf msgP sigD) == none)
  ensure "the partner the logged branch names is listed at that message"
    (decide (sigP1 ∈ loggedSignatures signingLog msgP))
  ensure "it carries the same randomizer"
    (sigP1.randomness == sigD.randomness && sigP1.randomness == sigH.randomness)
  ensure "it differs from the forgery, and the forgery's exact pair is not in the log"
    (sigP1 != sigD && sigP1 != sigH &&
      !SignatureAlg.signingLogContains signingLog msgP sigD &&
      !SignatureAlg.signingLogContains signingLog msgP sigH)
  ensure "the two split to the same digest against the same public key"
    (partsData (internalParts msgP sigD) == partsData (internalParts msgP sigP1) &&
      partsData (internalParts msgP sigH) == partsData (internalParts msgP sigP1))
  ensure "one of them realises the FORS disjunct alone"
    (sigD.fors != sigP1.fors && sigD.hypertree == sigP1.hypertree)
  ensure "and the other the hypertree disjunct alone"
    (sigH.fors == sigP1.fors && sigH.hypertree != sigP1.hypertree)
  ensure "the same-randomizer conjunct fails alone at the fresh forgery"
    (forgeryFresh.randomness != sigP1.randomness && forgeryFresh.randomness != sigP2.randomness &&
      !SignatureAlg.signingLogContains signingLog msgP forgeryFresh)
  ensure "the listing conjunct fails alone for a signature the log holds at the other message"
    (!decide (sigQ ∈ loggedSignatures signingLog msgP) &&
      decide (sigQ ∈ loggedSignatures signingLog msgQ))
  ensure "and the freshness hypothesis fails exactly at a replayed pair"
    (SignatureAlg.signingLogContains signingLog msgP sigP1 &&
      SignatureAlg.signingLogContains signingLog msgP sigP2 &&
      !SignatureAlg.signingLogContains signingLog msgP forgeryFresh)

/-! ## The pins

Every one of the forty-four declarations the library module exports, as an `example` at this
bundle's types, with generic arguments where the statement has them. -/

section Pins

open OracleComp ENNReal SignatureAlg

variable (pk : PublicKeyCore toyPrimitives.core) (sk : SecretKeyCore toyPrimitives.core)
  (msg : List Byte) (sig sig' : GeneralScheme.SignatureCore toy toyPrimitives.core)
  (target : Fin toyParams.k)
  (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore toy toyPrimitives.core))
  (adv : unforgeableAdv (generalAlg (vp := toy) toyPrimitives))
  (sadv : strongUnforgeableAdv (generalAlg (vp := toy) toyPrimitives))
  (sel : PublicKeyCore toyPrimitives.core → SecretKeyCore toyPrimitives.core → List Byte →
    GeneralScheme.SignatureCore toy toyPrimitives.core → Bool)
  (lsel : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore toy toyPrimitives.core) →
    List Byte → GeneralScheme.SignatureCore toy toyPrimitives.core → Bool)

example : SignatureAlg ProbComp (List Byte) (PublicKeyCore toyPrimitives.core)
    (SecretKeyCore toyPrimitives.core) (GeneralScheme.SignatureCore toy toyPrimitives.core) :=
  generalAlg (vp := toy) toyPrimitives

noncomputable example : SPMF (Bool × Bool) :=
  instrumentedEufExp ProbCompRuntime.probComp adv sel

noncomputable example : SPMF (Bool × Bool) :=
  instrumentedSameMessageExp ProbCompRuntime.probComp sadv lsel

example : unforgeableExp ProbCompRuntime.probComp adv =
    Prod.fst <$> instrumentedEufExp ProbCompRuntime.probComp adv sel :=
  instrumentedEufExp_fst ProbCompRuntime.probComp
    (fun f mx => ProbCompRuntime.probComp_evalSPMF_bind_pure f mx) adv sel

example : adv.advantage ProbCompRuntime.probComp ≤
    Pr[fun x => x.1 = true ∧ x.2 = true | instrumentedEufExp ProbCompRuntime.probComp adv sel] +
    Pr[fun x => x.1 = true ∧ x.2 = false | instrumentedEufExp ProbCompRuntime.probComp adv sel] :=
  advantage_le_arms ProbCompRuntime.probComp
    (fun f mx => ProbCompRuntime.probComp_evalSPMF_bind_pure f mx) adv sel

example : ProbCompRuntime.probComp.evalSPMF (sameMessageStrongUnforgeableGame sadv) =
    Prod.fst <$> instrumentedSameMessageExp ProbCompRuntime.probComp sadv lsel :=
  instrumentedSameMessageExp_fst ProbCompRuntime.probComp
    (fun f mx => ProbCompRuntime.probComp_evalSPMF_bind_pure f mx) sadv lsel

example : sadv.sameMessageAdvantage ProbCompRuntime.probComp ≤
    Pr[fun x => x.1 = true ∧ x.2 = true |
      instrumentedSameMessageExp ProbCompRuntime.probComp sadv lsel] +
    Pr[fun x => x.1 = true ∧ x.2 = false |
      instrumentedSameMessageExp ProbCompRuntime.probComp sadv lsel] :=
  sameMessageAdvantage_le_arms ProbCompRuntime.probComp
    (fun f mx => ProbCompRuntime.probComp_evalSPMF_bind_pure f mx) sadv lsel

example : (generalAlg (vp := toy) toyPrimitives).PerfectlyComplete ProbCompRuntime.probComp :=
  generalAlg_perfectlyComplete

example : (generalAlg (vp := toy) toyPrimitives).keygen = (do
    let skSeed ← $ᵗ toyPrimitives.SkSeed
    let skPrf ← $ᵗ toyPrimitives.SkPrf
    let pkSeed ← $ᵗ toyPrimitives.PkSeed
    pure (GeneralScheme.keygenInternal toy toyPrimitives skSeed skPrf pkSeed)) :=
  generalAlg_keygen (vp := toy)

example : (generalAlg (vp := toy) toyPrimitives).sign pk sk msg = (do
    let addrnd ← $ᵗ toyPrimitives.Y
    pure (GeneralScheme.signInternal toy toyPrimitives (emptyContextMessage msg) sk addrnd)) :=
  generalAlg_sign (vp := toy) pk sk msg

example : (generalAlg (vp := toy) toyPrimitives).verify pk msg sig =
    pure (GeneralScheme.verifyInternal toy toyPrimitives (emptyContextMessage msg) sig pk) :=
  generalAlg_verify (vp := toy) pk msg sig

example : (generalAlg (vp := toy) toyPrimitives).keygen = (do
    let skSeed ← $ᵗ toyPrimitives.SkSeed
    let skPrf ← $ᵗ toyPrimitives.SkPrf
    let pkSeed ← $ᵗ toyPrimitives.PkSeed
    pure ((⟨pkSeed, GeneralHypertree.root toy toyPrimitives skSeed pkSeed⟩ :
        PublicKeyCore toyPrimitives.core),
      (⟨skSeed, skPrf, pkSeed, GeneralHypertree.root toy toyPrimitives skSeed pkSeed⟩ :
        SecretKeyCore toyPrimitives.core))) :=
  generalAlg_keygen_eq (vp := toy)

example (h : (pk, sk) ∈ support ((generalAlg (vp := toy) toyPrimitives).keygen)) :
    pk = ⟨sk.pkSeed, GeneralHypertree.root toy toyPrimitives sk.skSeed sk.pkSeed⟩ :=
  honestKey_of_mem_support h

example : Bool := forsArm (vp := toy) toyPrimitives pk sk msg sig

example : forsArm (vp := toy) toyPrimitives pk sk msg sig = true ↔
    forsPkFromSig toyPrimitives sig.fors
        (schemeParts toy toyPrimitives (emptyContextMessage msg) sig pk).md.toList pk.pkSeed
        (schemeParts toy toyPrimitives (emptyContextMessage msg) sig pk).forsAdrs =
      forsPkGen toyPrimitives sk.skSeed pk.pkSeed
        (schemeParts toy toyPrimitives (emptyContextMessage msg) sig pk).forsAdrs :=
  forsArm_eq_true_iff pk sk msg sig

example : forsArm (vp := toy) toyPrimitives pk sk msg sig = false ↔
    forsPkFromSig toyPrimitives sig.fors
        (schemeParts toy toyPrimitives (emptyContextMessage msg) sig pk).md.toList pk.pkSeed
        (schemeParts toy toyPrimitives (emptyContextMessage msg) sig pk).forsAdrs ≠
      forsPkGen toyPrimitives sk.skSeed pk.pkSeed
        (schemeParts toy toyPrimitives (emptyContextMessage msg) sig pk).forsAdrs :=
  forsArm_eq_false_iff pk sk msg sig

example (h : forsArm (vp := toy) toyPrimitives pk sk msg sig = true) :
    findWitness sk.skSeed pk (emptyContextMessage msg) sig target =
      some (.fors (findForsWitness toyPrimitives sig.fors
        (schemeParts toy toyPrimitives (emptyContextMessage msg) sig pk).md.toList sk.skSeed
        pk.pkSeed
        (schemeParts toy toyPrimitives (emptyContextMessage msg) sig pk).forsAdrs target)) :=
  findWitness_eq_fors_of_forsArm pk sk msg sig target h

example (h : forsArm (vp := toy) toyPrimitives pk sk msg sig = false) :
    findWitness sk.skSeed pk (emptyContextMessage msg) sig target =
      (findHypertreeWitness toy toyPrimitives sk.skSeed pk.pkSeed
        (LayerPosition.initial toy (schemeParts toy toyPrimitives (emptyContextMessage msg) sig pk))
        toy.params.d (by simp)
        (forsPkFromSig toyPrimitives sig.fors
          (schemeParts toy toyPrimitives (emptyContextMessage msg) sig pk).md.toList pk.pkSeed
          (schemeParts toy toyPrimitives (emptyContextMessage msg) sig pk).forsAdrs)
        (forsPkGen toyPrimitives sk.skSeed pk.pkSeed
          (schemeParts toy toyPrimitives (emptyContextMessage msg) sig pk).forsAdrs)
        sig.hypertree).map .hypertree :=
  findWitness_eq_hypertree_of_forsArm pk sk msg sig target h

example {w : Witness toy toyPrimitives} (h : forsArm (vp := toy) toyPrimitives pk sk msg sig = true)
    (hw : findWitness sk.skSeed pk (emptyContextMessage msg) sig target = some w) :
    w = .fors (findForsWitness toyPrimitives sig.fors
      (schemeParts toy toyPrimitives (emptyContextMessage msg) sig pk).md.toList sk.skSeed
      pk.pkSeed
      (schemeParts toy toyPrimitives (emptyContextMessage msg) sig pk).forsAdrs target) :=
  witness_eq_fors_of_forsArm pk sk msg sig target h hw

example {w : Witness toy toyPrimitives}
    (h : forsArm (vp := toy) toyPrimitives pk sk msg sig = false)
    (hw : findWitness sk.skSeed pk (emptyContextMessage msg) sig target = some w) :
    ∃ u : HypertreeWitness toy toyPrimitives toyParams.d, w = .hypertree u :=
  exists_hypertree_witness_of_forsArm_eq_false pk sk msg sig target h hw

example (hkey : (pk, sk) ∈ support ((generalAlg (vp := toy) toyPrimitives).keygen))
    (hverify :
      GeneralScheme.verifyInternal toy toyPrimitives (emptyContextMessage msg) sig pk = true) :
    (findWitness sk.skSeed pk (emptyContextMessage msg) sig target).isSome :=
  findWitness_isSome_of_mem_support toyByteLaws hkey msg sig hverify target

example (hkey : (pk, sk) ∈ support ((generalAlg (vp := toy) toyPrimitives).keygen))
    (hverify :
      GeneralScheme.verifyInternal toy toyPrimitives (emptyContextMessage msg) sig pk = true) :
    ∃ w : Witness toy toyPrimitives,
      findWitness sk.skSeed pk (emptyContextMessage msg) sig target = some w ∧
        w.Valid sk.skSeed pk (emptyContextMessage msg) sig :=
  exists_witness_of_mem_support toyByteLaws hkey msg sig hverify target

noncomputable example : ℝ≥0∞ := forsHalf adv

noncomputable example : ℝ≥0∞ := hypertreeHalf adv

example : adv.advantage ProbCompRuntime.probComp ≤ forsHalf adv + hypertreeHalf adv :=
  advantage_le_forsHalf_add_hypertreeHalf adv

example : Function.Injective emptyContextMessage := emptyContextMessage_injective

example : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore toy toyPrimitives.core) :=
  internalLog log

example : internalLog log = log.map fun e => ⟨emptyContextMessage e.1, e.2⟩ := internalLog_eq log

example : loggedSignatures (internalLog log) (emptyContextMessage msg) =
    loggedSignatures log msg :=
  loggedSignatures_internalLog log msg

example : loggedRandomizers (internalLog log) (emptyContextMessage msg) =
    loggedRandomizers log msg :=
  loggedRandomizers_internalLog log msg

example : logQueries (internalLog log) =
    log.map fun e => (e.2.randomness, emptyContextMessage e.1) :=
  logQueries_internalLog log

example : SignatureAlg.signingLogContains (internalLog log) (emptyContextMessage msg) sig =
    SignatureAlg.signingLogContains log msg sig :=
  signingLogContains_internalLog log msg sig

example : Bool := randomizerLogged log msg sig

example : randomizerLogged log msg sig = true ↔ sig.randomness ∈ loggedRandomizers log msg :=
  randomizerLogged_eq_true_iff log msg sig

example : randomizerLogged log msg sig = false ↔ sig.randomness ∉ loggedRandomizers log msg :=
  randomizerLogged_eq_false_iff log msg sig

example (h : randomizerLogged log msg sig = false) :
    (sig.randomness, (⟨pk.pkSeed, pk.pkRoot, emptyContextMessage msg⟩ :
        HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y)) ∉
      embedTargets toyPrimitives pk.pkSeed pk.pkRoot (logQueries (internalLog log)) :=
  freshRandomizer_notMem_embedTargets pk h

example (h : randomizerLogged log msg sig = false) :
    (hmsgItsrProblem toyPrimitives).Wins
        (embedTargets toyPrimitives pk.pkSeed pk.pkRoot (logQueries (internalLog log)))
        (sig.randomness, ⟨pk.pkSeed, pk.pkRoot, emptyContextMessage msg⟩) ∨
      ∃ idx, findUncoveredIndex toyPrimitives
          (embedTargets toyPrimitives pk.pkSeed pk.pkRoot (logQueries (internalLog log)))
          (sig.randomness, ⟨pk.pkSeed, pk.pkRoot, emptyContextMessage msg⟩) = some idx ∧
        idx ∈ (hmsgItsrProblem toyPrimitives).indexSet
          (sig.randomness, ⟨pk.pkSeed, pk.pkRoot, emptyContextMessage msg⟩) ∧
        idx ∉ (hmsgItsrProblem toyPrimitives).targetIndexSet
          (embedTargets toyPrimitives pk.pkSeed pk.pkRoot (logQueries (internalLog log))) :=
  freshRandomizer_wins_or_uncovered (vp := toy) pk h

example (hfresh : SignatureAlg.signingLogContains log msg sig = false)
    (h : randomizerLogged log msg sig = true) :
    ∃ s ∈ loggedSignatures log msg, s.randomness = sig.randomness ∧ s ≠ sig ∧
      schemeParts toy toyPrimitives (emptyContextMessage msg) sig pk =
        schemeParts toy toyPrimitives (emptyContextMessage msg) s pk ∧
      (sig.fors ≠ s.fors ∨ sig.hypertree ≠ s.hypertree) :=
  sameRandomizer_of_randomizerLogged pk hfresh h

example (hfresh : SignatureAlg.signingLogContains log msg sig = false) :
    (sig.randomness, (⟨pk.pkSeed, pk.pkRoot, emptyContextMessage msg⟩ :
          HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y)) ∉
        embedTargets toyPrimitives pk.pkSeed pk.pkRoot (logQueries (internalLog log)) ∨
      ∃ s ∈ loggedSignatures log msg, s.randomness = sig.randomness ∧ s ≠ sig ∧
        schemeParts toy toyPrimitives (emptyContextMessage msg) sig pk =
          schemeParts toy toyPrimitives (emptyContextMessage msg) s pk ∧
        (sig.fors ≠ s.fors ∨ sig.hypertree ≠ s.hypertree) :=
  itsrFresh_or_sameRandomizer_external log msg sig pk hfresh

noncomputable example : ℝ≥0∞ := sameRandomizerHalf sadv

noncomputable example : ℝ≥0∞ := freshRandomizerHalf sadv

example : sadv.sameMessageAdvantage ProbCompRuntime.probComp ≤
    freshRandomizerHalf sadv + sameRandomizerHalf sadv :=
  sameMessageAdvantage_le_freshRandomizer_add_sameRandomizer sadv

example : sadv.advantage ProbCompRuntime.probComp =
    sadv.toUnforgeableAdv.advantage ProbCompRuntime.probComp +
      sadv.sameMessageAdvantage ProbCompRuntime.probComp :=
  strongAdvantage_eq_advantage_add_sameMessage sadv

example : sadv.advantage ProbCompRuntime.probComp ≤
    (forsHalf sadv.toUnforgeableAdv + hypertreeHalf sadv.toUnforgeableAdv) +
      (freshRandomizerHalf sadv + sameRandomizerHalf sadv) :=
  strongAdvantage_le_halves sadv

example : forsHalf adv ≤ adv.advantage ProbCompRuntime.probComp := forsHalf_le_advantage adv

example : hypertreeHalf adv ≤ adv.advantage ProbCompRuntime.probComp :=
  hypertreeHalf_le_advantage adv

example : sameRandomizerHalf sadv ≤ sadv.sameMessageAdvantage ProbCompRuntime.probComp :=
  sameRandomizerHalf_le_sameMessageAdvantage sadv

example : freshRandomizerHalf sadv ≤ sadv.sameMessageAdvantage ProbCompRuntime.probComp :=
  freshRandomizerHalf_le_sameMessageAdvantage sadv

end Pins

/-- Run the six check groups in order, then report. -/
def main : IO Unit := do
  checkFixture
  checkArmSelection
  checkInternalMessage
  checkInternalLog
  checkRandomizerLogged
  checkBranches
  IO.println "SLH-DSA scheme game tests: PASS"

end SLHDSA.SchemeGamesTest

/-- Entry point for `slhdsa_scheme_game_tests`. -/
def main : IO Unit := SLHDSA.SchemeGamesTest.main
