/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.SufPartition

/-!
# SLH-DSA strong-unforgeability residual canaries

Executable checks for the *decidable* shadow of the residual that
`HashSig.SLHDSA.Security.SufPartition` partitions — which branch of
`SchemeGames.randomizerLogged` a forgery lands in, at three signing logs — together with one
elaboration pin per exported declaration of that module.

Every statement that module exports is about a probability, and every probability in it is
`noncomputable`, so the two equivalences and the bounds on the two halves have no runtime coverage.
What the checks below read is the selector that decides which of the two named halves a forgery
contributes to, which is decidable because it is a list membership; what pins the statements is the
`Pins` section.

## The profile is the lane's, copied rather than imported

The block below is the one `HashSigTest.SLHDSA.SchemeGames` builds — the same seven parameters, the
same six byte maps, the same three honest seeds, the same published root, the same three messages,
the same three signature `DecidableEq` instances and the same three logs — so the lane's executables
run on one profile and a reviewer can diff the blocks.  It is copied because a `lean_exe` root must
own its `main`, and a module that imports another fixture cannot declare one.

What this fixture holds, beyond that block: three forgeries — `forgeryEarly` and `forgeryLate`, a
second signature under each of the hedged log's two randomizers at one message, and `forgeryDet`,
the same at the deterministic variant's single randomizer; and the misreading `randomizerLoggedRaw`.

Seven of that block's declarations are absent here, nothing below reading them: `byteFold` and
`toyByteLaws`, `otherPkSeed`, and the four dispatch-arm forgeries `sigD`, `sigE`, `sigH` and
`sigLate`.

## The reader-by-log matrix

Three readers and three logs.  L1 is the hedged log, three entries on two messages with the
twice-signed message's entries separated; L2 is the log FIPS 205 §9.2's deterministic variant would
produce for the same three queries; L3 is four entries, one message three times, with `sigP1`'s
randomizer at its tail rather than its head.

**R1**, `SchemeGames.randomizerLogged`, the residual's own selector.  A cell's catch is attributable
to the misreading and not to the substitution: the real reader, substituted under a misreading's
name, fires none of the thirty-two.

At **L1** it catches a reader that ignores the message — the cross forgery's randomizer is in the
log at the *other* message and must read `false` — and one that drops the log's head, since L1's
head is the only place any log here carries `sigP1`'s randomizer at `msgP`.  At **L2** it catches a
reader that reports membership only when a message carries two *distinct* randomizers: L2's list at
each message is constant and `forgeryDet` must still read `true`.  Across the three logs it catches
a reader that keeps only the first signature at a message, one that keeps only the last, and
truncation of the log to three entries, that last only in the group that reads the four-entry log.

**R2**, `SignatureAlg.signingLogContains`, the same-message experiment's own freshness conjunct.  At
**L1** it separates a forgery from the signature it shares a randomizer with: `forgeryEarly` reads
`false` where `sigP1` reads `true`.  At **L2** it does the same at the deterministic variant's own
signature.  It is not read at **L3**.

**R3**, `randomizerLoggedRaw`, the mutant that sweeps the whole log rather than the entries at this
message.  At **L1** it is separated from R1 at the cross forgery, and one further reading in this
file separates them as well: any forgery read at `msgU`, which no log carries, where the per-message
reader is `false` and the whole-log one is not.  At **L2** it is not separated: `forgeryDet`'s
randomizer occurs at `msgP` and nowhere else.  It is not read at **L3**.

**Cells that cannot discriminate, and why.**

* **R1 and R3 at L2 and L3.**  Both mutants differ from the real reader only in *which* entries of
  the log they collect, so a log separates them only when some randomizer occurs at one message and
  not at another.  L1 is the only log here in which that happens at a forgery this file carries.  A
  further log would separate them; none is added, because L1 already does and the matrix says so
  rather than leaving the other two cells looking covered.
* **R1 under reordering and de-duplication, at every log.**  R1 is `∈` on a list.  Membership is
  invariant under permutation and under `eraseDups`, so no log can make either visible: neither a
  reader that reverses the log nor one that collapses the per-message list to its distinct values is
  caught anywhere here.  This is the same structural blind spot `HashSigTest.SLHDSA.SufResidual`
  records for its own predicates, for the same reason; it is a property of the predicate and not a
  gap in the fixture.
* **R1 at L3 under a dropped head.**  L3's head pair recurs at its third entry, so dropping it
  changes nothing there.  L1 catches it; L3 does not.
* **Every reader against anything probabilistic.**  No probability is computable here.

## What the checks cannot catch

* **Anything about a probability.**  No probability is computable here.
* **Whether the residual's two branches are the source's.**  They are not: the EasyCrypt
  development has no strong-unforgeability statement at all.  That is a reading of its eleven
  `.ec`/`.eca` files, recorded in the library module's docstring, and no fixture can check it.

## The deterministic-variant boundary this fixture exercises

`HashSig.SLHDSA.Security.SufResidual` states that deterministic signing narrows the
same-randomizer branch without emptying it.  `checkVariants` exercises that boundary:
`forgeryDet` reuses the single randomizer L2 carries at `msgP`, is not itself in L2, and reads
`true`.  Reusing the randomizer costs an adversary nothing — it is a field of the signature it was
handed — so the branch is inhabited under either variant.  What the hedged default changes is the
*size* of the logged-randomizer list at a message, and therefore how hard the **fresh** branch is to
reach: the same checks put `forgeryLate` on the logged branch at L1 and on the fresh branch at L2.

## What is here

Thirty-two runtime checks in three groups — the branch each forgery lands in at the hedged log (13),
what the two FIPS 205 §9.2 variants change (10), and the reader at a longer log and against a mutant
of itself (9) — and the `Pins` section.

## References

- NIST FIPS 205, §9.2 and Algorithm 19 (the hedged default and the deterministic alternative)
-/

public section

namespace SLHDSA.SufPartitionTest

open Security Security.CanonicalGames KeyedHash OracleSpec TweakableHash SignatureAlg

/-- Throw on a failed check, naming it. -/
def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"SUF bound check failed: {label}")

/-! ## The profile -/

-- Exposed because `toyParams` has to reduce throughout this file: the five instances written at the
-- bundle below need it both to typecheck and to compile, and the definitions that read the carrier
-- need its width.
/-- Two layers of height two, two FORS trees of height one. -/
@[expose] def toyParams : Params :=
  { n := 1, h := 4, d := 2, hp := 2, a := 1, k := 2, lgw := 4 }

/-- The toy parameters are valid. -/
theorem toyValid : toyParams.Valid := by decide

-- Exposed because the three signature `DecidableEq` instances below are stated at `toy.params` and
-- every signature, log and forgery this file builds is at `toy`, so `toy.params` has to reduce to
-- `toyParams` for those instances to apply.  Without the body, instance search does not merely fail
-- on those goals but runs to the heartbeat limit on some of them.
/-- The validated form of `toyParams`. -/
@[expose] def toy : ValidatedParams := ⟨toyParams, toyValid⟩

/-- A nonlinear byte mix. -/
def mixByte (x : UInt8) : UInt8 := ((x * (181 : UInt8)) ^^^ (x >>> (3 : UInt8))) + 97

/-- The fold this bundle's `H_msg` and `PRF_msg` read a message through. -/
def byteMix (m : List Byte) : UInt8 :=
  m.foldl (fun acc b => mixByte (acc ^^^ b)) (UInt8.ofNat (m.length % 256))

/-- The per-address secret values the toy `PRF` hands out. -/
def toySecret (seed sk : UInt8) (a : Adrs) : UInt8 :=
  UInt8.ofNat ((seed.toNat * 19 + sk.toNat * 23 + a.layer * 101 + a.tree * 53 + a.type * 61 +
    a.word1 * 37 + a.word2 * 11 + a.word3 * 7 + 5) % 256)

/-- A per-address byte mixed into every `Thash` output. -/
def toyTweak (seed : UInt8) (a : Adrs) : UInt8 :=
  UInt8.ofNat ((seed.toNat * 17 + a.layer * 131 + a.tree * 71 + a.type * 41 + a.word1 * 29 +
    a.word2 * 43 + a.word3 * 97) % 256)

/-- The toy `PRF_msg`: the message randomizer FIPS 205 Algorithm 19 line 3 derives.  It reads the
per-signature `addrnd`, which is what makes the hedged and deterministic variants differ here. -/
def toyRandomizer (skPrf addrnd : UInt8) (msg : List Byte) : UInt8 :=
  mixByte (UInt8.ofNat
    ((skPrf.toNat * 13 + addrnd.toNat * 47 + (byteMix msg).toNat * 5 + 1) % 256))

/-- Byte `i` of the toy `H_msg` digest. -/
def toyDigestByte (r seed root : UInt8) (msg : List Byte) (i : ℕ) : UInt8 :=
  mixByte (UInt8.ofNat ((r.toNat * (6 * i + 37) + seed.toNat * (10 * i + 53) +
    root.toNat * (14 * i + 89) + (byteMix msg).toNat * (22 * i + 149) + (30 * i + 7)) % 256))

-- Exposed and `@[reducible]`, for two different reasons.  Exposed for code generation: the five
-- instances just below and the three signature-equality instances after them have to infer the same
-- compilation type for this bundle as an importing module would, which needs its body.  Reducible
-- because the carrier has to unfold to `Bytes 1` for instance resolution to reach it: `byteOf`'s
-- `y[0]` needs `GetElem toyPrimitives.Y ℕ` and the index bound that follows from it.
/-- The toy bundle. -/
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

/-- A one-byte node. -/
def node (x : UInt8) : toyPrimitives.Y := Vector.replicate 1 x

/-- The byte inside a node. -/
def byteOf (y : toyPrimitives.Y) : UInt8 := y[0]

/-- The honest secret seed. -/
def skSeed : toyPrimitives.SkSeed := node 0x11

/-- The honest message-PRF key. -/
def skPrf : toyPrimitives.SkPrf := node 0x22

/-- The honest public seed. -/
def pkSeed : toyPrimitives.PkSeed := node 0x33

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

/-- Signature equality, field by field. -/
instance : DecidableEq (GeneralScheme.SignatureCore toy toyPrimitives.core) := fun a b =>
  decidable_of_iff (a.randomness = b.randomness ∧ a.fors = b.fors ∧ a.hypertree = b.hypertree)
    ⟨fun h => by
      cases a; cases b; simp only at h
      obtain ⟨h1, h2, h3⟩ := h; subst h1; subst h2; subst h3; rfl,
     fun h => h ▸ ⟨rfl, rfl, rfl⟩⟩

/-! ## Messages, honest signatures and the three logs -/

/-- The message signed twice. -/
def msgP : List Byte := [0x01, 0x02]

/-- A second signed message. -/
def msgQ : List Byte := [0x05]

/-- A message no log carries. -/
def msgU : List Byte := [0x07, 0x09]

/-- The honest signature on the external message `msg`, under `addrnd`. -/
def honestSig (msg : List Byte) (addrnd : UInt8) :
    GeneralScheme.SignatureCore toy toyPrimitives.core :=
  GeneralScheme.signInternal toy toyPrimitives (emptyContextMessage msg) secretKey (node addrnd)

/-- The first honest signature on `msgP`. -/
def sigP1 : GeneralScheme.SignatureCore toy toyPrimitives.core := honestSig msgP 0x41

/-- The second honest signature on `msgP`, under a different `addrnd`. -/
def sigP2 : GeneralScheme.SignatureCore toy toyPrimitives.core := honestSig msgP 0x42

/-- The honest signature on `msgQ`. -/
def sigQ : GeneralScheme.SignatureCore toy toyPrimitives.core := honestSig msgQ 0x43

/-- FIPS 205 §9.2's deterministic variant on `msgP`: `opt_rand` is `PK.seed`. -/
def detSigP : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  GeneralScheme.signInternal toy toyPrimitives (emptyContextMessage msgP) secretKey pkSeed

/-- The same variant on `msgQ`. -/
def detSigQ : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  GeneralScheme.signInternal toy toyPrimitives (emptyContextMessage msgQ) secretKey pkSeed

/-- **L1, the hedged log.**  The `msgQ` entry separates the two `msgP` entries. -/
def signingLog : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore toy toyPrimitives.core) :=
  [⟨msgP, sigP1⟩, ⟨msgQ, sigQ⟩, ⟨msgP, sigP2⟩]

/-- **L2, the deterministic log.**  The same three queries under FIPS 205 §9.2's deterministic
variant: one randomizer per message. -/
def deterministicLog :
    QueryLog (List Byte →ₒ GeneralScheme.SignatureCore toy toyPrimitives.core) :=
  [⟨msgP, detSigP⟩, ⟨msgQ, detSigQ⟩, ⟨msgP, detSigP⟩]

/-- **L3, the four-entry log.**  One message three times, one entry repeated, and `sigP1`'s
randomizer at its tail rather than its head. -/
def thriceSignedLog :
    QueryLog (List Byte →ₒ GeneralScheme.SignatureCore toy toyPrimitives.core) :=
  [⟨msgP, detSigP⟩, ⟨msgQ, detSigQ⟩, ⟨msgP, detSigP⟩, ⟨msgP, sigP1⟩]

/-! ## The forgeries -/

/-- A second signature under the same randomizer: `sigP1` with one revealed FORS value moved.  Its
exact pair is not in any log here, and its randomizer is `sigP1`'s. -/
def forgeryEarly : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  { sigP1 with fors := sigP1.fors.set 0 { sigP1.fors[0] with
      sk := node (byteOf sigP1.fors[0].sk + 1) } }

/-- The same, at the *second* logged signature on `msgP`: a reading that kept only the first entry
at a message would call it fresh. -/
def forgeryLate : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  { sigP2 with fors := sigP2.fors.set 0 { sigP2.fors[0] with
      sk := node (byteOf sigP2.fors[0].sk + 1) } }

/-- The same, at the deterministic variant's signature: the same-randomizer branch's witness at a
log that carries one randomizer per message. -/
def forgeryDet : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  { detSigP with fors := detSigP.fors.set 0 { detSigP.fors[0] with
      sk := node (byteOf detSigP.fors[0].sk + 1) } }

/-- A forgery on `msgP` under randomness no log carries. -/
def forgeryFresh : GeneralScheme.SignatureCore toy toyPrimitives.core := honestSig msgP 0x51

/-- A forgery on `msgP` carrying the randomizer the log recorded at `msgQ`: in the log, but not at
this message. -/
def forgeryCross : GeneralScheme.SignatureCore toy toyPrimitives.core :=
  { sigP1 with randomness := sigQ.randomness }

/-- The mutant reader this file offers `randomizerLogged` against: membership in the randomizers of
the *whole* log rather than of the log at this message. -/
def randomizerLoggedRaw
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore toy toyPrimitives.core))
    (sig : GeneralScheme.SignatureCore toy toyPrimitives.core) : Bool :=
  decide (sig.randomness ∈ log.map fun e => e.2.randomness)

/-! ## The checks -/

/-- **Which branch of the residual each forgery lands in, at the hedged log.**  The selector
`SchemeGames.randomizerLogged` is the `by_cases` of `SufResidual.itsrFresh_or_sameRandomizer`, and
its `true` branch is the *same-randomizer* one, because it reports membership.  Each forgery below
is asserted to satisfy the same-message experiment's own freshness conjunct first — its exact pair
is not in the log — because without that the branch reading is a reading of a logged signature and
not of a forgery.  The logged signature itself is asserted to fail that conjunct, which is what
keeps it out of the event.  Thirteen properties. -/
def checkBranch : IO Unit := do
  ensure "a forgery under fresh randomness is on the fresh branch"
    (randomizerLogged signingLog msgP forgeryFresh == false)
  ensure "a forgery carrying the other message's randomizer is on the fresh branch here"
    (randomizerLogged signingLog msgP forgeryCross == false)
  ensure "and on the logged branch at that other message, so the reader is per message"
    (randomizerLogged signingLog msgQ forgeryCross == true)
  ensure "a second signature under the first logged randomizer is on the logged branch"
    (randomizerLogged signingLog msgP forgeryEarly == true)
  ensure "and so is one under the second, which a reader keeping only the first would miss"
    (randomizerLogged signingLog msgP forgeryLate == true)
  ensure "at a message the log never carries, every forgery is on the fresh branch"
    (randomizerLogged signingLog msgU forgeryEarly == false)
  ensure "the fresh-randomness forgery satisfies the freshness conjunct"
    (signingLogContains signingLog msgP forgeryFresh == false)
  ensure "so does the cross-message one"
    (signingLogContains signingLog msgP forgeryCross == false)
  ensure "so does the first same-randomizer one"
    (signingLogContains signingLog msgP forgeryEarly == false)
  ensure "so does the second"
    (signingLogContains signingLog msgP forgeryLate == false)
  ensure "while the logged signature itself does not, which excludes it from the event"
    (signingLogContains signingLog msgP sigP1 == true)
  ensure "the same-randomizer forgery differs from the signature it shares a randomizer with"
    (forgeryEarly != sigP1 && forgeryLate != sigP2)
  ensure "and shares exactly that randomizer"
    (forgeryEarly.randomness == sigP1.randomness && forgeryLate.randomness == sigP2.randomness)

/-- **What FIPS 205 §9.2's two variants change, and what they do not.**  The hedged default samples
`opt_rand` per signature, so a twice-signed message carries two randomizers; the deterministic
variant sets `opt_rand ← PK.seed` and leaves one, which is the shape the EasyCrypt development's
message-keyed signer has.

What that changes is the *size* of the logged-randomizer list at a message, and therefore how hard
the fresh branch is to reach: `forgeryLate` is on the logged branch at the hedged log and on the
fresh branch at the deterministic one.  What it does **not** change is whether the logged branch is
inhabited: `forgeryDet` reuses the deterministic log's single randomizer and is not itself in that
log, so it is on the logged branch there.  Reusing the randomizer costs an adversary nothing, since
it is a field of the signature it was handed.  These checks exercise
`HashSig.SLHDSA.Security.SufResidual`'s statement that the deterministic variant narrows the
second branch without emptying it.  Ten properties. -/
def checkVariants : IO Unit := do
  ensure "the deterministic log's own second signature is on its logged branch"
    (randomizerLogged deterministicLog msgP forgeryDet == true)
  ensure "and it satisfies the freshness conjunct, so the branch is inhabited there"
    (signingLogContains deterministicLog msgP forgeryDet == false)
  ensure "and it differs from the signature it shares that randomizer with"
    (forgeryDet != detSigP && forgeryDet.randomness == detSigP.randomness)
  ensure "a hedged forgery is on the fresh branch at the deterministic log"
    (randomizerLogged deterministicLog msgP forgeryEarly == false &&
      randomizerLogged deterministicLog msgP forgeryLate == false)
  ensure "and the deterministic forgery is on the fresh branch at the hedged log"
    (randomizerLogged signingLog msgP forgeryDet == false)
  ensure "the deterministic variant's two queries on one message are one signature"
    (loggedSignatures deterministicLog msgP == [detSigP, detSigP])
  ensure "so its log carries one randomizer at that message"
    ((loggedRandomizers deterministicLog msgP).eraseDups.length == 1)
  ensure "while the hedged log carries two"
    ((loggedRandomizers signingLog msgP).eraseDups.length == 2)
  ensure "both logs record the same number of queries at that message"
    ((loggedRandomizers deterministicLog msgP).length ==
      (loggedRandomizers signingLog msgP).length)
  ensure "and the deterministic randomizer is neither hedged one"
    (detSigP.randomness != sigP1.randomness && detSigP.randomness != sigP2.randomness)

/-- **The reader at a longer log, and against a mutant of itself.**  `randomizerLoggedRaw` sweeps
the whole log instead of the entries at this message; it is the single most plausible weakening of
the selector, because the message argument is the only thing that makes the branch a *pair*
condition.  L1 separates the two at `forgeryCross` and no log here separates them anywhere else,
which is stated rather than left implicit.

L3 is the only log that signs one message three times.  Dropping its head leaves `forgeryEarly` on
the logged branch, because L3 carries `sigP1` at its tail as well; L1's head is the only place any
log here carries that randomizer at `msgP`, so L1 is the log that catches a head-dropping reader
and L3 is not.  Nine properties. -/
def checkLogs : IO Unit := do
  ensure "the four-entry log lists three signatures at the thrice-signed message"
    ((loggedRandomizers thriceSignedLog msgP).length == 3)
  ensure "carrying two distinct randomizers"
    ((loggedRandomizers thriceSignedLog msgP).eraseDups.length == 2)
  ensure "the same-randomizer forgery is on its logged branch"
    (randomizerLogged thriceSignedLog msgP forgeryEarly == true)
  ensure "dropping the four-entry log's head does not move it, because that log repeats"
    (randomizerLogged thriceSignedLog.tail msgP forgeryEarly == true)
  ensure "dropping the hedged log's head does move it, which is the log that catches that reader"
    (randomizerLogged signingLog.tail msgP forgeryEarly == false)
  ensure "the whole-log reader disagrees with the per-message one at the cross-message forgery"
    (randomizerLoggedRaw signingLog forgeryCross != randomizerLogged signingLog msgP forgeryCross)
  ensure "it agrees at a forgery under fresh randomness"
    (randomizerLoggedRaw signingLog forgeryFresh == randomizerLogged signingLog msgP forgeryFresh)
  ensure "and at the deterministic log's own second signature, where nothing separates them"
    (randomizerLoggedRaw deterministicLog forgeryDet ==
      randomizerLogged deterministicLog msgP forgeryDet)
  ensure "the deterministic log's transcript still records both queries at that message"
    (logQueries deterministicLog ==
      [(detSigP.randomness, msgP), (detSigQ.randomness, msgQ), (detSigP.randomness, msgP)])

/-! ## The pins

One `example` for each declaration `HashSig.SLHDSA.Security.SufPartition` exports, restated at this
bundle's own types.  These are the only thing that refuses a weakening of a statement: every
statement in that module is about a probability, so no `ensure` above can see any of them. -/

section Pins

open OracleComp ENNReal

variable (sadv : StrongUnforgeableAdversary (generalAlg (vp := toy) toyPrimitives)) (x : ℝ≥0∞)

/-! ### The two arms -/

example (sel : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore toy toyPrimitives.core) →
      List Byte → GeneralScheme.SignatureCore toy toyPrimitives.core → Bool) :
    sameMessageStrongUnforgeableAdvantage ProbCompRuntime.probComp sadv =
      𝒟[instrumentedSameMessageExperiment sadv sel]
        {z | z.1 = true ∧ z.2 = false} +
      𝒟[instrumentedSameMessageExperiment sadv sel]
        {z | z.1 = true ∧ z.2 = true} :=
  sameMessageAdvantage_eq_arms ProbCompRuntime.probComp
    sadv sel

example : sameMessageStrongUnforgeableAdvantage ProbCompRuntime.probComp sadv ≤ 1 :=
  sameMessageAdvantage_le_one ProbCompRuntime.probComp sadv

/-! ### The two equivalences -/

example :
    strongUnforgeableAdvantage ProbCompRuntime.probComp sadv ≤
        x + sameMessageStrongUnforgeableAdvantage ProbCompRuntime.probComp sadv ↔
      unforgeableAdvantage ProbCompRuntime.probComp sadv.toUnforgeableAdversary ≤ x :=
  strongAdvantage_le_add_sameMessage_iff sadv x

example (sel : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore toy toyPrimitives.core) →
      List Byte → GeneralScheme.SignatureCore toy toyPrimitives.core → Bool) :
    strongUnforgeableAdvantage ProbCompRuntime.probComp sadv ≤ x +
        (𝒟[instrumentedSameMessageExperiment sadv sel]
          {z | z.1 = true ∧ z.2 = false} +
          𝒟[instrumentedSameMessageExperiment sadv sel]
            {z | z.1 = true ∧ z.2 = true}) ↔
      unforgeableAdvantage ProbCompRuntime.probComp sadv.toUnforgeableAdversary ≤ x :=
  strongAdvantage_le_add_arms_iff sadv x sel

/-! ### The two halves under the strong advantage -/

example : freshRandomizerHalf sadv ≤ strongUnforgeableAdvantage ProbCompRuntime.probComp sadv :=
  freshRandomizerHalf_le_strongAdvantage sadv

example : sameRandomizerHalf sadv ≤ strongUnforgeableAdvantage ProbCompRuntime.probComp sadv :=
  sameRandomizerHalf_le_strongAdvantage sadv

/-! ### Exact randomizer partition -/

example : sameMessageStrongUnforgeableAdvantage ProbCompRuntime.probComp sadv =
    freshRandomizerHalf sadv + sameRandomizerHalf sadv :=
  sameMessageAdvantage_eq_freshRandomizerHalf_add_sameRandomizerHalf sadv

end Pins

/-- Run the three check groups in order, then report. -/
def main : IO Unit := do
  checkBranch
  checkVariants
  checkLogs
  IO.println "SLH-DSA SUF partition tests: PASS"

end SLHDSA.SufPartitionTest

/-- Entry point for `slhdsa_suf_partition_tests`. -/
def main : IO Unit := SLHDSA.SufPartitionTest.main
