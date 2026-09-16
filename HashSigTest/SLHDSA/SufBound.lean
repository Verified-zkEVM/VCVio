/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.SufBound

/-!
# SLH-DSA strong-unforgeability residual canaries

Executable checks for the *decidable* shadow of the residual that
`HashSig.SLHDSA.Security.SufBound` carries — which branch of
`SchemeGames.randomizerLogged` a forgery lands in, at three signing logs — together with one
elaboration pin per exported declaration of that module and the vacuity canary its headline
inherits.

## Nothing about the bound itself is runnable, and that is a property of the subject

Every statement `HashSig.SLHDSA.Security.SufBound` exports is about a probability, and every
probability in it is `noncomputable`: the two advantages, both halves, the instrumented experiment
and `Summands.sufBound` alike.  So the headline, the two equivalences and the four bounds have **no
runtime coverage at all** and cannot be given any.  What the checks below read is the selector that
decides which of the two named halves a forgery contributes to, which is decidable because it is a
list membership; what pins the statements is the `Pins` section, and the matrix below records how
far that pinning reaches.

A reader of the lane's other fixtures will look for the headline among the runtime checks.  It is
not there, and no fixture could put it there.

## The profile is the lane's, copied rather than imported

The block below is the one `HashSigTest.SLHDSA.SchemeGames` builds — the same seven parameters, the
same six byte maps, the same three honest seeds, the same published root, the same three messages,
the same three signature `DecidableEq` instances and the same three logs — so the lane's executables
run on one profile and a reviewer can diff the blocks.  It is copied because a `lean_exe` root must
own its `main`, and a module that imports another fixture cannot declare one.

What this fixture holds, beyond that block: three forgeries — `forgeryEarly` and `forgeryLate`, a
second signature under each of the hedged log's two randomizers at one message, and `forgeryDet`,
the same at the deterministic variant's single randomizer; the misreading `randomizerLoggedRaw`; and
four instances the vacuity canary's `SLHDSA.Security.Certificate` asks for — `DecidableEq` on the
public seed and on the address key, `Fintype` and `Inhabited` on the node type.

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
* **Every reader against anything probabilistic.**  See above.

## What the checks cannot catch

* **A reordering or reassociation of `Summands.sufBound`'s two residuals that moves this file too.**
  Nothing outside these two files constrains the expression's order or its association.  Either edit
  made in the library module alone fails three entries here, but not the same three: the reordering
  fails three `Pins` entries, the reassociation two of those and the vacuity canary's own
  restatement of the refinement.  Made in both, nothing fails, and at that point the claim has been
  changed rather than a bug found.  A coefficient other than one on a residual and a stray additive
  constant are *not* in this class — the library refuses each on its own, at
  `sufBound_eq_bound_add_sameMessage_of_unfoldings` and, for the constant, at
  `sufBound_eq_bound_of_residuals_zero` as well.
* **Anything about a probability.**  See above.
* **Which of the two halves the consumption form bounds.**  The theorem
  `strongAdvantage_le_bound_add_sameRandomizer_of_fresh_le` takes a bound on the *fresh* half and
  leaves the same-randomizer one; the mirror statement is
  equally true and equally provable, so nothing inside the library module refuses the swap.  The pin
  here names `freshRandomizerHalf` in the hypothesis and refuses it; a paired edit moving this file
  too is silent, and the only remaining check is the argument in the module docstring for why the
  fresh branch is the one with somewhere to go.
* **Whether the residual's two branches are the source's.**  They are not: the source has no
  strong-unforgeability statement at all.  That is a reading of the eleven `.ec`/`.eca` files,
  recorded in the library module's docstring, and no fixture can check it.

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
of itself (9).  Nineteen `example`s in `Pins`: one for each of the fifteen declarations the
library module exports, plus three coefficient pins on the two residuals and the three-part shape
written out.  Then the vacuity canary: thirteen declarations copied from
`HashSigTest.SLHDSA.Composition` and four new ones, which put the strong-unforgeability headline at
the certificate that costs nothing and prove that what it bounds the advantage by is at least one.

## References

- NIST FIPS 205, §9.2 and Algorithm 19 (the hedged default and the deterministic alternative)
-/

public section

namespace SLHDSA.SufBoundTest

open Security Security.CanonicalGames KeyedHash OracleSpec TweakableHash SignatureAlg

/-- Throw on a failed check, naming it. -/
def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"SUF bound check failed: {label}")

/-! ## The profile -/

-- Exposed because `toyParams` has to reduce throughout this file: the nine instances written at the
-- bundle below need it both to typecheck and to compile, the two restatements of the vacuity canary
-- at this profile need `toy.params` to reduce to `toyParams`, and the definitions that read the
-- carrier need its width.
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

-- Exposed and `@[reducible]`, for two different reasons.  Exposed for code generation: the nine
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

/-- Public-seed equality, which the certificate's instance block asks for. -/
instance : DecidableEq toyPrimitives.PkSeed := inferInstanceAs (DecidableEq (Bytes 1))

/-- Tweak equality, which the collection games ask for. -/
instance : DecidableEq toyPrimitives.AdrsKey := inferInstanceAs (DecidableEq Adrs)

/-- The node type is finite, which the decisional reduction's advantage asks for. -/
instance : Fintype toyPrimitives.Y := inferInstanceAs (Fintype (Bytes 1))

/-- And inhabited, which the open-preimage game asks for. -/
instance : Inhabited toyPrimitives.Y := inferInstanceAs (Inhabited (Bytes 1))

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

One `example` for each of the fifteen declarations `HashSig.SLHDSA.Security.SufBound` exports,
restated at this bundle's own types, plus the shape pins on `Summands.sufBound`.  These are the only
thing that refuses a weakening of a statement: every statement in that module is about a
probability, so no `ensure` above can see any of them. -/

section Pins

open OracleComp ENNReal

variable (sadv : strongUnforgeableAdv (generalAlg (vp := toy) toyPrimitives))
  (c : Certificate (vp := toy) toyPrimitives sadv.toUnforgeableAdv) (s : Summands) (x y : ℝ≥0∞)

/-! ### The two arms -/

example (sel : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore toy toyPrimitives.core) →
      List Byte → GeneralScheme.SignatureCore toy toyPrimitives.core → Bool) :
    sadv.sameMessageAdvantage ProbCompRuntime.probComp =
      Pr[fun z => z.1 = true ∧ z.2 = false |
        instrumentedSameMessageExp ProbCompRuntime.probComp sadv sel] +
      Pr[fun z => z.1 = true ∧ z.2 = true |
        instrumentedSameMessageExp ProbCompRuntime.probComp sadv sel] :=
  sameMessageAdvantage_eq_arms ProbCompRuntime.probComp
    (fun f mx => ProbCompRuntime.probComp_evalSPMF_bind_pure f mx) sadv sel

example : sadv.sameMessageAdvantage ProbCompRuntime.probComp ≤ 1 :=
  sameMessageAdvantage_le_one ProbCompRuntime.probComp sadv

/-! ### The two equivalences -/

example :
    sadv.advantage ProbCompRuntime.probComp ≤
        x + sadv.sameMessageAdvantage ProbCompRuntime.probComp ↔
      sadv.toUnforgeableAdv.advantage ProbCompRuntime.probComp ≤ x :=
  strongAdvantage_le_add_sameMessage_iff sadv x

example (sel : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore toy toyPrimitives.core) →
      List Byte → GeneralScheme.SignatureCore toy toyPrimitives.core → Bool) :
    sadv.advantage ProbCompRuntime.probComp ≤ x +
        (Pr[fun z => z.1 = true ∧ z.2 = false |
            instrumentedSameMessageExp ProbCompRuntime.probComp sadv sel] +
          Pr[fun z => z.1 = true ∧ z.2 = true |
            instrumentedSameMessageExp ProbCompRuntime.probComp sadv sel]) ↔
      sadv.toUnforgeableAdv.advantage ProbCompRuntime.probComp ≤ x :=
  strongAdvantage_le_add_arms_iff sadv x sel

/-! ### The two halves under the strong advantage -/

example : freshRandomizerHalf sadv ≤ sadv.advantage ProbCompRuntime.probComp :=
  freshRandomizerHalf_le_strongAdvantage sadv

example : sameRandomizerHalf sadv ≤ sadv.advantage ProbCompRuntime.probComp :=
  sameRandomizerHalf_le_strongAdvantage sadv

/-! ### The bound expression -/

noncomputable example : ℝ≥0∞ := s.sufBound toyParams x y

example : s.sufBound toyParams x y = s.bound toyParams + (x + y) :=
  Summands.sufBound_eq s toyParams x y

example : s.sufBound toyParams 0 0 = s.bound toyParams :=
  sufBound_eq_bound_of_residuals_zero s toyParams

/-- The residuals carry coefficient one, each on its own: with the twelve summands zero the
expression is the residual. -/
example : (Summands.mk 0 0 0 0 0 0 0 0 0 0 0 0).sufBound toyParams x 0 = x := by
  rw [Summands.sufBound_eq, bound_eq_zero_of_summands_zero]
  simp

example : (Summands.mk 0 0 0 0 0 0 0 0 0 0 0 0).sufBound toyParams 0 y = y := by
  rw [Summands.sufBound_eq, bound_eq_zero_of_summands_zero]
  simp

example : (Summands.mk 0 0 0 0 0 0 0 0 0 0 0 0).sufBound toyParams x y = x + y := by
  rw [Summands.sufBound_eq, bound_eq_zero_of_summands_zero]
  simp

/-- The three-part shape written out: the twelve summands of the source expression, then the two
residuals as a group.  This is what refuses a residual attached inside the twelve. -/
example : s.sufBound toyParams x y =
    s.skgPrf + s.mkgPrf + s.hmsgItsr
      + s.forsFDspr + 3 * s.forsFTcr + s.forsHTcr + s.forsTlTcr
      + (toyParams.w - 2 : ℕ) * s.wotsFUd + s.wotsFTcr + s.wotsFPre + s.wotsTlTcr + s.xmssHTcr
      + (x + y) := by
  rw [Summands.sufBound_eq, Summands.bound_eq]

/-! ### The headline and its three companions -/

example : sadv.advantage ProbCompRuntime.probComp ≤
    c.summands.bound toy.params + sadv.sameMessageAdvantage ProbCompRuntime.probComp :=
  strongAdvantage_le_bound_add_sameMessage c

example (sel : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore toy toyPrimitives.core) →
      List Byte → GeneralScheme.SignatureCore toy toyPrimitives.core → Bool) :
    sadv.advantage ProbCompRuntime.probComp ≤ c.summands.bound toy.params +
      (Pr[fun z => z.1 = true ∧ z.2 = false |
          instrumentedSameMessageExp ProbCompRuntime.probComp sadv sel] +
        Pr[fun z => z.1 = true ∧ z.2 = true |
          instrumentedSameMessageExp ProbCompRuntime.probComp sadv sel]) :=
  strongAdvantage_le_bound_add_arms c sel

example : sadv.advantage ProbCompRuntime.probComp ≤
    c.summands.sufBound toy.params (freshRandomizerHalf sadv) (sameRandomizerHalf sadv) :=
  strongAdvantage_le_sufBound c

example (hfresh : freshRandomizerHalf sadv ≤ x) :
    sadv.advantage ProbCompRuntime.probComp ≤
      c.summands.bound toy.params + x + sameRandomizerHalf sadv :=
  strongAdvantage_le_bound_add_sameRandomizer_of_fresh_le c x hfresh

/-! ### The two halves at their defining equations

Both hypotheses below are `rfl` in the module that defines the halves and are not available here or
in the module under test, so these two pins are the only place in this file where a statement is
pinned at hypotheses nothing discharges. -/

example
    (hfresh : freshRandomizerHalf sadv =
      Pr[ fun z => z.1 = true ∧ z.2 = false |
        instrumentedSameMessageExp ProbCompRuntime.probComp sadv
          (randomizerLogged (vp := toy) (prims := toyPrimitives))])
    (hsame : sameRandomizerHalf sadv =
      Pr[ fun z => z.1 = true ∧ z.2 = true |
        instrumentedSameMessageExp ProbCompRuntime.probComp sadv
          (randomizerLogged (vp := toy) (prims := toyPrimitives))]) :
    sadv.sameMessageAdvantage ProbCompRuntime.probComp =
      freshRandomizerHalf sadv + sameRandomizerHalf sadv :=
  sameMessageAdvantage_eq_halves_of_unfoldings sadv hfresh hsame

example
    (hfresh : freshRandomizerHalf sadv =
      Pr[ fun z => z.1 = true ∧ z.2 = false |
        instrumentedSameMessageExp ProbCompRuntime.probComp sadv
          (randomizerLogged (vp := toy) (prims := toyPrimitives))])
    (hsame : sameRandomizerHalf sadv =
      Pr[ fun z => z.1 = true ∧ z.2 = true |
        instrumentedSameMessageExp ProbCompRuntime.probComp sadv
          (randomizerLogged (vp := toy) (prims := toyPrimitives))]) :
    s.sufBound toyParams (freshRandomizerHalf sadv) (sameRandomizerHalf sadv) =
      s.bound toyParams + sadv.sameMessageAdvantage ProbCompRuntime.probComp :=
  sufBound_eq_bound_add_sameMessage_of_unfoldings s toyParams sadv hfresh hsame

end Pins

/-! ## The vacuity canary

The composition fixture's vacuity canary, at this module's headline.  A closed
`SLHDSA.Security.Certificate` is constructible at an arbitrary validated parameter set, an arbitrary
bundle carrying the instances the structure asks for and an arbitrary adversary, from an address key
and a public seed and no security assumption at all, and the bound it names is at least one.  At
that certificate `strongAdvantage_le_bound_add_sameMessage` reads `sadv.advantage ≤ (something ≥ 1)
+ residual`, which `probOutput_le_one` gives with extra steps.

**The residual does not repair it and cannot.**  By `strongAdvantage_le_add_sameMessage_iff` the
headline is equivalent to the previous module's `advantage_le_bound` at the same certificate, so its
vacuity is that one's exactly.  The canary below is that equivalence instantiated: both conjuncts of
`freeCertificate_suf_headline` are proved, and the second is what makes the first empty.

**What this section holds.**  The free-certificate stack of `HashSigTest.SLHDSA.Composition` —
thirteen declarations: the two idle adversaries, the open-preimage adversary that records nothing
with its three advantage lemmas and its counting interface, the winning preimage adversary with its
inverse, and the certificate with the bound it names — together with `freeCertificate_suf_headline`
and `freeCertificate_sufBound_headline` at the end.  It is a copy rather than an import because that
module is a `lean_exe` root and declares a top-level `main`, which a module importing it cannot also
declare; the lane has no shared fixture module.  Every declaration in it is that module's verbatim,
but for the docstrings of the two statements named above.

That module's anchoring analysis — `winningOpenPre`, `anchoredCertificate` and
`nonempty_countingInterface_iff` — is not here: the question it answers is about `Certificate`'s own
fields and nothing about it changes when the residual is added. -/

section Vacuity

open OracleComp OracleSpec ENNReal SignatureAlg

/-! ### Adversaries that assume nothing

`idleTcr` and `idleUd` are here only to fill fields: nothing below reads their advantages. -/

/-- A target-collision adversary that forges nothing. -/
def idleTcr {ix PkS Tw Msg Nd : Type} [Inhabited Msg]
    (prob : SM_DT_TCR_SourceFinalValidity.Problem ix PkS Tw Msg Nd) :
    SM_DT_TCR_SourceFinalValidity.Adversary prob where
  State := Unit
  choose := pure ()
  forge := fun _ _ => pure (0, default)

/-- An undetectability adversary that always answers `false`. -/
def idleUd {ix PkS Tw Msg Msg' Nd : Type}
    (prob : SM_DT_UD_SourceFinalValidity.Problem ix PkS Tw Msg Msg' Nd) :
    SM_DT_UD_SourceFinalValidity.Adversary prob where
  State := Unit
  pick := pure ()
  distinguish := fun _ _ => pure false

-- Exposed, and the only one of the seven definitions in this section that needs to be.  Inside a
-- `public section` a definition's body is not available to later declarations, so without it
-- `(Problem.toDSPR (idleOpenPre prob)).State` does not reduce to `Unit × _ × _` and
-- `idleOpenPre_toDSPR_choose` cannot even be stated.
/-- An open-preimage adversary that commits to no target and opens nothing. -/
@[expose] def idleOpenPre {ix PkS Tw Msg Nd : Type} [Inhabited Msg]
    (prob : SM_DT_OpenPRE_SourceFinalValidity.Problem ix PkS Tw Msg Nd) :
    SM_DT_OpenPRE_SourceFinalValidity.Adversary prob where
  State := Unit
  pick := pure ((), [])
  find := fun _ _ _ => pure (0, default)

/-- It records no challenge, so the selected index misses and its advantage is zero. -/
theorem idleOpenPre_advantage {ix PkS Tw Msg Nd : Type} [DecidableEq Tw] [DecidableEq Nd]
    [Inhabited Msg] (prob : SM_DT_OpenPRE_SourceFinalValidity.Problem ix PkS Tw Msg Nd) :
    SM_DT_OpenPRE_SourceFinalValidity.Advantage (idleOpenPre prob) = 0 := by
  unfold SM_DT_OpenPRE_SourceFinalValidity.Advantage
    SM_DT_OpenPRE_SourceFinalValidity.Experiment
  simp [idleOpenPre, SM_DT_OpenPRE_SourceFinalValidity.initializeTargets,
    SourceFinalValidity.State.initial]

/-- The induced DSPR adversary's selection phase makes no challenge query either.  Stated
separately because the `do` block has to be reduced before the experiment can be. -/
theorem idleOpenPre_toDSPR_choose {ix PkS Tw Msg Nd : Type} [DecidableEq Msg] [Inhabited Msg]
    (prob : SM_DT_OpenPRE_SourceFinalValidity.Problem ix PkS Tw Msg Nd) :
    (SM_DT_OpenPRE_SourceFinalValidity.toDSPR (idleOpenPre prob)).choose = pure ((), [], []) := by
  change (do
      let __x ← (pure ((), []) :
        OracleComp (unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tw Msg Nd +
          SourceFinalValidity.collectionSpec prob.thColl)) (Unit × List Tw))
      let __x_1 ← SM_DT_OpenPRE_SourceFinalValidity.reductionInitialize prob
        (List.take prob.numTargets __x.2)
      pure (__x.1, __x_1)) = _
  rw [pure_bind]
  simp [SM_DT_OpenPRE_SourceFinalValidity.reductionInitialize]
  rfl

/-- So the induced DSPR advantage is zero: both its experiment and its `SPprob` baseline reject. -/
theorem idleOpenPre_dspr {ix PkS Tw Msg Nd : Type} [Fintype Msg] [DecidableEq Tw]
    [DecidableEq Msg] [DecidableEq Nd] [Inhabited Msg]
    (prob : SM_DT_OpenPRE_SourceFinalValidity.Problem ix PkS Tw Msg Nd) :
    SM_DT_DSPR_SourceFinalValidity.Advantage
      (SM_DT_OpenPRE_SourceFinalValidity.toDSPR (idleOpenPre prob)) = 0 := by
  unfold SM_DT_DSPR_SourceFinalValidity.Advantage SM_DT_DSPR_SourceFinalValidity.Success
    SM_DT_DSPR_SourceFinalValidity.SPProbability
    SM_DT_DSPR_SourceFinalValidity.Experiment SM_DT_DSPR_SourceFinalValidity.SPExperiment
  simp only [idleOpenPre_toDSPR_choose]
  simp [SM_DT_OpenPRE_SourceFinalValidity.toDSPR, idleOpenPre,
    SourceFinalValidity.State.initial]

/-- **The counting interface is inhabited from nothing.**  VCVio calls it "deliberately a proof
obligation, not a theorem supplied by this file"; at an adversary that records no target every
mass is zero, both decompositions read `0 = 0`, and the strata inequality reads `0 ≤ _`.  Its one
real input is `Problem.HasUniformInputs`, which `forsFOpenPreProblem_hasUniformInputs` proves. -/
noncomputable def idleCounting {ix PkS Tw Msg Nd : Type} [Fintype Msg] [DecidableEq Tw]
    [DecidableEq Msg] [DecidableEq Nd] [Inhabited Msg] [SampleableType Msg]
    {prob : SM_DT_OpenPRE_SourceFinalValidity.Problem ix PkS Tw Msg Nd}
    (h : prob.HasUniformInputs) :
    SM_DT_OpenPRE_SourceFinalValidity.CountingInterface (idleOpenPre prob) where
  uniformInputs := h
  singleMass := 0
  multipleMass := fun _ => 0
  openPRE_decomposition := by simp [idleOpenPre_advantage]
  dspr_decomposition := by
    simp [idleOpenPre_dspr, SM_DT_OpenPRE_SourceFinalValidity.reciprocalMass]
  tcr_strata_le := by simp [SM_DT_OpenPRE_SourceFinalValidity.collisionMass]


section Preimage

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  [SampleableType prims.PkSeed] [SampleableType prims.Y]
  [DecidableEq prims.AdrsKey] [DecidableEq prims.Y]

/-- Classical inversion of the WOTS+-`F` preimage game's attacked map. -/
noncomputable def wotsFPreInverse (pk : prims.PkSeed) (t : prims.AdrsKey) : prims.Y → prims.Y :=
  Function.invFun fun m =>
    (wotsFPreCProblem prims).th.eval pk t ((wotsFPreCProblem prims).emb m)

omit [DecidableEq prims.AdrsKey] [DecidableEq prims.Y] in
theorem wotsFPreInverse_eval (pk : prims.PkSeed) (t : prims.AdrsKey) (a : prims.Y) :
    (wotsFPreCProblem prims).th.eval pk t ((wotsFPreCProblem prims).emb
        (wotsFPreInverse prims pk t ((wotsFPreCProblem prims).th.eval pk t
          ((wotsFPreCProblem prims).emb a)))) =
      (wotsFPreCProblem prims).th.eval pk t ((wotsFPreCProblem prims).emb a) :=
  Function.invFun_eq (f := fun m =>
    (wotsFPreCProblem prims).th.eval pk t ((wotsFPreCProblem prims).emb m)) ⟨a, rfl⟩

/-- One challenge query, then classical inversion of the image it was answered with. -/
noncomputable def freePreAdv (t : prims.AdrsKey) :
    SM_DT_PRE_SourceFinalValidity.Adversary (wotsFPreCProblem prims) where
  State := prims.Y
  choose := liftM ((unifSpec +
    (SM_DT_PRE_SourceFinalValidity.challengeSpec prims.AdrsKey prims.Y +
      SourceFinalValidity.collectionSpec (wotsFPreCProblem prims).thColl)).query (.inr (.inl t)))
  invert := fun y pk => pure (0, wotsFPreInverse prims pk t y)

/-- **Preimage resistance is unconditionally false in this model**, at every validated parameter
set and every primitive bundle: the tenth summand of `Summands.bound` is exactly one here. -/
theorem freePreAdv_advantage (t : prims.AdrsKey) :
    SM_DT_PRE_SourceFinalValidity.Advantage (freePreAdv prims t) = 1 := by
  unfold SM_DT_PRE_SourceFinalValidity.Advantage SM_DT_PRE_SourceFinalValidity.Experiment
  simp [freePreAdv, wotsFPreInverse_eval, SM_DT_PRE_SourceFinalValidity.oracles,
    SM_DT_PRE_SourceFinalValidity.challengeOracle,
    SourceFinalValidity.State.recordTarget, SourceFinalValidity.State.initial,
    TweakableHash.TweakFresh, TweakableHash.TweakReserved,
    targetCount_pos vp.params vp.valid TargetRole.wotsFPre]

end Preimage

/-! ### The closed certificate -/

section Closed

variable {vp : ValidatedParams} {prims : Primitives vp.params}
  [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
  [SampleableType prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [DecidableEq prims.Y] [Fintype prims.Y] [Inhabited prims.Y]

/-- **A `Certificate` from nothing.**  The two arguments are an address key and a public seed,
which are data the scheme itself has and not assumptions.  `forsBranch := 0` puts the whole
obligation on `hypertreeBranch_le`, and `freePreAdv_advantage` discharges it. -/
noncomputable def freeCertificate {adv : unforgeableAdv (generalAlg prims)}
    (t : prims.AdrsKey) (pkSeed : prims.PkSeed) : Certificate prims adv where
  skgAdv := (pure true : OracleComp (PRFScheme.PRFOracleSpec Adrs prims.Y) Bool)
  mkgAdv := (pure true :
    OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) Bool)
  pkSeed := pkSeed
  itsrAdv := ⟨(pure (default, ⟨pkSeed, default, []⟩) :
    OracleComp (unifSpec + ITSRTargetSpec (HmsgITSRInput prims.PkSeed prims.Y) prims.Y)
      (prims.Y × HmsgITSRInput prims.PkSeed prims.Y))⟩
  openPreAdv := idleOpenPre (forsFOpenPreProblem prims)
  counting := idleCounting (forsFOpenPreProblem_hasUniformInputs prims)
  forsHAdv := idleTcr _
  forsTlAdv := idleTcr _
  wotsFUdAdv := idleUd _
  wotsFTcrAdv := idleTcr _
  wotsFPreAdv := freePreAdv prims t
  wotsTlAdv := idleTcr _
  xmssHAdv := idleTcr _
  idealAdvantage := adv.advantage ProbCompRuntime.probComp
  forsBranch := 0
  hypertreeBranch := adv.advantage ProbCompRuntime.probComp
  prfHops := le_add_self
  split := by simp
  forsBranch_le := by simp
  hypertreeBranch_le := by
    calc adv.advantage ProbCompRuntime.probComp ≤ 1 := probOutput_le_one
      _ = SM_DT_PRE_SourceFinalValidity.Advantage (freePreAdv prims t) :=
          (freePreAdv_advantage prims t).symm
      _ ≤ _ := le_add_right (le_add_right le_add_self)

/-- **The bound that certificate names is at least one**, so it is the trivial bound. -/
theorem one_le_freeCertificate_bound {adv : unforgeableAdv (generalAlg prims)}
    (t : prims.AdrsKey) (pkSeed : prims.PkSeed) :
    1 ≤ (freeCertificate (adv := adv) t pkSeed).summands.bound vp.params := by
  rw [Certificate.bound_eq]
  calc (1 : ℝ≥0∞) = SM_DT_PRE_SourceFinalValidity.Advantage (freePreAdv prims t) :=
        (freePreAdv_advantage prims t).symm
    _ ≤ _ := le_add_right (le_add_right le_add_self)

end Closed

/-- **The headline at that certificate.**  Both conjuncts together are the canary: the bound holds,
and what it bounds the strong advantage by is at least one — so the strong-unforgeability statement
of this module is, at this certificate, `probOutput_le_one` with extra steps, exactly as the
existential one is at the same certificate.

The residual is on the right-hand side of both conjuncts and changes neither. -/
theorem freeCertificate_suf_headline
    {vp : ValidatedParams} {prims : Primitives vp.params}
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
    [SampleableType prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
    [DecidableEq prims.Y] [Fintype prims.Y] [Inhabited prims.Y]
    {sadv : strongUnforgeableAdv (generalAlg prims)}
    (t : prims.AdrsKey) (pkSeed : prims.PkSeed) :
    sadv.advantage ProbCompRuntime.probComp ≤
        (freeCertificate (adv := sadv.toUnforgeableAdv) t pkSeed).summands.bound vp.params +
          sadv.sameMessageAdvantage ProbCompRuntime.probComp ∧
      1 ≤ (freeCertificate (adv := sadv.toUnforgeableAdv) t pkSeed).summands.bound vp.params +
          sadv.sameMessageAdvantage ProbCompRuntime.probComp :=
  ⟨strongAdvantage_le_bound_add_sameMessage _,
    le_trans (one_le_freeCertificate_bound t pkSeed) le_self_add⟩

/-- The same at the refinement through the two named halves, so that naming the same-randomizer term
is not mistaken for bounding it. -/
theorem freeCertificate_sufBound_headline
    {vp : ValidatedParams} {prims : Primitives vp.params}
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
    [SampleableType prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
    [DecidableEq prims.Y] [Fintype prims.Y] [Inhabited prims.Y]
    {sadv : strongUnforgeableAdv (generalAlg prims)}
    (t : prims.AdrsKey) (pkSeed : prims.PkSeed) :
    sadv.advantage ProbCompRuntime.probComp ≤
        (freeCertificate (adv := sadv.toUnforgeableAdv) t pkSeed).summands.sufBound vp.params
          (freshRandomizerHalf sadv) (sameRandomizerHalf sadv) ∧
      1 ≤ (freeCertificate (adv := sadv.toUnforgeableAdv) t pkSeed).summands.sufBound vp.params
          (freshRandomizerHalf sadv) (sameRandomizerHalf sadv) := by
  refine ⟨strongAdvantage_le_sufBound _, ?_⟩
  rw [Summands.sufBound_eq]
  exact le_trans (one_le_freeCertificate_bound t pkSeed) le_self_add

end Vacuity

/-! ### The same facts at this file's own bundle

The section above is at an arbitrary `ValidatedParams` and an arbitrary bundle; these restate the
two new statements at the profile the rest of this file uses, so a change that breaks only the
concrete case is caught too. -/

theorem toyFreeCertificateBound (t : Adrs) (pkSeed : toyPrimitives.PkSeed)
    (sadv : strongUnforgeableAdv (generalAlg (vp := toy) toyPrimitives)) :
    sadv.advantage ProbCompRuntime.probComp ≤
        (freeCertificate (vp := toy) (prims := toyPrimitives)
          (adv := sadv.toUnforgeableAdv) t pkSeed).summands.bound toy.params +
          sadv.sameMessageAdvantage ProbCompRuntime.probComp ∧
      1 ≤ (freeCertificate (vp := toy) (prims := toyPrimitives)
          (adv := sadv.toUnforgeableAdv) t pkSeed).summands.bound toy.params +
          sadv.sameMessageAdvantage ProbCompRuntime.probComp :=
  freeCertificate_suf_headline (vp := toy) (prims := toyPrimitives) (sadv := sadv) t pkSeed

theorem toyFreeCertificateSufBound (t : Adrs) (pkSeed : toyPrimitives.PkSeed)
    (sadv : strongUnforgeableAdv (generalAlg (vp := toy) toyPrimitives)) :
    sadv.advantage ProbCompRuntime.probComp ≤
        (freeCertificate (vp := toy) (prims := toyPrimitives)
          (adv := sadv.toUnforgeableAdv) t pkSeed).summands.sufBound toy.params
          (freshRandomizerHalf sadv) (sameRandomizerHalf sadv) ∧
      1 ≤ (freeCertificate (vp := toy) (prims := toyPrimitives)
          (adv := sadv.toUnforgeableAdv) t pkSeed).summands.sufBound toy.params
          (freshRandomizerHalf sadv) (sameRandomizerHalf sadv) :=
  freeCertificate_sufBound_headline (vp := toy) (prims := toyPrimitives) (sadv := sadv) t pkSeed

/-- Run the three check groups in order, then report. -/
def main : IO Unit := do
  checkBranch
  checkVariants
  checkLogs
  IO.println "SLH-DSA SUF bound tests: PASS"

end SLHDSA.SufBoundTest

/-- Entry point for `slhdsa_suf_bound_tests`. -/
def main : IO Unit := SLHDSA.SufBoundTest.main
