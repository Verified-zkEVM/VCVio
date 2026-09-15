/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.LimitedProfile

/-!
# SLH-DSA-SHA2-128-24 profile canaries

Executable checks for the *decidable* data that `HashSig.SLHDSA.Security.LimitedProfile`'s
corollaries are stated at — the reduced profile's parameters, the undetectability coefficient it
turns into a numeral, and the eight target caps — together with one elaboration pin per exported
declaration of that module, the ten games' caps read at the concrete bundle, and the vacuity the
corollaries inherit.

## Nothing about the corollaries is runnable, and that is a property of the subject

Every statement `HashSig.SLHDSA.Security.LimitedProfile` exports about a probability is
`noncomputable`, as it is in the two modules it instantiates: the advantages, both halves of the
residual, and the bound expression alike.  So the two headlines have **no runtime coverage at all**
and cannot be given any.  What runs below is `Params`-level arithmetic — the profile's seven
parameters and their derived values, `SLHDSA.Security.targetCount` at the eight roles, and a
twelve-row summand table this file writes down and checks against that function.  What pins the
corollaries themselves is the `Pins` section; what pins their strength is the canary at the end,
which is elaboration-only for the same reason.

## What the profile adds to the two general modules, and what it does not

`slhdsaSha2_128_24` is `n = 16`, `h = 22`, `d = 1`, `hp = 22`, `a = 24`, `k = 6`, `lgw = 2`; the
bundle is `Concrete.sha2Primitives` at it.  Instantiating discharges nine carrier instances, turns
`(p.w - 2 : ℕ)` into `2`, and turns eight caps into numerals.  It changes nothing about the
`Certificate` hypothesis, and the canary at the end is that sentence as a checked fact: the
free-certificate construction of `HashSigTest.SLHDSA.Composition`, carried through
`HashSigTest.SLHDSA.SufBound`, is rebuilt here and applied at this bundle, so
`limitedAdvantage_le_bound` at the certificate it returns bounds the advantage by something at
least one.

## The two cells that go dark at this profile, both asserted rather than hidden

* **The two `T_ℓ` compressions.**  `forsTlTcrCProblem` and `wotsTlTcrCProblem` are both
  target-collision games on the shared `Thash` collection, and at `d = 1` their caps coincide —
  `2 ^ 22` here.  A cap check alone therefore cannot tell them apart at the profile the
  corollaries use.  What does is the arity, `p.k = 6` against `p.len = 68`; the runtime table
  carries the arity beside the cap, and `Pins` reads it off the two games' own attacked-member
  equations, where the message type is `Vector limitedPrimitives.Y 6` in one and
  `Vector limitedPrimitives.Y 68` in the other.  `HashSigTest.SLHDSA.Composition` proves the cap
  coincidence general at `d = 1` and the strict separation general at `2 ≤ d`.
* **The WOTS+-`F` undetectability and preimage roles.**  `targetCount` gives both
  `wotsInstanceCount p * p.len`, at *every* parameter set and not only this one — asserted below
  as an `example` over an arbitrary `p`.  Their arities coincide too, both being the single-node
  chain hash.  So neither a cap nor an arity can separate those two rows, and what does is the
  game: the eighth summand is an undetectability advantage and the tenth a preimage advantage,
  which is a fact about the two `Certificate` fields' types and is pinned in `Pins`.

## What is here

Fifty-two runtime checks in five groups — the profile's seven parameters and the sizes they derive
(19), the eight caps and the two structural counts at `d = 1` (10), four arithmetic relations
between the caps (5), the two dark cells (7), and the summand table checked against `targetCount`
(11).  Fifty-four `example`s in `Pins`: one for each of the thirty-four declarations the library
module exports, the five carriers its instances are stated at, the ten games' caps at this bundle,
the two `T_ℓ` games' arities, the general coincidence of the two WOTS+-`F` caps, and the two
certificate fields whose types are all that separates them.  Then the vacuity canary — fifteen
declarations copied from `HashSigTest.SLHDSA.SufBound` and four restatements at this bundle.

## What the checks cannot catch

* **Anything about a probability.**  See above.
* **A paired edit of the `w − 2` coefficient — though not the one the general fixture
  records.**  At this profile the numeral is not a free choice:
  `limitedParams_wotsFUd_coefficient` is `rfl` against the parameter set, so changing `2` in that
  equation, in the two written-out corollaries,
  or in all three at once is refused by the library module itself, with three, one and two errors
  respectively.  What is silent is the *general* edit `HashSigTest.SLHDSA.Composition` measures:
  change `Summands.bound`'s expression there, its fixture with it, and this module's equation to
  match, and everything here is provable again with a different numeral.  So what this file adds
  is a numeral that has to agree with the parameter set, and not a check on the shape of `w − 2`,
  which the source citation in the general module is still the only thing that checks.
* **Whether the twelve summands are the source's.**  A reading of the EasyCrypt development,
  recorded in `HashSig.SLHDSA.Security.Composition`'s docstring, and no fixture can check it.
* **Whether this bundle is the one anyone executes.**  It is not:
  `HashSigTest.SLHDSA.Sha2KAT` runs `Concrete.shaPrimitives`, a different term, which the library
  module's docstring records and nothing here or there relates to this one.
* **The strength of the certificate.**  The canary exhibits one certificate; it does not show that
  every certificate is free, and `HashSigTest.SLHDSA.Composition` records what anchoring the three
  `ℝ≥0∞` fields would and would not refuse.  That analysis is not restated here.

## References

- NIST SP 800-230 (initial public draft) for the reduced `SLH-DSA-SHA2-128-24` profile
- NIST FIPS 205, §11 for the parameter sets
-/

public section

namespace SLHDSA.LimitedProfileTest

open Security Security.CanonicalGames KeyedHash OracleSpec TweakableHash SignatureAlg

/-- Throw on a failed check, naming it. -/
def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"Limited profile check failed: {label}")

/-! ## The profile, under this file's own names

`p` is the library module's `limitedVp.params`, which is `SLHDSA.slhdsaSha2_128_24`; the
abbreviation is local convenience and `Pins` restates the identity. -/

/-- The SP 800-230 reduced parameter set. -/
abbrev p : Params := Security.limitedVp.params

/-! ## The summand table

One row per summand of `SLHDSA.Security.Summands`, in the source's order: the field name, the
`TargetRole` whose `targetCount` caps the game the summand is the advantage of, that cap *at this
profile* as a numeral, and the arity of the hash the game attacks.  Three rows have no role — the
two `PRF` hops, which are not tweakable-hash games at all, and the `H_msg` ITSR term, whose game
has no target cap of any kind.  The caps are checked against `targetCount` below rather than only
being written here. -/

/-- A summand row: the field name, its game's cap role, that cap at this profile, and the arity of
the attacked hash. -/
structure SummandRow where
  /-- The field name of `SLHDSA.Security.Summands` this row is about. -/
  summand : String
  /-- The `TargetRole` capping the game, where the game has one. -/
  role : Option TargetRole
  /-- The cap at this profile, where the game has one. -/
  cap : Option ℕ
  /-- The arity of the attacked hash, where the summand is a tweakable-hash game. -/
  arity : Option ℕ
  deriving Repr

/-- The twelve summands at SLH-DSA-SHA2-128-24. -/
def summands : List SummandRow :=
  [ ⟨"skgPrf", none, none, none⟩,
    ⟨"mkgPrf", none, none, none⟩,
    ⟨"hmsgItsr", none, none, none⟩,
    ⟨"forsFDspr", some .forsF, some (6 * 2 ^ 46), some 1⟩,
    ⟨"forsFTcr", some .forsF, some (6 * 2 ^ 46), some 1⟩,
    ⟨"forsHTcr", some .forsH, some (2 ^ 22 * 6 * (2 ^ 24 - 1)), some 2⟩,
    ⟨"forsTlTcr", some .forsTl, some (2 ^ 22), some 6⟩,
    ⟨"wotsFUd", some .wotsFUd, some (2 ^ 22 * 68), some 1⟩,
    ⟨"wotsFTcr", some .wotsFTcr, some (2 ^ 22 * 68 * 4), some 1⟩,
    ⟨"wotsFPre", some .wotsFPre, some (2 ^ 22 * 68), some 1⟩,
    ⟨"wotsTlTcr", some .wotsTl, some (2 ^ 22), some 68⟩,
    ⟨"xmssHTcr", some .xmssH, some (2 ^ 22 - 1), some 2⟩ ]

/-! ## The checks -/

/-- **The profile's parameters and the numbers they derive.**  The seven fields, the Winternitz
width and chain count they determine, the digest width, and the coefficient the bound carries. -/
def checkProfile : IO Unit := do
  ensure "n" (p.n == 16)
  ensure "h" (p.h == 22)
  ensure "d" (p.d == 1)
  ensure "hp" (p.hp == 22)
  ensure "a" (p.a == 24)
  ensure "k" (p.k == 6)
  ensure "lgw" (p.lgw == 2)
  ensure "valid" (decide p.Valid)
  ensure "w" (p.w == 4)
  ensure "len" (p.len == 68)
  ensure "m" (p.m == 21)
  ensure "digest bytes" (p.digestBytes == 18)
  ensure "tree index bytes" (p.treeIdxBytes == 0)
  ensure "leaf index bytes" (p.leafIdxBytes == 3)
  ensure "signature bytes" (p.signatureBytes == 3856)
  -- the one coefficient the profile turns into a numeral
  ensure "undetectability coefficient" (p.w - 2 == 2)
  ensure "two ≤ w" (2 ≤ p.w)
  -- at every FIPS 205 set the same coefficient is 14, so the numeral is the profile's
  ensure "every FIPS 205 set has coefficient 14"
    (FipsParameterSet.all.all fun ps => ps.params.w - 2 == 14)
  ensure "the reduced set is not a FIPS 205 set"
    (FipsParameterSet.all.all fun ps => ps.params != p)

/-- **The eight caps at this profile**, one check per `TargetRole` constructor, against
`SLHDSA.Security.targetCount`. -/
def checkCaps : IO Unit := do
  ensure "forsF" (targetCount p .forsF == 6 * 2 ^ 46)
  ensure "forsH" (targetCount p .forsH == 2 ^ 22 * 6 * (2 ^ 24 - 1))
  ensure "forsTl" (targetCount p .forsTl == 2 ^ 22)
  ensure "wotsFUd" (targetCount p .wotsFUd == 2 ^ 22 * 68)
  ensure "wotsFTcr" (targetCount p .wotsFTcr == 2 ^ 22 * 68 * 4)
  ensure "wotsFPre" (targetCount p .wotsFPre == 2 ^ 22 * 68)
  ensure "wotsTl" (targetCount p .wotsTl == 2 ^ 22)
  ensure "xmssH" (targetCount p .xmssH == 2 ^ 22 - 1)
  -- the two structural counts the caps are built from, at `d = 1`
  ensure "one XMSS tree" (xmssTreeCount p == 1)
  ensure "2 ^ hp WOTS+ instances" (wotsInstanceCount p == 2 ^ 22)

/-- **Arithmetic relations between the caps**, which a mis-transcribed formula breaks even when
each numeral is individually plausible.  A FORS tree of height `a` has `2 ^ a` leaves and
`2 ^ a − 1` internal nodes, so the FORS-`F` and FORS-`H` caps differ by one per tree; a chain is
walked at most `w` times; and the one XMSS tree has one internal node fewer than it has leaves. -/
def checkCapRelations : IO Unit := do
  ensure "forsF − forsH is one per FORS tree"
    (targetCount p .forsF - targetCount p .forsH == targetCount p .forsTl * p.k)
  ensure "wotsFTcr is wotsFUd times the width"
    (targetCount p .wotsFTcr == targetCount p .wotsFUd * p.w)
  ensure "wotsFUd is one per chain of every instance"
    (targetCount p .wotsFUd == targetCount p .wotsTl * p.len)
  ensure "xmssH is one short of the leaf count"
    (targetCount p .xmssH + 1 == 2 ^ p.hp)
  ensure "at d = 1 the leaf count is the FORS instance count"
    (2 ^ p.hp == targetCount p .forsTl)

/-- **The two cells that go dark, asserted.**  The `T_ℓ` pair coincides in cap and is separated by
arity; the WOTS+-`F` undetectability and preimage pair coincides in both and is separated by
neither.  The mirror pair, the two arity-two `H` games, is separated by cap. -/
def checkDarkCells : IO Unit := do
  -- the T_l pair: caps coincide at d = 1, arities do not
  ensure "forsTl and wotsTl caps coincide"
    (targetCount p .forsTl == targetCount p .wotsTl)
  ensure "k ≠ len" (p.k != p.len)
  ensure "the two T_l arities are k and len"
    ((summands.filter (·.summand == "forsTlTcr")).map (·.arity) == [some p.k] &&
      (summands.filter (·.summand == "wotsTlTcr")).map (·.arity) == [some p.len])
  -- the wotsFUd/wotsFPre pair: cap and arity both coincide
  ensure "wotsFUd and wotsFPre caps coincide"
    (targetCount p .wotsFUd == targetCount p .wotsFPre)
  ensure "wotsFUd and wotsFPre arities coincide"
    ((summands.filter (fun r => r.summand == "wotsFUd" || r.summand == "wotsFPre")).map
      (·.arity) == [some 1, some 1])
  -- the mirror: the two arity-two games are separated by their caps
  ensure "forsH and xmssH caps differ"
    (targetCount p .forsH != targetCount p .xmssH)
  ensure "the two H arities coincide"
    ((summands.filter (fun r => r.summand == "forsHTcr" || r.summand == "xmssHTcr")).map
      (·.arity) == [some 2, some 2])

/-- **The summand table**, checked against `targetCount` rather than only written down: twelve
rows in the source's order, three of them roleless, and every row that has a role carrying that
role's cap at this profile. -/
def checkSummandTable : IO Unit := do
  ensure "twelve summands" (summands.length == 12)
  ensure "names distinct" ((summands.map (·.summand)).eraseDups.length == 12)
  ensure "three summands have no cap role" ((summands.filter (·.role.isNone)).length == 3)
  ensure "the roleless three are the two PRF hops and the ITSR term"
    ((summands.filter (·.role.isNone)).map (·.summand) == ["skgPrf", "mkgPrf", "hmsgItsr"])
  ensure "the roleless three carry no cap"
    ((summands.filter (·.role.isNone)).all (·.cap.isNone))
  ensure "every role row carries its own cap"
    (summands.all fun r => match r.role, r.cap with
      | some role, some cap => cap == targetCount p role
      | none, none => true
      | _, _ => false)
  ensure "every role row carries an arity"
    (summands.all fun r => r.role.isSome == r.arity.isSome)
  ensure "all eight roles are used" ((summands.filterMap (·.role)).eraseDups.length == 8)
  ensure "the FORS-F role is the only one used twice"
    ((summands.filterMap (·.role)).length == 9)
  ensure "the two FORS-F rows are the DSPR and TCR summands"
    ((summands.filter (fun r => r.role == some .forsF)).map (·.summand) ==
      ["forsFDspr", "forsFTcr"])
  ensure "every cap is positive"
    (summands.all fun r => match r.cap with | some c => 0 < c | none => true)

/-! ## The pins

One `example` per exported declaration of `HashSig.SLHDSA.Security.LimitedProfile`, then the ten
games' caps read at the concrete bundle and the two `T_ℓ` games' arities read off their own
attacked-member equations.  A library-side edit cannot reach this file, so these are what refuses
a change to the corollaries' shape. -/

section Pins

variable {adv : unforgeableAdv (Security.generalAlg Security.limitedPrimitives)}
  {sadv : strongUnforgeableAdv (Security.generalAlg Security.limitedPrimitives)}

/-! ### The profile objects -/

example : ValidatedParams := limitedVp
example : Primitives limitedVp.params := limitedPrimitives
example : limitedVp.params = slhdsaSha2_128_24 := limitedVp_params
example : limitedPrimitives = Concrete.sha2Primitives slhdsaSha2_128_24 := limitedPrimitives_eq

/-! ### The nine carrier instances

Each is found by `inferInstance` here because the library module declares it; at that bundle none
of the nine is found without such a declaration. -/

example : SampleableType limitedPrimitives.Y := inferInstance
example : SampleableType limitedPrimitives.PkSeed := inferInstance
example : SampleableType limitedPrimitives.SkSeed := inferInstance
example : SampleableType limitedPrimitives.SkPrf := inferInstance
example : DecidableEq limitedPrimitives.Y := inferInstance
example : DecidableEq limitedPrimitives.PkSeed := inferInstance
example : DecidableEq limitedPrimitives.AdrsKey := inferInstance
-- `noncomputable`, measured: without it this pin is itself a compiled constant and the build
-- reports that it depends on the library module's `noncomputable` `Fintype` instance.  That
-- instance is `noncomputable` for the reason its own comment gives, and this is the pin
-- inheriting it.
noncomputable example : Fintype limitedPrimitives.Y := inferInstance
example : Inhabited limitedPrimitives.Y := inferInstance

/-! ### The carriers those instances are stated at -/

example : limitedPrimitives.Y = Bytes 16 := rfl
example : limitedPrimitives.PkSeed = Bytes 16 := rfl
example : limitedPrimitives.SkSeed = Bytes 16 := rfl
example : limitedPrimitives.SkPrf = Bytes 16 := rfl
example : limitedPrimitives.AdrsKey = Bytes 22 := rfl

/-! ### The profile's numbers -/

example : limitedVp.params.d = 1 := limitedParams_d
example : limitedVp.params.w = 4 := limitedParams_w
example : (limitedVp.params.w - 2 : ℕ) = 2 := limitedParams_wotsFUd_coefficient
example : limitedVp.params.k = 6 := limitedParams_k
example : limitedVp.params.len = 68 := limitedParams_len
example : limitedVp.params.k ≠ limitedVp.params.len := limitedParams_k_ne_len

/-! ### The eight caps -/

example : targetCount limitedVp.params .forsF = 6 * 2 ^ 46 := limitedTargetCount_forsF
example : targetCount limitedVp.params .forsH = 2 ^ 22 * 6 * (2 ^ 24 - 1) :=
  limitedTargetCount_forsH
example : targetCount limitedVp.params .forsTl = 2 ^ 22 := limitedTargetCount_forsTl
example : targetCount limitedVp.params .wotsFUd = 2 ^ 22 * 68 := limitedTargetCount_wotsFUd
example : targetCount limitedVp.params .wotsFTcr = 2 ^ 22 * 68 * 4 := limitedTargetCount_wotsFTcr
example : targetCount limitedVp.params .wotsFPre = 2 ^ 22 * 68 := limitedTargetCount_wotsFPre
example : targetCount limitedVp.params .wotsTl = 2 ^ 22 := limitedTargetCount_wotsTl
example : targetCount limitedVp.params .xmssH = 2 ^ 22 - 1 := limitedTargetCount_xmssH

/-- The undetectability and preimage caps coincide at *every* parameter set, not only at this
profile: `targetCount` gives both `wotsInstanceCount p * p.len`.  So no cap check anywhere can
separate those two roles. -/
example (q : Params) : targetCount q .wotsFUd = targetCount q .wotsFPre := rfl

/-! ### The ten games' caps at the concrete bundle

Each game's declared `numTargets` at `limitedPrimitives`, composed with this profile's numeral.
This is where a summand wired to the wrong game shows up — subject to the two dark cells the
module docstring records. -/

example : (forsFOpenPreProblem limitedPrimitives).numTargets = 6 * 2 ^ 46 := by
  rw [forsFOpenPreProblem_numTargets]; exact limitedTargetCount_forsF
example : (forsFDsprProblem limitedPrimitives).numTargets = 6 * 2 ^ 46 := by
  rw [forsFDsprProblem_numTargets]; exact limitedTargetCount_forsF
example : (forsFTcrProblem limitedPrimitives).numTargets = 6 * 2 ^ 46 := by
  rw [forsFTcrProblem_numTargets]; exact limitedTargetCount_forsF
example : (forsHTcrCProblem limitedPrimitives).numTargets = 2 ^ 22 * 6 * (2 ^ 24 - 1) := by
  rw [forsHTcrCProblem_numTargets]; exact limitedTargetCount_forsH
example : (forsTlTcrCProblem limitedPrimitives).numTargets = 2 ^ 22 := by
  rw [forsTlTcrCProblem_numTargets]; exact limitedTargetCount_forsTl
example : (wotsFUdCProblem limitedPrimitives).numTargets = 2 ^ 22 * 68 := by
  rw [wotsFUdCProblem_numTargets]; exact limitedTargetCount_wotsFUd
example : (wotsFTcrCProblem limitedPrimitives).numTargets = 2 ^ 22 * 68 * 4 := by
  rw [wotsFTcrCProblem_numTargets]; exact limitedTargetCount_wotsFTcr
example : (wotsFPreCProblem limitedPrimitives).numTargets = 2 ^ 22 * 68 := by
  rw [wotsFPreCProblem_numTargets]; exact limitedTargetCount_wotsFPre
example : (wotsTlTcrCProblem limitedPrimitives).numTargets = 2 ^ 22 := by
  rw [wotsTlTcrCProblem_numTargets]; exact limitedTargetCount_wotsTl
example : (xmssHTcrCProblem limitedPrimitives).numTargets = 2 ^ 22 - 1 := by
  rw [xmssHTcrCProblem_numTargets]; exact limitedTargetCount_xmssH

/-! ### The two `T_ℓ` games' arities

The cap cannot separate these two at `d = 1`; the message type can.  The FORS root compression
takes a `Vector limitedPrimitives.Y 6` and the WOTS+ public-key compression a
`Vector limitedPrimitives.Y 68`, so each equation below is stated at a type the other refuses. -/

example (pkSeed : limitedPrimitives.PkSeed) (address : Adrs)
    (input : Vector limitedPrimitives.Y 6) :
    (forsTlTcrCProblem limitedPrimitives).th.eval pkSeed
        (limitedPrimitives.adrsToKey address) input =
      limitedPrimitives.Tl pkSeed address input.toList :=
  forsTlTcrCProblem_eval_adrsToKey limitedPrimitives pkSeed address input

example (pkSeed : limitedPrimitives.PkSeed) (address : Adrs)
    (input : Vector limitedPrimitives.Y 68) :
    (wotsTlTcrCProblem limitedPrimitives).th.eval pkSeed
        (limitedPrimitives.adrsToKey address) input =
      limitedPrimitives.Tl pkSeed address input.toList :=
  wotsTlTcrCProblem_eval_adrsToKey limitedPrimitives pkSeed address input

/-! ### The two profile facts -/

example : limitedPrimitives.core.ByteLaws := limitedPrimitives_byteLaws
example : EncodedTargetLedgerConditions limitedVp limitedPrimitives := limitedEncodedConditions

/-! ### The five corollaries -/

example (c : Certificate limitedPrimitives adv) :
    adv.advantage ProbCompRuntime.probComp ≤ c.summands.bound limitedVp.params :=
  limitedAdvantage_le_bound c

example (c : Certificate limitedPrimitives adv) :
    c.summands.bound limitedVp.params =
      prfAbsAdvantage (skPrfScheme limitedPrimitives c.pkSeed) c.skgAdv
        + prfAbsAdvantage (msgPrfScheme limitedPrimitives) c.mkgAdv
        + ITSRAdvantage c.itsrAdv
        + SM_DT_DSPR_SourceFinalValidity.Advantage
            (SM_DT_OpenPRE_SourceFinalValidity.toDSPR c.openPreAdv)
        + 3 * SM_DT_TCR_SourceFinalValidity.Advantage
            (SM_DT_OpenPRE_SourceFinalValidity.toTCR c.openPreAdv)
        + SM_DT_TCR_SourceFinalValidity.Advantage c.forsHAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.forsTlAdv
        + 2 * SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage c.wotsFUdAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsFTcrAdv
        + SM_DT_PRE_SourceFinalValidity.Advantage c.wotsFPreAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsTlAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.xmssHAdv :=
  limitedBound_eq c

example (c : Certificate limitedPrimitives adv) :
    adv.advantage ProbCompRuntime.probComp ≤
      prfAbsAdvantage (skPrfScheme limitedPrimitives c.pkSeed) c.skgAdv
        + prfAbsAdvantage (msgPrfScheme limitedPrimitives) c.mkgAdv
        + ITSRAdvantage c.itsrAdv
        + SM_DT_DSPR_SourceFinalValidity.Advantage
            (SM_DT_OpenPRE_SourceFinalValidity.toDSPR c.openPreAdv)
        + 3 * SM_DT_TCR_SourceFinalValidity.Advantage
            (SM_DT_OpenPRE_SourceFinalValidity.toTCR c.openPreAdv)
        + SM_DT_TCR_SourceFinalValidity.Advantage c.forsHAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.forsTlAdv
        + 2 * SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage c.wotsFUdAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsFTcrAdv
        + SM_DT_PRE_SourceFinalValidity.Advantage c.wotsFPreAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsTlAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage c.xmssHAdv :=
  limitedAdvantage_le_summands c

example (c : Certificate limitedPrimitives sadv.toUnforgeableAdv) :
    sadv.advantage ProbCompRuntime.probComp ≤
      c.summands.bound limitedVp.params +
        sadv.sameMessageAdvantage ProbCompRuntime.probComp :=
  limitedStrongAdvantage_le_bound_add_sameMessage c

example (c : Certificate limitedPrimitives sadv.toUnforgeableAdv) :
    sadv.advantage ProbCompRuntime.probComp ≤
      c.summands.sufBound limitedVp.params (freshRandomizerHalf sadv)
        (sameRandomizerHalf sadv) :=
  limitedStrongAdvantage_le_sufBound c

/-! ### The two certificate fields the dark cells leave to the types

`wotsFUdAdv` and `wotsFPreAdv` have the same role cap and the same arity at this profile, so
nothing the runtime table reads separates them.  Their types do. -/

example (c : Certificate limitedPrimitives adv) :
    SM_DT_UD_SourceFinalValidity.Adversary (wotsFUdCProblem limitedPrimitives) := c.wotsFUdAdv

example (c : Certificate limitedPrimitives adv) :
    SM_DT_PRE_SourceFinalValidity.Adversary (wotsFPreCProblem limitedPrimitives) := c.wotsFPreAdv

end Pins

/-! ## The vacuity canary, at this bundle

The two previous pull requests' measurement, re-run at the concrete profile.  A closed
`SLHDSA.Security.Certificate` is constructible at an arbitrary validated parameter set, an
arbitrary bundle carrying the instances the structure asks for and an arbitrary adversary, from an
address key and a public seed and no security assumption at all, and the bound it names is at
least one.  Applied here, that says the corollaries of
`HashSig.SLHDSA.Security.LimitedProfile` are no stronger than what they instantiate:
`limitedAdvantage_le_bound` at the certificate below reads
`adv.advantage ≤ (something ≥ 1)`, which `probOutput_le_one` gives with extra steps, and the two
strong-unforgeability corollaries read the same with a residual added on the right.

**Why it is restated at the bundle rather than cited.**  The construction is generic in the
parameter set and the bundle, so the concrete case follows from it — but it follows only through
the nine instances this pull request declares, and those are the part a concrete profile adds.
Restating it here is what catches an edit that breaks the concrete case alone, exactly as
`HashSigTest.SLHDSA.Composition` restates its own canary at the toy bundle for the same reason.

**Why these declarations are copied rather than imported.**  The construction is
`HashSigTest.SLHDSA.Composition`'s, carried unchanged through `HashSigTest.SLHDSA.SufBound`, and
importing either from a `lean_exe` root is not possible: each declares a top-level `main`, and a
second declaration of that name reports `` `main` has already been declared`` — measured, not
assumed.  The lane has no shared fixture module and adding one would edit merged, reviewed files
from inside this pull request.  What is copied is the free-certificate stack and the two
strong-unforgeability headlines above it: fifteen declarations, the two idle adversaries, the
open-preimage adversary that records nothing with its three advantage lemmas and its counting
interface, the winning preimage adversary with its inverse, the certificate with the bound it
names, and the two headlines.  What is **not** copied is `HashSigTest.SLHDSA.Composition`'s
anchoring analysis — `winningOpenPre`, `anchoredCertificate` and `nonempty_countingInterface_iff`
— for the reason `HashSigTest.SLHDSA.SufBound` gives, and for one more that is specific to this
bundle: the equivalence those end in carries `2 ≤ Fintype.card` of the node type, and at
`Bytes 16` that is a statement about `2 ^ 128` elements which no `decide` in this repository
reaches.

*Copied verbatim from `HashSigTest.SLHDSA.SufBound` except for the docstrings of this section; a
reviewer can diff the blocks.* -/

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

-- Exposed, and it is the only one of the seven definitions in this section that is: the file
-- elaborates clean with this attribute and no other one here.  Inside a `public section` a
-- definition's body is not available to later declarations, so without it
-- `(Problem.toDSPR (idleOpenPre prob)).State` does not reduce to `Unit × _ × _` and
-- `idleOpenPre_toDSPR_choose` cannot even be stated: three errors, a `Type mismatch` at that
-- statement, the `unknownIdentifier` it causes in `idleOpenPre_dspr`, and that theorem's
-- `unsolved goals`.
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

/-! ### The same facts at the concrete SHA2-128-24 bundle

The section above is at an arbitrary validated parameter set and an arbitrary bundle; these four
restate it at the profile the corollaries use, so a change that breaks only the concrete case is
caught here.  The first is the certificate itself, the second the existential headline, and the
last two the strong-unforgeability headline and its refinement. -/

noncomputable example (t : limitedPrimitives.AdrsKey) (pkSeed : limitedPrimitives.PkSeed)
    (adv : unforgeableAdv (generalAlg limitedPrimitives)) :
    Certificate limitedPrimitives adv :=
  freeCertificate (vp := limitedVp) (prims := limitedPrimitives) (adv := adv) t pkSeed

example (t : limitedPrimitives.AdrsKey) (pkSeed : limitedPrimitives.PkSeed)
    (adv : unforgeableAdv (generalAlg limitedPrimitives)) :
    adv.advantage ProbCompRuntime.probComp ≤
        (freeCertificate (vp := limitedVp) (prims := limitedPrimitives)
          (adv := adv) t pkSeed).summands.bound limitedVp.params ∧
      1 ≤ (freeCertificate (vp := limitedVp) (prims := limitedPrimitives)
          (adv := adv) t pkSeed).summands.bound limitedVp.params :=
  ⟨limitedAdvantage_le_bound _,
    one_le_freeCertificate_bound (vp := limitedVp) (prims := limitedPrimitives) t pkSeed⟩

example (t : limitedPrimitives.AdrsKey) (pkSeed : limitedPrimitives.PkSeed)
    (sadv : strongUnforgeableAdv (generalAlg limitedPrimitives)) :
    sadv.advantage ProbCompRuntime.probComp ≤
        (freeCertificate (vp := limitedVp) (prims := limitedPrimitives)
          (adv := sadv.toUnforgeableAdv) t pkSeed).summands.bound limitedVp.params +
          sadv.sameMessageAdvantage ProbCompRuntime.probComp ∧
      1 ≤ (freeCertificate (vp := limitedVp) (prims := limitedPrimitives)
          (adv := sadv.toUnforgeableAdv) t pkSeed).summands.bound limitedVp.params +
          sadv.sameMessageAdvantage ProbCompRuntime.probComp :=
  freeCertificate_suf_headline (vp := limitedVp) (prims := limitedPrimitives) (sadv := sadv)
    t pkSeed

example (t : limitedPrimitives.AdrsKey) (pkSeed : limitedPrimitives.PkSeed)
    (sadv : strongUnforgeableAdv (generalAlg limitedPrimitives)) :
    sadv.advantage ProbCompRuntime.probComp ≤
        (freeCertificate (vp := limitedVp) (prims := limitedPrimitives)
          (adv := sadv.toUnforgeableAdv) t pkSeed).summands.sufBound limitedVp.params
          (freshRandomizerHalf sadv) (sameRandomizerHalf sadv) ∧
      1 ≤ (freeCertificate (vp := limitedVp) (prims := limitedPrimitives)
          (adv := sadv.toUnforgeableAdv) t pkSeed).summands.sufBound limitedVp.params
          (freshRandomizerHalf sadv) (sameRandomizerHalf sadv) :=
  freeCertificate_sufBound_headline (vp := limitedVp) (prims := limitedPrimitives) (sadv := sadv)
    t pkSeed

/-- Run the five check groups in order, then report. -/
def main : IO Unit := do
  checkProfile
  checkCaps
  checkCapRelations
  checkDarkCells
  checkSummandTable
  IO.println "SLH-DSA limited profile tests: PASS"

end SLHDSA.LimitedProfileTest

/-- Entry point for `slhdsa_limited_profile_tests`. -/
def main : IO Unit := SLHDSA.LimitedProfileTest.main
