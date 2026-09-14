/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.Composition

/-!
# SLH-DSA composition canaries

Executable checks for the *decidable* data that `HashSig.SLHDSA.Security.Composition`'s bound is
parameterised by — the two coefficients, the twelve summands' routing to the named games of
`HashSig.SLHDSA.Security.CanonicalGames`, and those games' target caps — together with at least
one elaboration pin per exported declaration of that module.

## Nothing about the bound itself is runnable, and that is a property of the subject

`Summands.bound` is `ℝ≥0∞`-valued and every advantage it is built from is `noncomputable`, so the
headline `advantage_le_bound`, the certificate, the two transports and every statement about a
probability have **no runtime coverage at all** and cannot be given any.  The runtime checks below
are about `Params`-level data only: `p.w - 2`, `SLHDSA.Security.targetCount`, and a routing table
this file writes down.  What pins the bound's own shape is the `Pins` section, which restates each
of the twenty-one exported declarations, and mutation testing against those pins; what pins the
*strength* of the hypotheses is the vacuity canary at the end, which is elaboration-only for the
same reason.

A reader of the lane's other fixtures will look for the headline among the runtime checks; it is
not there, and no fixture could put it there.

## The two profiles, and why there are two

`toyParams` is the two-layer profile of the scheme-dispatch, SUF-residual and scheme-game fixtures,
copied rather than imported for the reason those files give: a `lean_exe` root must own its `main`,
and a module that imports another fixture cannot declare one.  The primitive bundle is theirs less
three things: the exclusive-or fold, which only that file's `H_msg` blindness assertion used; every
message, signature and log, because no reader here reads one; and the bundle's `@[reducible]`
attribute, which is measured unnecessary here.

`SLHDSA.LimitedParameterSet.SLHDSA_SHA2_128_24` is here as a bare `Params`, with no primitive
bundle, because it is the profile at which the summand-to-game routing has a cell that goes dark.
The FORS `T_k` and WOTS+ `T_len` compressions are both target-collision games on the shared
collection, which makes them the most plausible mis-wiring in the module, and at `d = 1` they have
**the same cap** — both `2 ^ 22` at this profile, and `2 ^ h` at every one-layer parameter set,
which the `Pins` section proves.  At `toyParams`, where `d = 2`, the caps differ, 16 against 20;
`Pins` proves that separation general too, for every `2 ≤ d`.

So the caps separate the two `T_ℓ` games exactly when the hypertree has more than one layer, and
what is left at `d = 1` is the **arity**, `p.k` against `p.len`.  That is not a property of
`Params.Valid`, which relates neither: `collideParams` below is *valid*, has `d = 1` and
`k = len = 6`, and at it `forsTlTcrCProblem` and `wotsTlTcrCProblem` are the same term by `rfl`,
so no check of any kind can tell them apart there.  What makes the separation true where it
matters is the parameter table: every FIPS 205 set and the SP 800-230 set has `k ≠ len`, asserted
below over the whole table rather than at the two profiles this file carries.

## The reader-by-log matrix is empty, by construction

The lane's other fixtures carry two or three signing logs and a matrix of readers against them.
This one carries none: its three readers — the coefficient `p.w - 2`, the cap function
`targetCount`, and the routing table — are functions of a `Params` and of nothing else.  No log
could change any of their values, so no log is carried and the matrix has no rows.  The dispatch
selector and the logged-randomizer predicate are `HashSigTest.SLHDSA.SchemeGames`' readers and are
exercised there.

## What the checks cannot catch

* **A paired edit of the `w − 2` coefficient that also moves this file.**  Nothing in the
  repository derives the coefficient.  Changed throughout the library module it leaves that module
  elaborating clean and fails eleven `Pins` entries here, which restate the bound expression, the
  two branch expressions and the coefficient as a numeral at two profiles.  Changed here as well,
  nothing anywhere fails and the executable passes — at which point the claim has been changed
  rather than a bug found, and the only remaining check is the source citation the library module
  carries.
* **Anything about a probability.**  See above.
* **What a certificate's three named quantities mean.**  `idealAdvantage`, `forsBranch` and
  `hypertreeBranch` are `ℝ≥0∞` fields with no tie to any experiment, so the pins can only restate
  their types.  That no check *catches* it does not mean no check *records* it: the vacuity canary
  below exhibits the certificate that puts the whole obligation on one branch and closes the goal
  it leaves, which is the fact rather than the absence of one.  The certificate's `pkSeed` is
  likewise not tied to the seed key generation sampled, and that one is recorded in the library
  module's docstring as open with nothing here checking it.
* **Whether the summands are the source's.**  The routing table below says which Lean game each
  summand is the advantage of; that the twelve games are the source's twelve is a reading of
  `SPHINCS_PLUS.ec`, `FORS_ES.ec`, `FL_SL_XMSS_MT_ES.ec` and `WOTS_TW_ES.ec`, recorded in the
  library module's docstring, and no fixture can check it.

## What is here

Sixty-seven runtime checks in four groups — the two coefficients (18), the eight caps at both
profiles (16), the `T_ℓ` separation and the valid profile where it fails (20), and the routing
table (13).  Eighty `example`s in `Pins`: at least one for each of the twenty-one declarations the
library module exports, the two `T_ℓ` attacked-member equations, the ten games' declared caps, the
three general cap separations and the game identity they explain, the `ITSRProblem` shape, and
twenty-two profile pins.  Then the vacuity canary — eighteen declarations and four `example`s,
which together build a closed `Certificate` from an address key and a public seed and prove that
the bound it names is at least one.

## References

- NIST FIPS 205, §11 for the parameter sets, and SP 800-230 for the reduced `SLH-DSA-SHA2-128-24`
-/

public section

namespace SLHDSA.CompositionTest

open Security Security.CanonicalGames KeyedHash OracleSpec TweakableHash

/-- Throw on a failed check, naming it. -/
def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"Composition check failed: {label}")

/-! ## The two profiles -/

-- Exposed, and what the attribute is for was read off the errors its removal alone produces in
-- this file: thirty-six, no error ceiling reached.  One `Type mismatch: id` inside the bundle
-- below, at `yToBytes := id`; eighteen `(kernel) declaration type mismatch`, two at each of the
-- nine instances written at `toyPrimitives`; nine code-generation failures at those same nine
-- instances, six `failed to compile definition` and three `Failed to find LCNF signature`; and
-- eight `Application type mismatch` in the vacuity canary's toy instantiations, where `toy.params`
-- has to be `toyParams` for the generic declarations to apply.
/-- Two layers of height two, two FORS trees of height one. -/
@[expose] def toyParams : Params :=
  { n := 1, h := 4, d := 2, hp := 2, a := 1, k := 2, lgw := 4 }

/-- The toy parameters are valid. -/
theorem toyValid : toyParams.Valid := by decide

-- Exposed for a different reason from `toyParams`, also read off its removal: seven errors, none
-- of them in the bundle and all of them in the pins, where the certificate's own `vp` has to
-- reduce to `toyParams` for the bundle's instances to be found.  Six are `typeclass instance
-- problem is stuck` and the seventh is a `(deterministic) timeout at isDefEq`; none is a
-- `failed to synthesize`.
/-- The validated form of `toyParams`. -/
@[expose] def toy : ValidatedParams := ⟨toyParams, toyValid⟩

/-- The SP 800-230 reduced parameter set, as a bare `Params`: the profile at which the two `T_ℓ`
caps coincide.  No primitive bundle is built at it here. -/
def p24 : Params := LimitedParameterSet.params .SLHDSA_SHA2_128_24

/-- A *valid* parameter set with `lgw = 1`, hence `w = 2` and an undetectability coefficient of
zero.  It is here because `Params.Valid` does not rule this out, and at it the WOTS+-`F`
undetectability summand leaves the bound.  Whether that is right the source does not say: it fixes
`w` to 4, 16 or 256 (`WOTS_TW_ES.ec`, `val_w`) and states neither hypertree lemma outside that set,
so `Params.Valid` is more permissive here than the parameter space of the theorem the bound
mirrors.  `SLHDSA.Security.two_le_w` does not settle it either, and
`bound_wotsFUd_coefficient_add_two` is what it buys. -/
def widthTwoParams : Params :=
  { n := 1, h := 4, d := 2, hp := 2, a := 1, k := 2, lgw := 1 }

/-- A *valid* parameter set with `d = 1` and `k = len`, at which the two `T_ℓ` compression games
are literally the same object: same attacked hash, same collection, same cap, same arity.  It is
here because `Params.Valid` relates `k` to nothing, so the arity separation the routing relies on
is a property of the shipped parameter table and not of validity. -/
def collideParams : Params :=
  { n := 1, h := 4, d := 1, hp := 4, a := 2, k := 6, lgw := 2 }

/-- A deliberately invalid parameter set with `lgw = 0`, hence `w = 1`.  It exists so that the
`ℕ`-truncation `two_le_w` rules out has a witness: at it the undetectability coefficient would be
`1 - 2 = 0` and the whole WOTS+ undetectability summand would silently vanish from the bound. -/
def degenerateParams : Params :=
  { n := 1, h := 4, d := 2, hp := 2, a := 1, k := 2, lgw := 0 }

/-! ## The toy primitive bundle

The bundle of `HashSigTest.SLHDSA.SchemeGames`, unchanged.  Nothing below evaluates a digest, a
signature or a hash: the bundle is here so that the twelve games, the two PRF schemes, the external
signature algebra and the certificate can be named at concrete types. -/

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

/-- The toy `PRF_msg`: the message randomizer FIPS 205 Algorithm 19 line 3 derives. -/
def toyRandomizer (skPrf addrnd : UInt8) (msg : List Byte) : UInt8 :=
  mixByte (UInt8.ofNat
    ((skPrf.toNat * 13 + addrnd.toNat * 47 + (byteMix msg).toNat * 5 + 1) % 256))

/-- Byte `i` of the toy `H_msg` digest. -/
def toyDigestByte (r seed root : UInt8) (msg : List Byte) (i : ℕ) : UInt8 :=
  mixByte (UInt8.ofNat ((r.toNat * (6 * i + 37) + seed.toNat * (10 * i + 53) +
    root.toNat * (14 * i + 89) + (byteMix msg).toNat * (22 * i + 149) + (30 * i + 7)) % 256))

-- Exposed for code generation, and that is the whole of it: without the attribute, thirty errors,
-- every one of them `Compilation failed, locally inferred compilation type differs from type that
-- would be inferred in other modules` — two at each of the nine instances below, eleven at the
-- pins that name the certificate's fields at this bundle's types, and one at the `ITSRProblem`
-- shape pin.  `@[reducible]`, which the scheme-game fixture's copy of this bundle also carries,
-- is *not* needed here and is not written: the build is clean without it, because no check below
-- resolves an instance through the carrier by unfolding it — the nine instances name `Bytes 1`
-- and `Adrs` directly.
/-- The toy bundle: one byte per node, a collapsing order- and address-sensitive `Thash`, and an
`H_msg` that depends on all four of its arguments. -/
@[expose] def toyPrimitives : Primitives toyParams where
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

/-- Public-seed equality, which the `H_msg` ITSR input type's own `DecidableEq` is derived from. -/
instance : DecidableEq toyPrimitives.PkSeed := inferInstanceAs (DecidableEq (Bytes 1))

/-- Tweak equality, which every `SM_DT_*` advantage asks for. -/
instance : DecidableEq toyPrimitives.AdrsKey := inferInstanceAs (DecidableEq Adrs)

/-- Finiteness of the node type, which the DSPR advantage asks for. -/
instance : Fintype toyPrimitives.Y := inferInstanceAs (Fintype (Bytes 1))

/-- Inhabitedness of the node type, which the OpenPRE coupling asks for. -/
instance : Inhabited toyPrimitives.Y := inferInstanceAs (Inhabited (Bytes 1))

/-- Key generation samples the public seed. -/
instance : SampleableType toyPrimitives.PkSeed := inferInstanceAs (SampleableType (Bytes 1))

/-- Key generation samples the secret seed. -/
instance : SampleableType toyPrimitives.SkSeed := inferInstanceAs (SampleableType (Bytes 1))

/-- Key generation samples the message-PRF key. -/
instance : SampleableType toyPrimitives.SkPrf := inferInstanceAs (SampleableType (Bytes 1))

/-- Signing samples the per-signature `addrnd`. -/
instance : SampleableType toyPrimitives.Y := inferInstanceAs (SampleableType (Bytes 1))

/-! ## The routing table

One row per summand of `Summands`, in the source's order: the field's name, the `TargetRole` whose
`targetCount` caps the game the summand is the advantage of, and whether a witness family of slices
7.1--7.5 lands in that game.  Three summands have no role and no witness: the two `PRF` hops and the
undetectability term, which in the source comes from the `Game2 → Game3` step of
`MEUFGCMA_WOTSTWESNPRF` rather than from a forgery.  The `H_msg` ITSR game has a witness but no
`TargetRole`, and no cap of any other kind either: `KeyedHash.ITSRProblem` has two fields, the
keyed hash family and the index map, and `ITSRTargetOracle` answers and records every query with
no bound and no poison bit.  The source's `MCO_ITSR` term is bounded through its reduction, whose
target count is the forger's signing queries because the reduction is built from the forger; the
Lean advantage is a supremum over adversaries with unbounded transcripts, which is a strictly
larger quantity.  `Pins` restates the two-field shape, so a cap added later has to be noticed
here. -/

/-- A routing row: the summand's field name, its game's cap role, and whether a witness family of
this lane lands in that game. -/
structure RoutingRow where
  /-- The field name of `SLHDSA.Security.Summands` this row is about. -/
  summand : String
  /-- The `TargetRole` capping the game, where the game has one. -/
  role : Option TargetRole
  /-- Whether one of the lane's witness families lands in the game. -/
  witnessBacked : Bool
  deriving Repr

/-- The twelve summands, in the order of `EUFCMA_SPHINCS_PLUS`. -/
def routing : List RoutingRow :=
  [ ⟨"skgPrf", none, false⟩,
    ⟨"mkgPrf", none, false⟩,
    ⟨"hmsgItsr", none, true⟩,
    ⟨"forsFDspr", some .forsF, true⟩,
    ⟨"forsFTcr", some .forsF, true⟩,
    ⟨"forsHTcr", some .forsH, true⟩,
    ⟨"forsTlTcr", some .forsTl, true⟩,
    ⟨"wotsFUd", some .wotsFUd, false⟩,
    ⟨"wotsFTcr", some .wotsFTcr, true⟩,
    ⟨"wotsFPre", some .wotsFPre, true⟩,
    ⟨"wotsTlTcr", some .wotsTl, true⟩,
    ⟨"xmssHTcr", some .xmssH, true⟩ ]

/-- The eight distinct witness branches the nine witness-backed summands are backed by.  The FORS
open-preimage branch backs two of them — the `DSPR` and the `3 · TCR` summands are read off one
adversary — so the two counts differ, and both are asserted. -/
def witnessBranches : List String :=
  [ "HmsgWitnesses.itsr_wins_or_uncovered",
    "ForsWitness.fPreimage",
    "ForsWitness.hCollision",
    "ForsWitness.tlCollision",
    "WotsWitness.fCollision",
    "WotsWitness.fPreimage",
    "WotsWitness.tlCollision",
    "XmssWitness.hCollision" ]

/-! ## The checks -/

/-- **The two coefficients.**  The `3` on the FORS-`F` target-collision summand is the library's
own, so nothing here can move it; what this group reads is the `w − 2` coefficient, which is a
`Params`-level number, at both profiles and at a parameter set where the `ℕ`-subtraction would
truncate. -/
def checkCoefficients : IO Unit := do
  ensure "toy w" (toyParams.w == 16)
  ensure "toy lgw" (toyParams.lgw == 4)
  ensure "toy w - 2" (toyParams.w - 2 == 14)
  ensure "toy 2 <= w" (2 ≤ toyParams.w)
  ensure "p24 w" (p24.w == 4)
  ensure "p24 lgw" (p24.lgw == 2)
  ensure "p24 w - 2" (p24.w - 2 == 2)
  ensure "p24 2 <= w" (2 ≤ p24.w)
  ensure "p24 d = 1" (p24.d == 1)
  -- a *valid* set at which the coefficient is legitimately zero: `Valid` permits `lgw = 1`
  ensure "width-two w" (widthTwoParams.w == 2)
  ensure "width-two lgw" (widthTwoParams.lgw == 1)
  ensure "width-two coefficient is zero" (widthTwoParams.w - 2 == 0)
  ensure "width-two is valid" (decide widthTwoParams.Valid)
  -- the truncation `two_le_w` rules out, exhibited at a parameter set where it fires
  ensure "degenerate w" (degenerateParams.w == 1)
  ensure "degenerate w - 2 truncates to zero" (degenerateParams.w - 2 == 0)
  ensure "degenerate is not valid" (!decide degenerateParams.Valid)
  ensure "toy is valid" (decide toyParams.Valid)
  ensure "p24 is valid" (decide p24.Valid)

/-- **The eight caps, at both profiles.**  One check per `TargetRole` constructor, against
`SLHDSA.Security.targetCount` at that role: eight roles, sixteen checks. -/
def checkCaps : IO Unit := do
  ensure "toy forsF" (targetCount toyParams .forsF == 64)
  ensure "toy forsH" (targetCount toyParams .forsH == 32)
  ensure "toy forsTl" (targetCount toyParams .forsTl == 16)
  ensure "toy wotsFUd" (targetCount toyParams .wotsFUd == 80)
  ensure "toy wotsFTcr" (targetCount toyParams .wotsFTcr == 1280)
  ensure "toy wotsFPre" (targetCount toyParams .wotsFPre == 80)
  ensure "toy wotsTl" (targetCount toyParams .wotsTl == 20)
  ensure "toy xmssH" (targetCount toyParams .xmssH == 15)
  ensure "p24 forsF" (targetCount p24 .forsF == 6 * 2 ^ 46)
  ensure "p24 forsH" (targetCount p24 .forsH == 2 ^ 22 * 6 * (2 ^ 24 - 1))
  ensure "p24 forsTl" (targetCount p24 .forsTl == 2 ^ 22)
  ensure "p24 wotsFUd" (targetCount p24 .wotsFUd == 2 ^ 22 * 68)
  ensure "p24 wotsFTcr" (targetCount p24 .wotsFTcr == 2 ^ 22 * 68 * 4)
  ensure "p24 wotsFPre" (targetCount p24 .wotsFPre == 2 ^ 22 * 68)
  ensure "p24 wotsTl" (targetCount p24 .wotsTl == 2 ^ 22)
  ensure "p24 xmssH" (targetCount p24 .xmssH == 2 ^ 22 - 1)

/-- **The cell that goes dark, and what is left when it does.**  The two `T_ℓ` compressions are
both target-collision games on the shared `Thash` collection; at `d = 1` their caps coincide, so at
the profile the corollary of the next pull request will use, a cap check alone cannot tell
`forsTlTcrCProblem` from `wotsTlTcrCProblem`.  What is left there is the arity, `p.k` against
`p.len`, and `Params.Valid` does not relate the two: `collideParams` is valid with `k = len`, and
at it the two games are the same term.  So the last group here asserts the separation where it is
actually true, over the whole shipped parameter table. -/
def checkTlDiscrimination : IO Unit := do
  -- at the two-layer profile the caps discriminate
  ensure "toy forsTl ≠ wotsTl" (targetCount toyParams .forsTl != targetCount toyParams .wotsTl)
  -- at SLH-DSA-SHA2-128-24 they do not: this is the dark cell, asserted
  ensure "p24 forsTl = wotsTl" (targetCount p24 .forsTl == targetCount p24 .wotsTl)
  -- the paired arity check, which discriminates at both
  ensure "toy k" (toyParams.k == 2)
  ensure "toy len" (toyParams.len == 4)
  ensure "toy k ≠ len" (toyParams.k != toyParams.len)
  ensure "p24 k" (p24.k == 6)
  ensure "p24 len" (p24.len == 68)
  ensure "p24 k ≠ len" (p24.k != p24.len)
  -- the other pair of same-shaped games: FORS-`H` and XMSS-`H` are both two-node `H` collisions
  ensure "toy forsH ≠ xmssH" (targetCount toyParams .forsH != targetCount toyParams .xmssH)
  ensure "p24 forsH ≠ xmssH" (targetCount p24 .forsH != targetCount p24 .xmssH)
  -- the valid profile at which nothing discriminates, asserted rather than hidden
  ensure "collide is valid" (decide collideParams.Valid)
  ensure "collide d = 1" (collideParams.d == 1)
  ensure "collide k" (collideParams.k == 6)
  ensure "collide len" (collideParams.len == 6)
  ensure "collide k = len" (collideParams.k == collideParams.len)
  ensure "collide forsTl = wotsTl" (targetCount collideParams .forsTl ==
    targetCount collideParams .wotsTl)
  ensure "collide w is not two" (collideParams.w == 4)
  -- so the arity separation is a fact about the table, asserted over all of it
  ensure "every FIPS 205 set has k ≠ len"
    (FipsParameterSet.all.all fun ps => ps.params.k != ps.params.len)
  ensure "twelve FIPS 205 sets" (FipsParameterSet.all.length == 12)
  ensure "the SP 800-230 set has k ≠ len"
    ((LimitedParameterSet.params .SLHDSA_SHA2_128_24).k !=
      (LimitedParameterSet.params .SLHDSA_SHA2_128_24).len)

/-- **The routing table.**  Twelve rows, three of them roleless, nine witness-backed, and the eight
`TargetRole` constructors covered with `forsF` used twice. -/
def checkRouting : IO Unit := do
  ensure "twelve summands" (routing.length == 12)
  ensure "names distinct" ((routing.map (·.summand)).eraseDups.length == 12)
  ensure "three summands have no cap role"
    ((routing.filter (·.role.isNone)).length == 3)
  ensure "the roleless three are the two PRF hops and the ITSR term"
    ((routing.filter (·.role.isNone)).map (·.summand) == ["skgPrf", "mkgPrf", "hmsgItsr"])
  ensure "nine summands are witness-backed" ((routing.filter (·.witnessBacked)).length == 9)
  ensure "the three unbacked are the two PRF hops and the undetectability term"
    ((routing.filter (fun r => !r.witnessBacked)).map (·.summand) ==
      ["skgPrf", "mkgPrf", "wotsFUd"])
  ensure "eight distinct witness branches back those nine"
    (witnessBranches.length == 8 && witnessBranches.eraseDups.length == 8)
  ensure "nine rows carry a role" ((routing.filter (·.role.isSome)).length == 9)
  ensure "all eight roles are used"
    ((routing.filterMap (·.role)).eraseDups.length == 8)
  ensure "forsF is the only role used twice"
    ((routing.filter (fun r => r.role == some .forsF)).length == 2)
  ensure "the two forsF rows are the DSPR and TCR summands"
    ((routing.filter (fun r => r.role == some .forsF)).map (·.summand) ==
      ["forsFDspr", "forsFTcr"])
  -- every role's cap is positive at both valid profiles, which `targetCount_pos` proves generally
  ensure "toy caps positive"
    ((routing.filterMap (·.role)).all fun r => 0 < targetCount toyParams r)
  ensure "p24 caps positive"
    ((routing.filterMap (·.role)).all fun r => 0 < targetCount p24 r)

/-! ## The pins

Every one of the twenty-one declarations `HashSig.SLHDSA.Security.Composition` exports, restated at
this bundle's types, with generic arguments where the statement has them.  These are the only check
on the bound's own shape: a library-side edit of a coefficient, of a summand's routing, or of a
certificate field's type moves the library statement and fails the pin here, which no library-side
edit can reach. -/

section Pins

open OracleComp ENNReal SignatureAlg

variable (s : Summands) (p : Params) (x : ℝ≥0∞)
  (adv : unforgeableAdv (generalAlg (vp := toy) toyPrimitives))

/-! ### The PRF seam -/

noncomputable example {K D R : Type} [DecidableEq D] [SampleableType R]
    (prf : PRFScheme K D R) (a : PRFScheme.PRFAdversary D R) : ℝ≥0∞ := prfAbsAdvantage prf a

example {K D R : Type} [DecidableEq D] [SampleableType R]
    (prf : PRFScheme K D R) (a : PRFScheme.PRFAdversary D R) :
    (prfAbsAdvantage prf a).toReal = PRFScheme.prfAdvantage prf a := prfAbsAdvantage_toReal prf a

/-! ### The bound expression, with both coefficients written out -/

example (h : p.Valid) : 2 ≤ p.w := two_le_w h

noncomputable example : ℝ≥0∞ := s.bound p

example : s.bound p = s.skgPrf + s.mkgPrf + s.hmsgItsr
    + s.forsFDspr + 3 * s.forsFTcr + s.forsHTcr + s.forsTlTcr
    + (p.w - 2 : ℕ) * s.wotsFUd + s.wotsFTcr + s.wotsFPre + s.wotsTlTcr + s.xmssHTcr :=
  s.bound_eq p

example : (Summands.mk 0 0 0 0 0 0 0 0 0 0 0 0).bound p = 0 := bound_eq_zero_of_summands_zero p

example : (Summands.mk 0 0 0 0 0 0 0 x 0 0 0 0).bound p = (p.w - 2 : ℕ) * x :=
  bound_wotsFUd_coefficient p x

example (h : p.Valid) : (Summands.mk 0 0 0 0 0 0 0 x 0 0 0 0).bound p + 2 * x = (p.w : ℝ≥0∞) * x :=
  bound_wotsFUd_coefficient_add_two h x

example : (Summands.mk 0 0 0 0 x 0 0 0 0 0 0 0).bound p = 3 * x :=
  bound_forsFTcr_coefficient p x

/-- The undetectability coefficient at the two profiles, as a value: the `Summands.bound` of a
one-hot `wotsFUd` is `14 · x` at the toy profile and `2 · x` at SLH-DSA-SHA2-128-24. -/
example : (Summands.mk 0 0 0 0 0 0 0 x 0 0 0 0).bound toyParams = 14 * x := by
  rw [bound_wotsFUd_coefficient, show toyParams.w - 2 = 14 from by decide]
  norm_num

example : (Summands.mk 0 0 0 0 0 0 0 x 0 0 0 0).bound p24 = 2 * x := by
  rw [bound_wotsFUd_coefficient, show p24.w - 2 = 2 from by decide]
  norm_num

/-! ### The certificate, field by field

The eleven adversary fields are pinned at the games they are adversaries against, which is the
check that a summand is wired to the game its name says.  Nothing inside the library module pins
this: the field types are declared there and a paired edit moves them. -/

variable (c : Certificate (vp := toy) toyPrimitives adv)

example : PRFScheme.PRFAdversary Adrs toyPrimitives.Y := c.skgAdv
example : PRFScheme.PRFAdversary (toyPrimitives.Y × List Byte) toyPrimitives.Y := c.mkgAdv
example : toyPrimitives.PkSeed := c.pkSeed
example : ITSRAdversary (hmsgItsrProblem toyPrimitives) := c.itsrAdv
example : SM_DT_OpenPRE_SourceFinalValidity.Adversary (forsFOpenPreProblem toyPrimitives) :=
  c.openPreAdv
example : SM_DT_OpenPRE_SourceFinalValidity.CountingInterface c.openPreAdv := c.counting
example : SM_DT_TCR_SourceFinalValidity.Adversary (forsHTcrCProblem toyPrimitives) := c.forsHAdv
example : SM_DT_TCR_SourceFinalValidity.Adversary (forsTlTcrCProblem toyPrimitives) := c.forsTlAdv
example : SM_DT_UD_SourceFinalValidity.Adversary (wotsFUdCProblem toyPrimitives) := c.wotsFUdAdv
example : SM_DT_TCR_SourceFinalValidity.Adversary (wotsFTcrCProblem toyPrimitives) := c.wotsFTcrAdv
example : SM_DT_PRE_SourceFinalValidity.Adversary (wotsFPreCProblem toyPrimitives) := c.wotsFPreAdv
example : SM_DT_TCR_SourceFinalValidity.Adversary (wotsTlTcrCProblem toyPrimitives) := c.wotsTlAdv
example : SM_DT_TCR_SourceFinalValidity.Adversary (xmssHTcrCProblem toyPrimitives) := c.xmssHAdv

example : ℝ≥0∞ := c.idealAdvantage
example : ℝ≥0∞ := c.forsBranch
example : ℝ≥0∞ := c.hypertreeBranch

example : adv.advantage ProbCompRuntime.probComp ≤
    prfAbsAdvantage (skPrfScheme toyPrimitives c.pkSeed) c.skgAdv
      + prfAbsAdvantage (msgPrfScheme toyPrimitives) c.mkgAdv + c.idealAdvantage := c.prfHops

example : c.idealAdvantage ≤ c.forsBranch + c.hypertreeBranch := c.split

example : c.forsBranch ≤ ITSRAdvantage c.itsrAdv
    + SM_DT_OpenPRE_SourceFinalValidity.Advantage c.openPreAdv
    + SM_DT_TCR_SourceFinalValidity.Advantage c.forsHAdv
    + SM_DT_TCR_SourceFinalValidity.Advantage c.forsTlAdv := c.forsBranch_le

example : c.hypertreeBranch ≤
    (toy.params.w - 2 : ℕ) * SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage c.wotsFUdAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsFTcrAdv
      + SM_DT_PRE_SourceFinalValidity.Advantage c.wotsFPreAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsTlAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage c.xmssHAdv := c.hypertreeBranch_le

/-! ### The twelve summands, and the headline -/

noncomputable example : Summands := c.summands

example : c.summands.bound toy.params =
    prfAbsAdvantage (skPrfScheme toyPrimitives c.pkSeed) c.skgAdv
      + prfAbsAdvantage (msgPrfScheme toyPrimitives) c.mkgAdv
      + ITSRAdvantage c.itsrAdv
      + SM_DT_DSPR_SourceFinalValidity.Advantage
          (SM_DT_OpenPRE_SourceFinalValidity.toDSPR c.openPreAdv)
      + 3 * SM_DT_TCR_SourceFinalValidity.Advantage
          (SM_DT_OpenPRE_SourceFinalValidity.toTCR c.openPreAdv)
      + SM_DT_TCR_SourceFinalValidity.Advantage c.forsHAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage c.forsTlAdv
      + (toy.params.w - 2 : ℕ) *
          SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage c.wotsFUdAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsFTcrAdv
      + SM_DT_PRE_SourceFinalValidity.Advantage c.wotsFPreAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage c.wotsTlAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage c.xmssHAdv := c.bound_eq

example : adv.advantage ProbCompRuntime.probComp ≤ c.summands.bound toy.params :=
  advantage_le_bound c

/-! ### The branch-bounds constructor -/

section OfBranch

variable (skgAdv : PRFScheme.PRFAdversary Adrs toyPrimitives.Y)
  (mkgAdv : PRFScheme.PRFAdversary (toyPrimitives.Y × List Byte) toyPrimitives.Y)
  (pkSeed : toyPrimitives.PkSeed)
  (itsrAdv : ITSRAdversary (hmsgItsrProblem toyPrimitives))
  (openPreAdv : SM_DT_OpenPRE_SourceFinalValidity.Adversary (forsFOpenPreProblem toyPrimitives))
  (counting : SM_DT_OpenPRE_SourceFinalValidity.CountingInterface openPreAdv)
  (forsHAdv : SM_DT_TCR_SourceFinalValidity.Adversary (forsHTcrCProblem toyPrimitives))
  (forsTlAdv : SM_DT_TCR_SourceFinalValidity.Adversary (forsTlTcrCProblem toyPrimitives))
  (wotsFUdAdv : SM_DT_UD_SourceFinalValidity.Adversary (wotsFUdCProblem toyPrimitives))
  (wotsFTcrAdv : SM_DT_TCR_SourceFinalValidity.Adversary (wotsFTcrCProblem toyPrimitives))
  (wotsFPreAdv : SM_DT_PRE_SourceFinalValidity.Adversary (wotsFPreCProblem toyPrimitives))
  (wotsTlAdv : SM_DT_TCR_SourceFinalValidity.Adversary (wotsTlTcrCProblem toyPrimitives))
  (xmssHAdv : SM_DT_TCR_SourceFinalValidity.Adversary (xmssHTcrCProblem toyPrimitives))
  (hfors : forsHalf adv ≤ ITSRAdvantage itsrAdv
    + SM_DT_OpenPRE_SourceFinalValidity.Advantage openPreAdv
    + SM_DT_TCR_SourceFinalValidity.Advantage forsHAdv
    + SM_DT_TCR_SourceFinalValidity.Advantage forsTlAdv)
  (hhyper : hypertreeHalf adv ≤
    (toy.params.w - 2 : ℕ) * SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage wotsFUdAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage wotsFTcrAdv
      + SM_DT_PRE_SourceFinalValidity.Advantage wotsFPreAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage wotsTlAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage xmssHAdv)

noncomputable example : Certificate (vp := toy) toyPrimitives adv :=
  Certificate.ofBranchBounds (vp := toy) (prims := toyPrimitives) (adv := adv)
    skgAdv mkgAdv pkSeed itsrAdv openPreAdv counting forsHAdv forsTlAdv
    wotsFUdAdv wotsFTcrAdv wotsFPreAdv wotsTlAdv xmssHAdv hfors hhyper

example :
    (Certificate.ofBranchBounds (vp := toy) (prims := toyPrimitives) (adv := adv)
        skgAdv mkgAdv pkSeed itsrAdv openPreAdv counting forsHAdv
        forsTlAdv wotsFUdAdv wotsFTcrAdv wotsFPreAdv wotsTlAdv xmssHAdv hfors hhyper).summands =
      { skgPrf := prfAbsAdvantage (skPrfScheme toyPrimitives pkSeed) skgAdv
        mkgPrf := prfAbsAdvantage (msgPrfScheme toyPrimitives) mkgAdv
        hmsgItsr := ITSRAdvantage itsrAdv
        forsFDspr := SM_DT_DSPR_SourceFinalValidity.Advantage
          (SM_DT_OpenPRE_SourceFinalValidity.toDSPR openPreAdv)
        forsFTcr := SM_DT_TCR_SourceFinalValidity.Advantage
          (SM_DT_OpenPRE_SourceFinalValidity.toTCR openPreAdv)
        forsHTcr := SM_DT_TCR_SourceFinalValidity.Advantage forsHAdv
        forsTlTcr := SM_DT_TCR_SourceFinalValidity.Advantage forsTlAdv
        wotsFUd := SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage wotsFUdAdv
        wotsFTcr := SM_DT_TCR_SourceFinalValidity.Advantage wotsFTcrAdv
        wotsFPre := SM_DT_PRE_SourceFinalValidity.Advantage wotsFPreAdv
        wotsTlTcr := SM_DT_TCR_SourceFinalValidity.Advantage wotsTlAdv
        xmssHTcr := SM_DT_TCR_SourceFinalValidity.Advantage xmssHAdv } :=
  Certificate.ofBranchBounds_summands (vp := toy) (prims := toyPrimitives) (adv := adv)
    skgAdv mkgAdv pkSeed itsrAdv openPreAdv counting forsHAdv
    forsTlAdv wotsFUdAdv wotsFTcrAdv wotsFPreAdv wotsTlAdv xmssHAdv hfors hhyper

example : adv.advantage ProbCompRuntime.probComp ≤
    prfAbsAdvantage (skPrfScheme toyPrimitives pkSeed) skgAdv
      + prfAbsAdvantage (msgPrfScheme toyPrimitives) mkgAdv
      + ITSRAdvantage itsrAdv
      + SM_DT_DSPR_SourceFinalValidity.Advantage
          (SM_DT_OpenPRE_SourceFinalValidity.toDSPR openPreAdv)
      + 3 * SM_DT_TCR_SourceFinalValidity.Advantage
          (SM_DT_OpenPRE_SourceFinalValidity.toTCR openPreAdv)
      + SM_DT_TCR_SourceFinalValidity.Advantage forsHAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage forsTlAdv
      + (toy.params.w - 2 : ℕ) *
          SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage wotsFUdAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage wotsFTcrAdv
      + SM_DT_PRE_SourceFinalValidity.Advantage wotsFPreAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage wotsTlAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage xmssHAdv :=
  advantage_le_bound_of_halves (vp := toy) (prims := toyPrimitives) (adv := adv)
    skgAdv mkgAdv pkSeed itsrAdv openPreAdv counting forsHAdv
    forsTlAdv wotsFUdAdv wotsFTcrAdv wotsFPreAdv wotsTlAdv xmssHAdv hfors hhyper

end OfBranch

/-! ### The two transports, and the two theorems that consume them -/

example (εD : ℝ≥0∞)
    (h : ∀ a : SM_DT_DSPR_SourceFinalValidity.Adversary (forsFDsprProblem toyPrimitives),
      SM_DT_DSPR_SourceFinalValidity.Advantage a ≤ εD)
    (a : SM_DT_OpenPRE_SourceFinalValidity.Adversary (forsFOpenPreProblem toyPrimitives)) :
    SM_DT_DSPR_SourceFinalValidity.Advantage
      (SM_DT_OpenPRE_SourceFinalValidity.toDSPR a) ≤ εD :=
  dspr_bound_transfer (vp := toy) toyPrimitives εD h a

example (εT : ℝ≥0∞)
    (h : ∀ a : SM_DT_TCR_SourceFinalValidity.Adversary (forsFTcrProblem toyPrimitives),
      SM_DT_TCR_SourceFinalValidity.Advantage a ≤ εT)
    (a : SM_DT_OpenPRE_SourceFinalValidity.Adversary (forsFOpenPreProblem toyPrimitives)) :
    SM_DT_TCR_SourceFinalValidity.Advantage
      (SM_DT_OpenPRE_SourceFinalValidity.toTCR a) ≤ εT :=
  tcr_bound_transfer (vp := toy) toyPrimitives εT h a

example (εD εT : ℝ≥0∞)
    (hD : ∀ a : SM_DT_DSPR_SourceFinalValidity.Adversary (forsFDsprProblem toyPrimitives),
      SM_DT_DSPR_SourceFinalValidity.Advantage a ≤ εD)
    (hT : ∀ a : SM_DT_TCR_SourceFinalValidity.Adversary (forsFTcrProblem toyPrimitives),
      SM_DT_TCR_SourceFinalValidity.Advantage a ≤ εT) :
    c.summands.forsFDspr + 3 * c.summands.forsFTcr ≤ εD + 3 * εT :=
  summands_forsF_le c εD εT hD hT

example : SM_DT_OpenPRE_SourceFinalValidity.Advantage c.openPreAdv ≤
    c.summands.forsFDspr + 3 * c.summands.forsFTcr :=
  openPre_le_summands_forsF c

/-! ### The games the two `T_ℓ` summands are routed to, pinned by arity

The cap check of `checkTlDiscrimination` goes dark at `d = 1`; these two do not.  Each names the
attacked member at its own arity, which is `p.k` for the FORS compression and `p.len` for the
WOTS+ one, and the two arities differ at every profile this file carries. -/

example (pkSeed : toyPrimitives.PkSeed) (address : Adrs)
    (input : Vector toyPrimitives.Y toyParams.k) :
    (forsTlTcrCProblem toyPrimitives).th.eval pkSeed (toyPrimitives.adrsToKey address) input =
      toyPrimitives.Tl pkSeed address input.toList :=
  forsTlTcrCProblem_eval_adrsToKey toyPrimitives pkSeed address input

example (pkSeed : toyPrimitives.PkSeed) (address : Adrs)
    (input : Vector toyPrimitives.Y toyParams.len) :
    (wotsTlTcrCProblem toyPrimitives).th.eval pkSeed (toyPrimitives.adrsToKey address) input =
      toyPrimitives.Tl pkSeed address input.toList :=
  wotsTlTcrCProblem_eval_adrsToKey toyPrimitives pkSeed address input

/-! ### The caps the ten games declare, tied to `targetCount`

The runtime checks read `targetCount`; these tie each game's own `numTargets` field to it, so the
routing table's third column is about the games and not only about the cap function. -/

example : (forsFOpenPreProblem toyPrimitives).numTargets = targetCount toyParams .forsF :=
  forsFOpenPreProblem_numTargets toyPrimitives
example : (forsFDsprProblem toyPrimitives).numTargets = targetCount toyParams .forsF :=
  forsFDsprProblem_numTargets toyPrimitives
example : (forsFTcrProblem toyPrimitives).numTargets = targetCount toyParams .forsF :=
  forsFTcrProblem_numTargets toyPrimitives
example : (forsHTcrCProblem toyPrimitives).numTargets = targetCount toyParams .forsH :=
  forsHTcrCProblem_numTargets toyPrimitives
example : (forsTlTcrCProblem toyPrimitives).numTargets = targetCount toyParams .forsTl :=
  forsTlTcrCProblem_numTargets toyPrimitives
example : (wotsFUdCProblem toyPrimitives).numTargets = targetCount toyParams .wotsFUd :=
  wotsFUdCProblem_numTargets toyPrimitives
example : (wotsFTcrCProblem toyPrimitives).numTargets = targetCount toyParams .wotsFTcr :=
  wotsFTcrCProblem_numTargets toyPrimitives
example : (wotsFPreCProblem toyPrimitives).numTargets = targetCount toyParams .wotsFPre :=
  wotsFPreCProblem_numTargets toyPrimitives
example : (wotsTlTcrCProblem toyPrimitives).numTargets = targetCount toyParams .wotsTl :=
  wotsTlTcrCProblem_numTargets toyPrimitives
example : (xmssHTcrCProblem toyPrimitives).numTargets = targetCount toyParams .xmssH :=
  xmssHTcrCProblem_numTargets toyPrimitives

/-! ### The two `T_ℓ` games' separation, in general

The runtime group asserts the caps at three named profiles.  These three say what is true of every
validated parameter set: the caps separate the two `T_ℓ` compressions exactly when the hypertree
has more than one layer, and at one layer they coincide.  The fourth exhibits the consequence —
at a valid `d = 1` profile with `k = len` the two games are the *same term*, so no cap check, no
arity check and no attacked-member equation can distinguish them there. -/

example (p : Params) (h : p.Valid) (hd : p.d = 1) :
    targetCount p .forsTl = targetCount p .wotsTl := by
  rw [show targetCount p .forsTl = 2 ^ p.h from rfl,
    show targetCount p .wotsTl = wotsInstanceCount p from rfl,
    wotsInstanceCount_eq_xmssTreeCount_mul, xmssTreeCount_eq_geomSum, hd]
  simp [h.h_eq_layers, hd]

example (p : Params) (h : p.Valid) (hd : 2 ≤ p.d) :
    targetCount p .forsTl < targetCount p .wotsTl := by
  rw [show targetCount p .forsTl = 2 ^ p.h from rfl,
    show targetCount p .wotsTl = wotsInstanceCount p from rfl,
    wotsInstanceCount_eq_xmssTreeCount_mul, xmssTreeCount_eq_geomSum, h.h_eq_layers, pow_mul']
  have hlast : (2 ^ p.hp) ^ (p.d - 1) < ∑ i ∈ Finset.range p.d, (2 ^ p.hp) ^ i := by
    have hsub : ({p.d - 1, 0} : Finset ℕ) ⊆ Finset.range p.d := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
    calc (2 ^ p.hp) ^ (p.d - 1) < (2 ^ p.hp) ^ (p.d - 1) + (2 ^ p.hp) ^ 0 := by simp
      _ = ∑ i ∈ ({p.d - 1, 0} : Finset ℕ), (2 ^ p.hp) ^ i := by
          rw [Finset.sum_insert (by simp; omega), Finset.sum_singleton]
      _ ≤ ∑ i ∈ Finset.range p.d, (2 ^ p.hp) ^ i := Finset.sum_le_sum_of_subset hsub
  calc (2 ^ p.hp) ^ p.d = (2 ^ p.hp) ^ (p.d - 1) * 2 ^ p.hp := by
        rw [← pow_succ]; congr 1; omega
    _ < (∑ i ∈ Finset.range p.d, (2 ^ p.hp) ^ i) * 2 ^ p.hp :=
        (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hlast

/-- The other pair of same-shaped games is separated everywhere, with no side condition beyond
validity: the XMSS internal-node cap is `2 ^ h - 1` and the FORS one is at least `2 ^ h`. -/
example (p : Params) (h : p.Valid) : targetCount p .xmssH < targetCount p .forsH := by
  rw [targetCount_xmssH_eq p h]
  have hfors : 2 ^ p.h ≤ targetCount p .forsH := by
    rw [show targetCount p .forsH = 2 ^ p.h * p.k * (2 ^ p.a - 1) from rfl]
    calc 2 ^ p.h = 2 ^ p.h * 1 * 1 := by ring
      _ ≤ 2 ^ p.h * p.k * (2 ^ p.a - 1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ h.k_pos)
            (Nat.sub_pos_of_lt (Nat.one_lt_two_pow (Nat.ne_of_gt h.a_pos)))
  have hpos : 0 < 2 ^ p.h := Nat.two_pow_pos _
  omega

example (prims : Primitives collideParams) [SampleableType prims.PkSeed] :
    forsTlTcrCProblem prims = wotsTlTcrCProblem prims := rfl

/-! ### The ITSR game's shape

`KeyedHash.ITSRProblem` has exactly two fields and neither is a target cap, which is why the
`MCO_ITSR` summand has no `TargetRole` row and no cap of any other kind.  An added third field
fails this pin. -/

example (khf : CollisionResistance.KeyedHashFamily toyPrimitives.Y
      (HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y) (Bytes toyParams.m))
    (indices : Bytes toyParams.m → List (HmsgIndex toyParams)) :
    ITSRProblem toyPrimitives.Y (HmsgITSRInput toyPrimitives.PkSeed toyPrimitives.Y)
      (Bytes toyParams.m) (HmsgIndex toyParams) :=
  ⟨khf, indices⟩

/-! ### The profile pins -/

example : toyParams.w = 16 := by decide
example : toyParams.len = 4 := by decide
example : toyParams.k = 2 := by decide
example : toyParams.lgw = 4 := by decide
example : p24.w = 4 := by decide
example : p24.len = 68 := by decide
example : p24.k = 6 := by decide
example : p24.lgw = 2 := by decide
example : p24.d = 1 := by decide
example : p24.Valid := LimitedParameterSet.params_valid _
example : targetCount p24 .forsTl = targetCount p24 .wotsTl := by decide
example : targetCount toyParams .forsTl ≠ targetCount toyParams .wotsTl := by decide
example : degenerateParams.w - 2 = 0 := by decide
example : ¬ degenerateParams.Valid := by decide
example : widthTwoParams.w - 2 = 0 := by decide
example : widthTwoParams.Valid := by decide
example : collideParams.Valid := by decide
example : collideParams.k = collideParams.len := by decide
example : collideParams.d = 1 := by decide
example : targetCount collideParams .forsTl = targetCount collideParams .wotsTl := by decide
example (ps : FipsParameterSet) : ps.params.k ≠ ps.params.len := by cases ps <;> decide
example (ps : LimitedParameterSet) : ps.params.k ≠ ps.params.len := by cases ps; decide

end Pins

/-! ## The vacuity canary

Every other check in this file refuses a claim about a *definition*: a coefficient, a summand's
routing, a cap, a certificate field's type.  This one refuses a claim about the *hypotheses*, and
it is the first in this lane to do so.  It builds a closed `SLHDSA.Security.Certificate` — all
twenty fields supplied, all four inequalities proved — at an **arbitrary** `ValidatedParams`, an
arbitrary primitive bundle carrying the instances the structure asks for, and an arbitrary
adversary, from an address key and a public seed and no security assumption whatever; and it
proves that the bound that certificate names is at least one.  `advantage_le_bound` at it is
`adv.advantage ≤ (something ≥ 1)`, which `probOutput_le_one` already gives.

What it is for.  Three docstrings in the library module, this file, and the pull-request body once
said that no route to a certificate was known which avoided proving something hard.  Shipping the
route as a checked fact is what keeps that reading from coming back.  Measured, against the two
changes that would make the bound mean something:

* **Anchoring.**  Add `forsBranch_ge : forsHalf adv ≤ forsBranch` to `Certificate` and repair
  `Certificate.ofBranchBounds` with `le_refl`: the library elaborates clean and this file has
  **one** error, `Fields missing`, at `freeCertificate`.  With this section deleted the file has
  **none**, so the canary is the sole refusal and no pin sees the change.  No repair of
  `freeCertificate` is known: taking `forsBranch := forsHalf adv` turns `forsBranch_le` into the
  FORS-branch bound itself, which is the open question below.
* **A reduction field.**  Make `wotsFPreAdv` a function `unforgeableAdv (generalAlg prims) → _`
  at its four declaration sites: the library again elaborates clean and this file has **eighteen**
  errors, nine in `Pins` and nine here.  These nine go away under a one-line repair,
  `wotsFPreAdv := fun _ => freePreAdv prims t`, because a field of function type is still freely
  chosen.  So this canary *notifies* on that change; only fixing the function at the structure,
  which deletes the field, refuses it.

What it does not say.  It is not a soundness bug: `advantage_le_bound` is true and its proof is
correct.  It says that the antecedent is free, so the implication carries no information about
SLH-DSA.  The library module's "A certificate costs nothing" records what would change that.

The two games that do the work are the two whose winning conditions have no distinctness clause.
`SM_DT_PRE_SourceFinalValidity` accepts on `th.eval pk t (emb m) = th.eval pk t (emb x)`, and
`SM_DT_OpenPRE_SourceFinalValidity` on `th.eval pk t m = th.eval pk t x`; both hand the adversary
an image the game has just computed, so the fibre is non-empty and `Function.invFun` wins.  The
five target-collision games and the decisional game do carry one, and none of them is driven
anywhere here.  `winningOpenPre` is included because the FORS branch's only such game is the
open-preimage one, and what stops it from making the FORS branch free as well is the `counting`
field: the interface below is inhabited at `idleOpenPre`, whose advantage is zero, and whether one
exists at `winningOpenPre`, whose advantage is one, is open.  `winningOpenPre_advantage` needs
nothing of the input distribution, not even `HasUniformInputs` — measured by removing it. -/

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

-- Exposed, and it is the only one of the six adversaries here that needs to be; measured by
-- removing each attribute alone.  Inside this file's `public section` a definition's body is not
-- available to later declarations, so `(Problem.toDSPR (idleOpenPre prob)).State` does not reduce
-- to `Unit × _ × _` and `idleOpenPre_toDSPR_choose` cannot even be stated: three errors, a
-- `Type mismatch` at that statement, the `unknownIdentifier` it causes in `idleOpenPre_dspr`, and
-- that theorem's `unsolved goals`.
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

/-! ### The two games with no distinctness clause -/

/-- Classical inversion of the open-preimage game's attacked map at one seed and one tweak. -/
noncomputable def openPreInverse {ix PkS Tw Msg Nd : Type} [Nonempty Msg]
    (prob : SM_DT_OpenPRE_SourceFinalValidity.Problem ix PkS Tw Msg Nd) (pk : PkS) (t : Tw) :
    Nd → Msg :=
  Function.invFun (fun m => prob.th.eval pk t m)

theorem openPreInverse_eval {ix PkS Tw Msg Nd : Type} [Nonempty Msg]
    (prob : SM_DT_OpenPRE_SourceFinalValidity.Problem ix PkS Tw Msg Nd) (pk : PkS) (t : Tw)
    (a : Msg) :
    prob.th.eval pk t (openPreInverse prob pk t (prob.th.eval pk t a)) = prob.th.eval pk t a :=
  Function.invFun_eq (f := fun m => prob.th.eval pk t m) ⟨a, rfl⟩

/-- One committed target, nothing opened, and the revealed image inverted classically. -/
noncomputable def winningOpenPre {ix PkS Tw Msg Nd : Type} [Nonempty Msg] [Inhabited Nd]
    (prob : SM_DT_OpenPRE_SourceFinalValidity.Problem ix PkS Tw Msg Nd) (t : Tw) :
    SM_DT_OpenPRE_SourceFinalValidity.Adversary prob where
  State := Unit
  pick := pure ((), [t])
  find := fun _ pk ys => pure (0, openPreInverse prob pk t (ys.headD default))

/-- **Open-preimage resistance is unconditionally false in this model.**  The winning condition is
an equality of images with no `m ≠ x` clause, the target the adversary must invert is unopened
because it opened nothing, and one committed tweak is inside every positive cap. -/
theorem winningOpenPre_advantage {ix PkS Tw Msg Nd : Type} [DecidableEq Tw] [DecidableEq Nd]
    [Inhabited Msg] [Inhabited Nd]
    (prob : SM_DT_OpenPRE_SourceFinalValidity.Problem ix PkS Tw Msg Nd) (t : Tw)
    (h : 0 < prob.numTargets) :
    SM_DT_OpenPRE_SourceFinalValidity.Advantage (winningOpenPre prob t) = 1 := by
  have htake : List.take prob.numTargets [t] = [t] :=
    List.take_of_length_le (by simpa using Nat.succ_le_of_lt h)
  unfold SM_DT_OpenPRE_SourceFinalValidity.Advantage
    SM_DT_OpenPRE_SourceFinalValidity.Experiment
  simp [winningOpenPre, htake, openPreInverse_eval, h,
    SM_DT_OpenPRE_SourceFinalValidity.initializeTargets,
    SourceFinalValidity.State.initial, SourceFinalValidity.State.recordTarget,
    TweakableHash.TweakFresh, TweakableHash.TweakReserved]

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

/-- **The headline at that certificate.**  Both conjuncts together are the whole canary: the
conditional bound holds, and what it bounds the advantage by is at least one. -/
theorem freeCertificate_headline {adv : unforgeableAdv (generalAlg prims)}
    (t : prims.AdrsKey) (pkSeed : prims.PkSeed) :
    adv.advantage ProbCompRuntime.probComp ≤
        (freeCertificate (adv := adv) t pkSeed).summands.bound vp.params ∧
      1 ≤ (freeCertificate (adv := adv) t pkSeed).summands.bound vp.params :=
  ⟨advantage_le_bound _, one_le_freeCertificate_bound t pkSeed⟩

end Closed

/-! ### The same three facts at the toy bundle

The section above is at an arbitrary `ValidatedParams` and an arbitrary bundle; these restate it
at the profile the rest of this file uses, so a change that breaks only the concrete case is
caught too. -/

example (t : Adrs) :
    SM_DT_PRE_SourceFinalValidity.Advantage (freePreAdv (vp := toy) toyPrimitives t) = 1 :=
  freePreAdv_advantage (vp := toy) toyPrimitives t

example (t : Adrs) :
    SM_DT_OpenPRE_SourceFinalValidity.Advantage
      (winningOpenPre (forsFOpenPreProblem toyPrimitives) t) = 1 :=
  winningOpenPre_advantage (forsFOpenPreProblem toyPrimitives) t (by
    rw [forsFOpenPreProblem_numTargets]
    exact targetCount_pos toyParams toyValid TargetRole.forsF)

noncomputable example (t : Adrs) (pkSeed : toyPrimitives.PkSeed)
    (adv : unforgeableAdv (generalAlg (vp := toy) toyPrimitives)) :
    Certificate (vp := toy) toyPrimitives adv :=
  freeCertificate (vp := toy) (prims := toyPrimitives) (adv := adv) t pkSeed

example (t : Adrs) (pkSeed : toyPrimitives.PkSeed)
    (adv : unforgeableAdv (generalAlg (vp := toy) toyPrimitives)) :
    adv.advantage ProbCompRuntime.probComp ≤
        (freeCertificate (vp := toy) (prims := toyPrimitives) (adv := adv) t pkSeed).summands.bound
          toy.params ∧
      1 ≤ (freeCertificate (vp := toy) (prims := toyPrimitives) (adv := adv) t
          pkSeed).summands.bound toy.params :=
  freeCertificate_headline (vp := toy) (prims := toyPrimitives) (adv := adv) t pkSeed

/-! ### The certificate anchoring does not refuse

`freeCertificate` is refused by anchoring, because its `forsBranch` is `0`.  A certificate is not.
The one below sets the three `ℝ≥0∞` fields to `adv.advantage`, `forsHalf adv` and
`hypertreeHalf adv`, which are the three values the anchoring inequalities ask for, so each of them
holds at it by `le_refl`; the three `example`s after it are those inequalities, and they are what
the `@[expose]` is for.  Each branch bound is then the same chain — the half is at most the
advantage, the advantage is at most one, and one is the advantage of a game on that branch whose
winning condition has no distinctness clause.  The FORS side has one, the open-preimage game, which
is why `forsBranch := forsHalf adv` is not an obstacle; the hypertree side has the preimage game.

What this certificate does not supply is `counting`, now asked for at an adversary of advantage one
rather than zero.  That is the whole of what anchoring buys, and the next subsection says what it
amounts to. -/

section Anchored

variable {vp : ValidatedParams} {prims : Primitives vp.params}
  [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.PkSeed]
  [SampleableType prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey]
  [DecidableEq prims.Y] [Fintype prims.Y] [Inhabited prims.Y]

omit [Fintype prims.Y] in
/-- **The FORS branch bound holds at the winning open-preimage adversary**, for every adversary and
with the branch stated at `forsHalf adv` itself.  The right-hand side's second summand is the
OpenPRE advantage, which `winningOpenPre_advantage` makes one, so the chain lands. -/
theorem forsHalf_le_winningOpenPre {adv : unforgeableAdv (generalAlg prims)} (t : prims.AdrsKey)
    (itsrAdv : ITSRAdversary (hmsgItsrProblem prims))
    (forsHAdv : SM_DT_TCR_SourceFinalValidity.Adversary (forsHTcrCProblem prims))
    (forsTlAdv : SM_DT_TCR_SourceFinalValidity.Adversary (forsTlTcrCProblem prims)) :
    forsHalf adv ≤ ITSRAdvantage itsrAdv
      + SM_DT_OpenPRE_SourceFinalValidity.Advantage (winningOpenPre (forsFOpenPreProblem prims) t)
      + SM_DT_TCR_SourceFinalValidity.Advantage forsHAdv
      + SM_DT_TCR_SourceFinalValidity.Advantage forsTlAdv := by
  calc forsHalf adv ≤ adv.advantage ProbCompRuntime.probComp := forsHalf_le_advantage adv
    _ ≤ 1 := probOutput_le_one
    _ = SM_DT_OpenPRE_SourceFinalValidity.Advantage
          (winningOpenPre (forsFOpenPreProblem prims) t) :=
        (winningOpenPre_advantage _ t (by
          rw [forsFOpenPreProblem_numTargets]
          exact targetCount_pos vp.params vp.valid TargetRole.forsF)).symm
    _ ≤ _ := le_add_right (le_add_right le_add_self)

omit [DecidableEq prims.PkSeed] [Fintype prims.Y] [Inhabited prims.Y] in
/-- **The hypertree branch bound holds at the free preimage adversary**, with the branch stated at
`hypertreeHalf adv` itself.  This is the same chain as the FORS one, landing on the preimage
summand instead. -/
theorem hypertreeHalf_le_freePre {adv : unforgeableAdv (generalAlg prims)} (t : prims.AdrsKey)
    (wotsFUdAdv : SM_DT_UD_SourceFinalValidity.Adversary (wotsFUdCProblem prims))
    (wotsFTcrAdv : SM_DT_TCR_SourceFinalValidity.Adversary (wotsFTcrCProblem prims))
    (wotsTlAdv : SM_DT_TCR_SourceFinalValidity.Adversary (wotsTlTcrCProblem prims))
    (xmssHAdv : SM_DT_TCR_SourceFinalValidity.Adversary (xmssHTcrCProblem prims)) :
    hypertreeHalf adv ≤
      (vp.params.w - 2 : ℕ) * SM_DT_UD_SourceFinalValidity.AbsoluteAdvantage wotsFUdAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage wotsFTcrAdv
        + SM_DT_PRE_SourceFinalValidity.Advantage (freePreAdv prims t)
        + SM_DT_TCR_SourceFinalValidity.Advantage wotsTlAdv
        + SM_DT_TCR_SourceFinalValidity.Advantage xmssHAdv := by
  calc hypertreeHalf adv ≤ adv.advantage ProbCompRuntime.probComp := hypertreeHalf_le_advantage adv
    _ ≤ 1 := probOutput_le_one
    _ = SM_DT_PRE_SourceFinalValidity.Advantage (freePreAdv prims t) :=
        (freePreAdv_advantage prims t).symm
    _ ≤ _ := le_add_right (le_add_right le_add_self)

-- Exposed so that the three anchoring inequalities below can be `le_refl`: without the attribute
-- this file's later declarations cannot see that the three `ℝ≥0∞` fields are the anchored values.
/-- **A `Certificate` whose three named quantities are the experiment's own.**  The two arguments
that are data are an address key and a public seed, as in `freeCertificate`; the third is a
`CountingInterface` at an adversary whose advantage is one, which is the one input that is not
data and is not known to exist. -/
@[expose] noncomputable def anchoredCertificate {adv : unforgeableAdv (generalAlg prims)}
    (t : prims.AdrsKey) (pkSeed : prims.PkSeed)
    (counting : SM_DT_OpenPRE_SourceFinalValidity.CountingInterface
      (winningOpenPre (forsFOpenPreProblem prims) t)) :
    Certificate prims adv where
  skgAdv := (pure true : OracleComp (PRFScheme.PRFOracleSpec Adrs prims.Y) Bool)
  mkgAdv := (pure true :
    OracleComp (PRFScheme.PRFOracleSpec (prims.Y × List Byte) prims.Y) Bool)
  pkSeed := pkSeed
  itsrAdv := ⟨(pure (default, ⟨pkSeed, default, []⟩) :
    OracleComp (unifSpec + ITSRTargetSpec (HmsgITSRInput prims.PkSeed prims.Y) prims.Y)
      (prims.Y × HmsgITSRInput prims.PkSeed prims.Y))⟩
  openPreAdv := winningOpenPre (forsFOpenPreProblem prims) t
  counting := counting
  forsHAdv := idleTcr _
  forsTlAdv := idleTcr _
  wotsFUdAdv := idleUd _
  wotsFTcrAdv := idleTcr _
  wotsFPreAdv := freePreAdv prims t
  wotsTlAdv := idleTcr _
  xmssHAdv := idleTcr _
  idealAdvantage := adv.advantage ProbCompRuntime.probComp
  forsBranch := forsHalf adv
  hypertreeBranch := hypertreeHalf adv
  prfHops := le_add_self
  split := advantage_le_forsHalf_add_hypertreeHalf adv
  forsBranch_le := forsHalf_le_winningOpenPre t _ _ _
  hypertreeBranch_le := hypertreeHalf_le_freePre t _ _ _ _

/-- **The bound that certificate names is at least one too**, for the same reason
`freeCertificate`'s is: the preimage summand is one. -/
theorem one_le_anchoredCertificate_bound {adv : unforgeableAdv (generalAlg prims)}
    (t : prims.AdrsKey) (pkSeed : prims.PkSeed)
    (counting : SM_DT_OpenPRE_SourceFinalValidity.CountingInterface
      (winningOpenPre (forsFOpenPreProblem prims) t)) :
    1 ≤ (anchoredCertificate (adv := adv) t pkSeed counting).summands.bound vp.params := by
  rw [Certificate.bound_eq]
  calc (1 : ℝ≥0∞) = SM_DT_PRE_SourceFinalValidity.Advantage (freePreAdv prims t) :=
        (freePreAdv_advantage prims t).symm
    _ ≤ _ := le_add_right (le_add_right le_add_self)

/-! The three inequalities a full anchoring would add to `Certificate`, at this certificate. -/

example (adv : unforgeableAdv (generalAlg prims)) (t : prims.AdrsKey) (pkSeed : prims.PkSeed)
    (counting : SM_DT_OpenPRE_SourceFinalValidity.CountingInterface
      (winningOpenPre (forsFOpenPreProblem prims) t)) :
    (anchoredCertificate (adv := adv) t pkSeed counting).idealAdvantage ≤
      adv.advantage ProbCompRuntime.probComp := le_refl _

example (adv : unforgeableAdv (generalAlg prims)) (t : prims.AdrsKey) (pkSeed : prims.PkSeed)
    (counting : SM_DT_OpenPRE_SourceFinalValidity.CountingInterface
      (winningOpenPre (forsFOpenPreProblem prims) t)) :
    forsHalf adv ≤ (anchoredCertificate (adv := adv) t pkSeed counting).forsBranch := le_refl _

example (adv : unforgeableAdv (generalAlg prims)) (t : prims.AdrsKey) (pkSeed : prims.PkSeed)
    (counting : SM_DT_OpenPRE_SourceFinalValidity.CountingInterface
      (winningOpenPre (forsFOpenPreProblem prims) t)) :
    hypertreeHalf adv ≤
      (anchoredCertificate (adv := adv) t pkSeed counting).hypertreeBranch := le_refl _

end Anchored

/-- The same certificate at the toy bundle.  There is no unconditional form of this one: the
counting interface is a hypothesis here because nothing constructs it. -/
noncomputable example (t : Adrs) (pkSeed : toyPrimitives.PkSeed)
    (adv : unforgeableAdv (generalAlg (vp := toy) toyPrimitives))
    (counting : SM_DT_OpenPRE_SourceFinalValidity.CountingInterface
      (winningOpenPre (forsFOpenPreProblem toyPrimitives) t)) :
    Certificate (vp := toy) toyPrimitives adv :=
  anchoredCertificate (vp := toy) (prims := toyPrimitives) (adv := adv) t pkSeed counting

/-! ### What the counting interface costs where it is not free

The interface is a proof obligation about masses, and at an adversary that wins outright it looks
like a question about that structure.  It is not: at any open-preimage adversary of advantage one,
over a finite input type with at least two elements and with uniformly sampled inputs, the
interface exists exactly when `1 ≤ TCRDSPRBound` holds — that is, exactly when the adversary's two
induced reductions satisfy `DSPR + 3 · TCR ≥ 1`.

The forward direction is `advantage_le_tcrDsprBound` at the winning advantage.  The reverse is a
construction, and where it puts its mass is the interesting part: everything on the stratum of
fibre size two, `singleMass := 1 - 2d` and `multipleMass 0 := 2d` with `d := (1 - DSPR) / 3`.  At
that stratum the reciprocal and collision masses are both `d`, the two decompositions read
`1 = (1 - 2d) + 2d` and `(1 - 2d) - d = DSPR`, and the strata inequality reads `d ≤ TCR`, which is
`1 ≤ DSPR + 3 · TCR` rearranged.  Fibre size two is where the source's factor of three comes from —
at fibre size `n` the same construction needs `(n - 1)(1 - DSPR) / (n + 1) ≤ TCR`, which is
weakest at `n = 2`.

So the question the previous subsection leaves is not about the interface's shape.  It is whether
`winningOpenPre`'s own two induced reductions satisfy that inequality, and that turns on which
preimage the adversary returns: `openPreInverse` is `Function.invFun`, which is `Classical.choose`
of a non-empty fibre, and nothing in the model says whether what it returns is the sampled target
or a different preimage of the same image.  Neither the inequality nor its negation is proved here
at that adversary.  An adversary that sampled its preimage uniformly from the fibre instead would
satisfy it — the conditional law of the target given its image is uniform on the fibre when the
inputs are, so the returned preimage differs from the target often enough — but that argument is a
paper one, and what it needs to become a checked one is exactly the conditional-distribution
coupling VCVio calls "the substantive probabilistic coupling still to be constructed".  So the
reading this file supports is that anchoring very probably closes nothing, and that settling it
needs the coupling the library leaves open. -/

section Counting

/-- The DSPR advantage is a truncated difference of probabilities, so it never exceeds one. -/
theorem dspr_advantage_le_one {ix PkS Tw Msg Nd : Type} [Fintype Msg] [DecidableEq Tw]
    [DecidableEq Msg] [DecidableEq Nd]
    {prob : SM_DT_DSPR_SourceFinalValidity.Problem ix PkS Tw Msg Nd}
    (a : SM_DT_DSPR_SourceFinalValidity.Adversary prob) :
    SM_DT_DSPR_SourceFinalValidity.Advantage a ≤ 1 :=
  le_trans tsub_le_self probOutput_le_one

/-- **The counting interface exists at a winning adversary exactly when its two reductions sum
to one.**  Both directions: the forward one is VCVio's own inequality at an advantage of one, and
the reverse puts all the mass on the fibre-size-two stratum. -/
theorem nonempty_countingInterface_iff {ix PkS Tw Msg Nd : Type} [Fintype Msg] [Inhabited Msg]
    [SampleableType Msg] [DecidableEq Tw] [DecidableEq Msg] [DecidableEq Nd]
    {prob : SM_DT_OpenPRE_SourceFinalValidity.Problem ix PkS Tw Msg Nd}
    (adv : SM_DT_OpenPRE_SourceFinalValidity.Adversary prob)
    (hu : prob.HasUniformInputs) (hcard : 2 ≤ Fintype.card Msg)
    (hone : SM_DT_OpenPRE_SourceFinalValidity.Advantage adv = 1) :
    Nonempty (SM_DT_OpenPRE_SourceFinalValidity.CountingInterface adv) ↔
      1 ≤ SM_DT_OpenPRE_SourceFinalValidity.TCRDSPRBound adv := by
  constructor
  · rintro ⟨hc⟩
    have h := SM_DT_OpenPRE_SourceFinalValidity.advantage_le_tcrDsprBound adv hc
    rwa [hone] at h
  · intro h
    have : NeZero (Fintype.card Msg - 1) := ⟨by omega⟩
    set D := SM_DT_DSPR_SourceFinalValidity.Advantage
      (SM_DT_OpenPRE_SourceFinalValidity.toDSPR adv) with hD
    set T := SM_DT_TCR_SourceFinalValidity.Advantage
      (SM_DT_OpenPRE_SourceFinalValidity.toTCR adv) with hT
    have hD1 : D ≤ 1 := dspr_advantage_le_one _
    set e : ℝ≥0∞ := 1 - D with he
    set d : ℝ≥0∞ := e / 3 with hd
    have h3 : (3 : ℝ≥0∞) ≠ 0 := by norm_num
    have h3t : (3 : ℝ≥0∞) ≠ ⊤ := by norm_num
    have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
    have h2t : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
    have h3d : 3 * d = e := by rw [hd]; exact ENNReal.mul_div_cancel h3 h3t
    have hhalf : (1 : ℝ≥0∞) / 2 * (2 * d) = d := by
      rw [one_div, ← mul_assoc, ENNReal.inv_mul_cancel h2 h2t, one_mul]
    have hsum : 2 * d + 1 / 2 * (2 * d) = e := by rw [hhalf, ← h3d]; ring
    have hc1 : 2 * d ≤ 1 := by
      calc 2 * d ≤ 3 * d := by gcongr; norm_num
        _ = e := h3d
        _ ≤ 1 := tsub_le_self
    have hTle : d ≤ T := by
      rw [hd]
      refine ENNReal.div_le_of_le_mul ?_
      rw [he, tsub_le_iff_right]
      calc (1 : ℝ≥0∞) ≤ SM_DT_OpenPRE_SourceFinalValidity.TCRDSPRBound adv := h
        _ = D + 3 * T := rfl
        _ = T * 3 + D := by ring
    exact ⟨{ uniformInputs := hu
             singleMass := 1 - 2 * d
             multipleMass := fun k => if k = 0 then 2 * d else 0
             openPRE_decomposition := by
               rw [hone]
               simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
               exact (tsub_add_cancel_of_le hc1).symm
             dspr_decomposition := by
               rw [SM_DT_OpenPRE_SourceFinalValidity.reciprocalMass]
               simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
                 Fin.val_zero, zero_add, Nat.cast_ofNat]
               rw [tsub_tsub, hsum, he]
               exact (ENNReal.sub_sub_cancel one_ne_top hD1).symm
             tcr_strata_le := by
               rw [SM_DT_OpenPRE_SourceFinalValidity.collisionMass]
               simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
                 Fin.val_zero, zero_add, Nat.cast_ofNat]
               rw [show ((2 - 1 : ℕ) : ℝ≥0∞) = 1 by norm_num, hhalf]
               exact hTle }⟩

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  [SampleableType prims.PkSeed] [SampleableType prims.Y] [DecidableEq prims.AdrsKey]
  [DecidableEq prims.Y] [Fintype prims.Y] [Inhabited prims.Y]

/-- **The open question, at the adversary the anchored certificate uses.**  The FORS-`F`
open-preimage problem has uniform inputs and `winningOpenPre` wins it, so what is left of
`anchoredCertificate`'s missing field is one inequality between two advantages. -/
theorem nonempty_counting_winningOpenPre_iff (t : prims.AdrsKey)
    (hcard : 2 ≤ Fintype.card prims.Y) :
    Nonempty (SM_DT_OpenPRE_SourceFinalValidity.CountingInterface
        (winningOpenPre (forsFOpenPreProblem prims) t)) ↔
      1 ≤ SM_DT_OpenPRE_SourceFinalValidity.TCRDSPRBound
        (winningOpenPre (forsFOpenPreProblem prims) t) :=
  nonempty_countingInterface_iff _ (forsFOpenPreProblem_hasUniformInputs prims) hcard
    (winningOpenPre_advantage _ t (by
      rw [forsFOpenPreProblem_numTargets]
      exact targetCount_pos vp.params vp.valid TargetRole.forsF))

end Counting

end Vacuity

/-- Run the four check groups in order, then report. -/
def main : IO Unit := do
  checkCoefficients
  checkCaps
  checkTlDiscrimination
  checkRouting
  IO.println "SLH-DSA composition tests: PASS"

end SLHDSA.CompositionTest

/-- Entry point for `slhdsa_composition_tests`. -/
def main : IO Unit := SLHDSA.CompositionTest.main
