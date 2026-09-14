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
`HashSig.SLHDSA.Security.CanonicalGames`, and those games' target caps — together with one
elaboration pin per exported declaration of that module.

## Nothing about the bound itself is runnable, and that is a property of the subject

`Summands.bound` is `ℝ≥0∞`-valued and every advantage it is built from is `noncomputable`, so the
headline `advantage_le_bound`, the certificate, the two transports and every statement about a
probability have **no runtime coverage at all** and cannot be given any.  The runtime checks below
are about `Params`-level data only: `p.w - 2`, `SLHDSA.Security.targetCount`, and a routing table
this file writes down.  What pins the bound's own shape is the `Pins` section, which restates each
of the twenty exported declarations, and mutation testing against those pins.

A reader of the seven other fixtures in this lane will look for the headline among the runtime
checks; it is not there, and no fixture could put it there.

## The two profiles, and why there are two

`toyParams` is the two-layer profile of the scheme-dispatch, SUF-residual and scheme-game fixtures,
copied rather than imported for the reason those files give: a `lean_exe` root must own its `main`,
and a module that imports another fixture cannot declare one.  The primitive bundle is theirs
verbatim; what this file drops is the exclusive-or fold, which only that file's `H_msg` blindness
assertion used, and every message, signature and log, because no reader here reads one.

`SLHDSA.LimitedParameterSet.SLHDSA_SHA2_128_24` is here as a bare `Params`, with no primitive
bundle, because it is the profile at which the summand-to-game routing has a cell that goes dark.
At `d = 1` the FORS `T_k` and WOTS+ `T_len` compressions have **the same cap** — both `2 ^ 22` —
so a cap check alone cannot tell the two `T_ℓ` games apart there, which is the most plausible
mis-wiring in the module since they are both target-collision games on the shared collection.  This
file asserts that coincidence rather than hiding it, and pairs the cap check with an arity check:
`k = 6` against `len = 68`.  At `toyParams` the two caps differ, 16 against 20, so the two-layer
profile is where a cap check does discriminate.

## The reader-by-log matrix is empty, by construction

The lane's other fixtures carry two or three signing logs and a matrix of readers against them.
This one carries none: its three readers — the coefficient `p.w - 2`, the cap function
`targetCount`, and the routing table — are functions of a `Params` and of nothing else.  No log
could change any of their values, so no log is carried and the matrix has no rows.  The dispatch
selector and the logged-randomizer predicate are `HashSigTest.SLHDSA.SchemeGames`' readers and are
exercised there.

## What the checks cannot catch

* **A paired edit of the `w − 2` coefficient.**  Nothing in the repository derives it.  Changing it
  in `Summands.bound` *and* in `Certificate.hypertreeBranch_le` together gives a consistent,
  compiling, differently scaled theorem, and the only checks that see it are the `Pins` entries in
  this file, which restate both statements with the coefficient in them.  A reviewer who changes
  both and this file has changed the claim, not found a bug in it.
* **Anything about a probability.**  See above.
* **Whether the summands are the source's.**  The routing table below says which Lean game each
  summand is the advantage of; that the twelve games are the source's twelve is a reading of
  `SPHINCS_PLUS.ec`, `FORS_ES.ec`, `FL_SL_XMSS_MT_ES.ec` and `WOTS_TW_ES.ec`, recorded in the
  library module's docstring, and no fixture can check it.

## What is here

Fifty-three runtime checks in four groups — the two coefficients (14), the eight caps at both
profiles (16), the `T_ℓ` discrimination and its arity pairing (10), and the routing table (13) —
and sixty-six `example`s in `Pins`, at least one for each of the twenty declarations the library
module exports, plus the two `T_ℓ` attacked-member equations, the ten games' declared caps and the
fourteen profile pins.

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
-- this file: nineteen, no error ceiling reached, the first inside the bundle below at
-- `yToBytes := id`, `Type mismatch: id`, and the rest one `(kernel) declaration type mismatch`
-- and one code-generation failure at each of the nine instances written at `toyPrimitives`.
/-- Two layers of height two, two FORS trees of height one. -/
@[expose] def toyParams : Params :=
  { n := 1, h := 4, d := 2, hp := 2, a := 1, k := 2, lgw := 4 }

/-- The toy parameters are valid. -/
theorem toyValid : toyParams.Valid := by decide

-- Exposed for a different reason from `toyParams`, also read off its removal: eight errors, none
-- of them in the bundle and all of them in the pins, where the certificate's own `vp` has to
-- reduce to `toyParams` for the bundle's instances to be found.  Five are `typeclass instance
-- problem is stuck` on `DecidableEq ?m` and three `failed to synthesize`.
/-- The validated form of `toyParams`. -/
@[expose] def toy : ValidatedParams := ⟨toyParams, toyValid⟩

/-- The SP 800-230 reduced parameter set, as a bare `Params`: the profile at which the two `T_ℓ`
caps coincide.  No primitive bundle is built at it here. -/
def p24 : Params := LimitedParameterSet.params .SLHDSA_SHA2_128_24

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

-- Exposed for code generation, and that is the whole of it: without the attribute, twenty-nine
-- errors, every one of them `Compilation failed, locally inferred compilation type differs from
-- type that would be inferred in other modules`, two at each of the nine instances and the rest at
-- the definitions that read the carrier.  `@[reducible]`, which the scheme-game fixture's copy of
-- this bundle also carries, is *not* needed here and is not written: removing it alone leaves the
-- build at zero errors, because no check below resolves an instance through the carrier by
-- unfolding it — the nine instances name `Bytes 1` and `Adrs` directly.
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
`TargetRole`: its transcript is capped by the number of signing queries and the `k` indices each
digest selects, not by a structural ledger. -/

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
  -- the truncation `two_le_w` rules out, exhibited at a parameter set where it fires
  ensure "degenerate w" (degenerateParams.w == 1)
  ensure "degenerate w - 2 truncates to zero" (degenerateParams.w - 2 == 0)
  ensure "degenerate is not valid" (!decide degenerateParams.Valid)
  ensure "toy is valid" (decide toyParams.Valid)
  ensure "p24 is valid" (decide p24.Valid)

/-- **The twelve caps, at both profiles.**  Each summand with a role, against
`SLHDSA.Security.targetCount` at that role. -/
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

/-- **The cell that goes dark, and the arity check that is paired with it.**  The two `T_ℓ`
compressions are both target-collision games on the shared `Thash` collection; at `d = 1` their caps
coincide, so at the profile the corollary of the next pull request will use, a cap check alone
cannot tell `forsTlTcrCProblem` from `wotsTlTcrCProblem`.  The arity does tell them apart at both
profiles, and so does the `th` each game fixes, which the `Pins` section restates. -/
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

Every one of the twenty declarations `HashSig.SLHDSA.Security.Composition` exports, restated at this
bundle's types, with generic arguments where the statement has them.  These are the only check on
the bound's own shape: a library-side edit of a coefficient, of a summand's routing, or of a
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

The twelve adversary fields are pinned at the games they are adversaries against, which is the
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

/-! ### The anti-vacuity constructor -/

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

/-! ### The caps the twelve games declare, tied to `targetCount`

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

end Pins

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
