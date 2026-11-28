/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.CanonicalGames
public import HashSig.SLHDSA.Security.LimitedProfile

/-!
# SLH-DSA-SHA2-128-24 profile canaries

Executable checks for the decidable data of `HashSig.SLHDSA.Security.LimitedProfile` — the reduced
profile's parameters and the sizes they derive, the eight target caps, arithmetic relations between
them, and the two cells where caps coincide — together with one elaboration pin per exported
declaration of that module, the ten canonical games' caps read at the concrete bundle, and every
game's arity read off its own attacked-member equation.

## The two cells that go dark at this profile, both asserted rather than hidden

* **The two `T_ℓ` compressions.**  `forsTlTcrCProblem` and `wotsTlTcrCProblem` are both
  target-collision games on the shared `Thash` collection, and at `d = 1` their caps coincide —
  `2 ^ 22` here.  What separates them is the arity, `p.k = 6` against `p.len = 68`, which `Pins`
  reads off the two games' own attacked-member equations, where the message type is
  `Vector limitedPrimitives.Y 6` in one and `Vector limitedPrimitives.Y 68` in the other.
  `HashSigTest.SLHDSA.CanonicalGameCaps` proves the cap coincidence general at `d = 1` and the
  strict separation general at `2 ≤ d`.
* **The WOTS+-`F` undetectability and preimage roles.**  `targetCount` gives both
  `wotsInstanceCount p * p.len`, at *every* parameter set — asserted below as an `example` over an
  arbitrary `p`.  Their arities coincide too, both being the single-node chain hash, so only the
  games' types, `SM_DT_UD_SourceFinalValidity` against `SM_DT_PRE_SourceFinalValidity`, separate
  them.

## What the checks cannot catch

* **Anything about a probability.**  No probability is computable here.
* **Whether this bundle is the one anyone executes.**  It is not:
  `HashSigTest.SLHDSA.Sha2KAT` runs `Concrete.shaPrimitives`, a different term, which the library
  module's docstring records and nothing relates to this one.

## References

- NIST SP 800-230 (initial public draft) for the reduced `SLH-DSA-SHA2-128-24` profile
- NIST FIPS 205, §11 for the parameter sets
-/

public section

namespace SLHDSA.LimitedProfileTest

open Security Security.CanonicalGames KeyedHash OracleSpec TweakableHash

/-- Throw on a failed check, naming it. -/
def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"Limited profile check failed: {label}")

/-! ## The profile, under this file's own names

`p` is the library module's `limitedVp.params`, which is `SLHDSA.slhdsaSha2_128_24`; the
abbreviation is local convenience and `Pins` restates the identity. -/

/-- The SP 800-230 reduced parameter set. -/
abbrev p : Params := Security.limitedVp.params

/-! ## The checks -/

/-- **The profile's parameters and the numbers they derive.**  The seven fields, the Winternitz
width and chain count they determine, the digest and signature widths, and `w - 2`. -/
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
  -- `w - 2`, which is 14 at every FIPS 205 set
  ensure "w - 2" (p.w - 2 == 2)
  ensure "two ≤ w" (2 ≤ p.w)
  ensure "every FIPS 205 set has w - 2 = 14"
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
arity (`Pins` reads the arities off the two games); the WOTS+-`F` undetectability and preimage pair
coincides in cap.  The mirror pair, the two arity-two `H` games, is separated by cap. -/
def checkDarkCells : IO Unit := do
  -- the T_l pair: caps coincide at d = 1, arities do not
  ensure "forsTl and wotsTl caps coincide"
    (targetCount p .forsTl == targetCount p .wotsTl)
  ensure "k ≠ len" (p.k != p.len)
  -- the wotsFUd/wotsFPre pair: cap and arity both coincide
  ensure "wotsFUd and wotsFPre caps coincide"
    (targetCount p .wotsFUd == targetCount p .wotsFPre)
  -- the mirror: the two arity-two games are separated by their caps
  ensure "forsH and xmssH caps differ"
    (targetCount p .forsH != targetCount p .xmssH)

/-! ## The pins

One `example` per exported declaration of `HashSig.SLHDSA.Security.LimitedProfile`, then the ten
games' caps read at the concrete bundle and every game's arity read off its own input type, through
eight `*_eval_adrsToKey` equations and the two `forsF*Problem_eq_to*` equations.  A library-side
edit cannot reach this file. -/

section Pins

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
-- `noncomputable`, because without it this pin is itself a compiled constant and the build reports
-- that it depends on the library module's `noncomputable` `Fintype` instance.  That instance is
-- `noncomputable` for the reason its own comment gives, and this is the pin inheriting it.
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
Subject to the two dark cells the module docstring records, a cap transcribed onto the wrong game
shows up here. -/

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

/-! ### Every game's arity, read off its own attacked-member equation

Each of the ten `example`s below is stated at the game's own input type, so a statement made at
another arity is refused.  Seven use the `*_eval_adrsToKey` equation of their own game, of which
`HashSig.SLHDSA.Security.CanonicalGames` exports one per collection game and one for the standalone
FORS-`F` family; the standalone FORS-`F` DSPR and TCR games go through
`forsFDsprProblem_eq_toDSPR` and `forsFTcrProblem_eq_toTCR` first, those two games being `.toDSPR`
and `.toTCR` of `forsFOpenPreProblem`, whose input type is therefore theirs.  The tenth `example`
is `forsFOpenPreProblem` itself.

The two `T_ℓ` games are the pair the cap cannot separate at `d = 1`: the FORS root compression
takes a `Vector limitedPrimitives.Y 6` and the WOTS+ public-key compression a
`Vector limitedPrimitives.Y 68`.  The five single-node games take one `limitedPrimitives.Y` and
the two arity-two ones a pair of them.

**What separates a pin is its statement and not the lemma that proves it, across the whole
substitution matrix.**  Each of the eight directly-proved statements re-proved by each of the eight
equations is sixty-four elaborations, of which forty-eight are refused and sixteen accepted.  The
refusals are every cross-arity cell — the WOTS+-`F` undetectability statement re-made about the
arity-two FORS-`H` game, the FORS-`H` statement made at the single-node type — and they include the
standalone/collection boundary, in both directions between `forsFOpenPre` and any WOTS+-`F`
collection game.  Of the sixteen accepted, eight are the diagonal; the other eight are the ordered
pairs inside `{wotsFUd, wotsFTcr, wotsFPre}` and `{forsHTcr, xmssHTcr}`, which are four unordered
pairs of games sharing an arity and a `Thash`.  Three of those four are told apart by their caps,
which `checkDarkCells` asserts for the `H` pair; the fourth, `wotsFUd`/`wotsFPre`, is this module's
**second dark cell**, where the caps are equal
at every parameter set and only the two games' types separate them. -/

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

example (pkSeed : limitedPrimitives.PkSeed) (address : Adrs) (input : limitedPrimitives.Y) :
    (forsFOpenPreProblem limitedPrimitives).th.eval pkSeed
        (limitedPrimitives.adrsToKey address) input =
      limitedPrimitives.F pkSeed address input :=
  forsFOpenPreProblem_eval_adrsToKey limitedPrimitives pkSeed address input

example (pkSeed : limitedPrimitives.PkSeed) (address : Adrs) (input : limitedPrimitives.Y) :
    (forsFDsprProblem limitedPrimitives).th.eval pkSeed
        (limitedPrimitives.adrsToKey address) input =
      limitedPrimitives.F pkSeed address input := by
  rw [forsFDsprProblem_eq_toDSPR]
  exact forsFOpenPreProblem_eval_adrsToKey limitedPrimitives pkSeed address input

example (pkSeed : limitedPrimitives.PkSeed) (address : Adrs) (input : limitedPrimitives.Y) :
    (forsFTcrProblem limitedPrimitives).th.eval pkSeed
        (limitedPrimitives.adrsToKey address) input =
      limitedPrimitives.F pkSeed address input := by
  rw [forsFTcrProblem_eq_toTCR]
  exact forsFOpenPreProblem_eval_adrsToKey limitedPrimitives pkSeed address input

example (pkSeed : limitedPrimitives.PkSeed) (address : Adrs) (input : limitedPrimitives.Y) :
    (wotsFUdCProblem limitedPrimitives).th.eval pkSeed
        (limitedPrimitives.adrsToKey address) input =
      limitedPrimitives.F pkSeed address input :=
  wotsFUdCProblem_eval_adrsToKey limitedPrimitives pkSeed address input

example (pkSeed : limitedPrimitives.PkSeed) (address : Adrs) (input : limitedPrimitives.Y) :
    (wotsFTcrCProblem limitedPrimitives).th.eval pkSeed
        (limitedPrimitives.adrsToKey address) input =
      limitedPrimitives.F pkSeed address input :=
  wotsFTcrCProblem_eval_adrsToKey limitedPrimitives pkSeed address input

example (pkSeed : limitedPrimitives.PkSeed) (address : Adrs) (input : limitedPrimitives.Y) :
    (wotsFPreCProblem limitedPrimitives).th.eval pkSeed
        (limitedPrimitives.adrsToKey address) input =
      limitedPrimitives.F pkSeed address input :=
  wotsFPreCProblem_eval_adrsToKey limitedPrimitives pkSeed address input

example (pkSeed : limitedPrimitives.PkSeed) (address : Adrs)
    (input : limitedPrimitives.Y × limitedPrimitives.Y) :
    (forsHTcrCProblem limitedPrimitives).th.eval pkSeed
        (limitedPrimitives.adrsToKey address) input =
      limitedPrimitives.H pkSeed address input.1 input.2 :=
  forsHTcrCProblem_eval_adrsToKey limitedPrimitives pkSeed address input

example (pkSeed : limitedPrimitives.PkSeed) (address : Adrs)
    (input : limitedPrimitives.Y × limitedPrimitives.Y) :
    (xmssHTcrCProblem limitedPrimitives).th.eval pkSeed
        (limitedPrimitives.adrsToKey address) input =
      limitedPrimitives.H pkSeed address input.1 input.2 :=
  xmssHTcrCProblem_eval_adrsToKey limitedPrimitives pkSeed address input

/-! ### The two profile facts -/

example : limitedPrimitives.core.ByteLaws := limitedPrimitives_byteLaws
example : EncodedTargetLedgerConditions limitedVp limitedPrimitives := limitedEncodedConditions

end Pins

/-- Run the four check groups in order, then report. -/
def main : IO Unit := do
  checkProfile
  checkCaps
  checkCapRelations
  checkDarkCells
  IO.println "SLH-DSA limited profile tests: PASS"

end SLHDSA.LimitedProfileTest

/-- Entry point for `slhdsa_limited_profile_tests`. -/
def main : IO Unit := SLHDSA.LimitedProfileTest.main
