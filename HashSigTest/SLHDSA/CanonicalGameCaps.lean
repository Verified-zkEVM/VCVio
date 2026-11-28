/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.CanonicalGames
public import HashSig.SLHDSA.Security.TargetCounts

/-!
# SLH-DSA canonical game caps and open-preimage canaries

Executable checks and elaboration pins for the `Params`-level data of
`HashSig.SLHDSA.Security.CanonicalGames` — each game's declared target cap against
`SLHDSA.Security.targetCount`, the separation of the two `T_ℓ` compression games, and the
`KeyedHash.ITSRProblem` shape — together with facts about what the `SM_DT_*` games admit when the
adversary is computationally unbounded.

## The two profiles

`toyParams` is the two-layer profile of the scheme-dispatch, SUF-residual and scheme-game fixtures,
copied rather than imported because a `lean_exe` root must own its `main`. The SP 800-230 reduced
set `SLHDSA.LimitedParameterSet.SLHDSA_SHA2_128_24` is here as a bare `Params`: it is the profile at
which the FORS `T_k` and WOTS+ `T_len` compression games have the same cap, `2 ^ h` at every
one-layer parameter set. At `toyParams`, where `d = 2`, the caps differ, 16 against 20, and the pins
prove that separation for every `2 ≤ d`. At `d = 1` what separates the two games is their arity,
`p.k` against `p.len`. `Params.Valid` does not relate the two: `collideParams` is valid with `d = 1`
and `k = len = 6`, and at it `forsTlTcrCProblem` and `wotsTlTcrCProblem` are the same term by
`rfl`. Every FIPS 205 set and the SP 800-230 set has `k ≠ len`, asserted over the whole table.

## Open-preimage and preimage games at unbounded adversaries

`SM_DT_PRE_SourceFinalValidity` and `SM_DT_OpenPRE_SourceFinalValidity` accept on an equality of
images with no distinctness clause and hand the adversary an image the game has just computed, so
classical inversion (`Function.invFun`) wins: `freePreAdv_advantage` and
`winningOpenPre_advantage` give adversaries of advantage one. VCVio's
`SM_DT_OpenPRE_SourceFinalValidity.CountingInterface` is inhabited at an adversary that records no
target (`idleCounting`), and at an adversary of advantage one, over a finite input type with at
least two elements and uniform inputs, it exists exactly when `1 ≤ TCRDSPRBound`
(`nonempty_countingInterface_iff`).

## References

- NIST FIPS 205, §11 for the parameter sets, and SP 800-230 for the reduced `SLH-DSA-SHA2-128-24`
-/

public section

namespace SLHDSA.CanonicalGameCapsTest

open Security Security.CanonicalGames KeyedHash OracleSpec TweakableHash

/-- Throw on a failed check, naming it. -/
def ensure (label : String) (condition : Bool) : IO Unit :=
  unless condition do
    throw (IO.userError s!"Canonical game cap check failed: {label}")

/-! ## The two profiles -/

-- Exposed because `toyParams` has to reduce throughout this file: the bundle below checks `yToBytes
-- := id` against `Bytes 1 → Bytes toyParams.n`, the nine instances written at `toyPrimitives` need
-- it both to typecheck and to compile, and the toy instantiations of the open-preimage facts need
-- `toy.params` to reduce to `toyParams` for the generic declarations to apply.
/-- Two layers of height two, two FORS trees of height one. -/
@[expose] def toyParams : Params :=
  { n := 1, h := 4, d := 2, hp := 2, a := 1, k := 2, lgw := 4 }

/-- The toy parameters are valid. -/
theorem toyValid : toyParams.Valid := by decide

-- Exposed for a different reason from `toyParams`, and for nothing in the bundle: in the toy
-- instantiations the generic `vp` has to reduce to `toyParams` before the bundle's instances can be
-- found.
-- Without the body those searches do not report a missing instance but get stuck, one of them
-- running to the heartbeat limit.
/-- The validated form of `toyParams`. -/
@[expose] def toy : ValidatedParams := ⟨toyParams, toyValid⟩

/-- The SP 800-230 reduced parameter set, as a bare `Params`: the profile at which the two `T_ℓ`
caps coincide.  No primitive bundle is built at it here. -/
def p24 : Params := LimitedParameterSet.params .SLHDSA_SHA2_128_24

/-- A *valid* parameter set with `lgw = 1`, hence `w = 2` and an undetectability coefficient of
zero.  It is here because `Params.Valid` does not rule this out, whereas the EasyCrypt SPHINCS+
development fixes `w` to 4, 16 or 256 (`WOTS_TW_ES.ec`, `val_w`), so `Params.Valid` is more
permissive than the parameter space of that proof. -/
def widthTwoParams : Params :=
  { n := 1, h := 4, d := 2, hp := 2, a := 1, k := 2, lgw := 1 }

/-- A *valid* parameter set with `d = 1` and `k = len`, at which the two `T_ℓ` compression games
are literally the same object: same attacked hash, same collection, same cap, same arity.  It is
here because `Params.Valid` relates `k` to nothing, so the arity separation of the two games is a
property of the shipped parameter table and not of validity. -/
def collideParams : Params :=
  { n := 1, h := 4, d := 1, hp := 4, a := 2, k := 6, lgw := 2 }

/-- A deliberately invalid parameter set with `lgw = 0`, hence `w = 1`, at which the
`ℕ`-subtraction `w - 2` truncates to zero. -/
def degenerateParams : Params :=
  { n := 1, h := 4, d := 2, hp := 2, a := 1, k := 2, lgw := 0 }

/-! ## The toy primitive bundle

The bundle of `HashSigTest.SLHDSA.SchemeGames`, unchanged.  Nothing below evaluates a digest, a
signature or a hash: the bundle is here so that the canonical games can be named at concrete
types. -/

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

-- Exposed for code generation, and that is the whole of it: the nine instances below, the pins that
-- name the games at this bundle's types, and the `ITSRProblem` shape pin all have to
-- infer the same compilation type for this bundle as an importing module would, which needs its
-- body.  `@[reducible]`, which the scheme-game fixture's copy of this bundle carries, is *not*
-- needed here and is not written: no check below resolves an instance through the carrier by
-- unfolding it, the nine instances naming `Bytes 1` and `Adrs` directly.
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

/-! ## The checks -/

/-- **The Winternitz width.**  `w` and `w − 2` at both profiles, at a valid parameter set where
`w − 2` is legitimately zero, and at an invalid one where the `ℕ`-subtraction truncates. -/
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
  -- an invalid parameter set at which `w - 2` truncates
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
the SP 800-230 reduced profile a cap check alone cannot tell `forsTlTcrCProblem` from
`wotsTlTcrCProblem`.  What is left there is the arity, `p.k` against `p.len`, and `Params.Valid`
does not relate the two: `collideParams` is valid with `k = len`, and at it the two games are the
same term.  So the last group here asserts the separation where it is
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

/-! ## The pins

Elaboration pins for the canonical games' arities and caps, the general `T_ℓ` separation, the
`ITSRProblem` shape and the profile values. -/

section Pins

/-! ### The two `T_ℓ` games, pinned by arity

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

The runtime checks read `targetCount`; these tie each game's own `numTargets` field to it. -/

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

`KeyedHash.ITSRProblem` has exactly two fields, the keyed hash family and the index map, and
neither is a target cap.  An added third field fails this pin. -/

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

/-! ## Open-preimage and preimage canaries -/

section OpenPreimage

open OracleComp OracleSpec ENNReal

/-! ### An adversary that records no target -/

-- Exposed, and the only one of the ten definitions in this section that needs to be.  Inside a
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
    SM_DT_OpenPRE_SourceFinalValidity.advantage (idleOpenPre prob) = 0 := by
  unfold SM_DT_OpenPRE_SourceFinalValidity.advantage
    SM_DT_OpenPRE_SourceFinalValidity.experiment
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
    SM_DT_DSPR_SourceFinalValidity.advantage
      (SM_DT_OpenPRE_SourceFinalValidity.toDSPR (idleOpenPre prob)) = 0 := by
  unfold SM_DT_DSPR_SourceFinalValidity.advantage SM_DT_DSPR_SourceFinalValidity.Success
    SM_DT_DSPR_SourceFinalValidity.SPProbability
    SM_DT_DSPR_SourceFinalValidity.experiment SM_DT_DSPR_SourceFinalValidity.spExperiment
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
    SM_DT_OpenPRE_SourceFinalValidity.advantage (winningOpenPre prob t) = 1 := by
  have htake : List.take prob.numTargets [t] = [t] :=
    List.take_of_length_le (by simpa using Nat.succ_le_of_lt h)
  unfold SM_DT_OpenPRE_SourceFinalValidity.advantage
    SM_DT_OpenPRE_SourceFinalValidity.experiment
  simp [winningOpenPre, htake, openPreInverse_eval, h,
    SM_DT_OpenPRE_SourceFinalValidity.initializeTargets,
    SourceFinalValidity.State.initial, SourceFinalValidity.State.recordTarget,
    TweakableHash.TweakFresh, TweakableHash.TweakReserved]

section Preimage

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  [SampleableType prims.PkSeed] [SampleableType prims.Y]

/-- Classical inversion of the WOTS+-`F` preimage game's attacked map. -/
noncomputable def wotsFPreInverse (pk : prims.PkSeed) (t : prims.AdrsKey) : prims.Y → prims.Y :=
  Function.invFun fun m =>
    (wotsFPreCProblem prims).th.eval pk t ((wotsFPreCProblem prims).emb m)

theorem wotsFPreInverse_eval (pk : prims.PkSeed) (t : prims.AdrsKey) (a : prims.Y) :
    (wotsFPreCProblem prims).th.eval pk t ((wotsFPreCProblem prims).emb
        (wotsFPreInverse prims pk t ((wotsFPreCProblem prims).th.eval pk t
          ((wotsFPreCProblem prims).emb a)))) =
      (wotsFPreCProblem prims).th.eval pk t ((wotsFPreCProblem prims).emb a) :=
  Function.invFun_eq (f := fun m =>
    (wotsFPreCProblem prims).th.eval pk t ((wotsFPreCProblem prims).emb m)) ⟨a, rfl⟩

variable [DecidableEq prims.AdrsKey] [DecidableEq prims.Y]

/-- One challenge query, then classical inversion of the image it was answered with. -/
noncomputable def freePreAdv (t : prims.AdrsKey) :
    SM_DT_PRE_SourceFinalValidity.Adversary (wotsFPreCProblem prims) where
  State := prims.Y
  choose := liftM ((unifSpec +
    (SM_DT_PRE_SourceFinalValidity.challengeSpec prims.AdrsKey prims.Y +
      SourceFinalValidity.collectionSpec (wotsFPreCProblem prims).thColl)).query (.inr (.inl t)))
  invert := fun y pk => pure (0, wotsFPreInverse prims pk t y)

/-- **Preimage resistance is unconditionally false in this model**, at every validated parameter
set and every primitive bundle: the WOTS+-`F` preimage game has an adversary of advantage one. -/
theorem freePreAdv_advantage (t : prims.AdrsKey) :
    SM_DT_PRE_SourceFinalValidity.advantage (freePreAdv prims t) = 1 := by
  unfold SM_DT_PRE_SourceFinalValidity.advantage SM_DT_PRE_SourceFinalValidity.experiment
  simp [freePreAdv, wotsFPreInverse_eval, SM_DT_PRE_SourceFinalValidity.oracles,
    SM_DT_PRE_SourceFinalValidity.challengeOracle,
    SourceFinalValidity.State.recordTarget, SourceFinalValidity.State.initial,
    TweakableHash.TweakFresh, TweakableHash.TweakReserved,
    targetCount_pos vp.params vp.valid TargetRole.wotsFPre]

end Preimage

/-! ### The same facts at the toy bundle -/

example (t : Adrs) :
    SM_DT_PRE_SourceFinalValidity.advantage (freePreAdv (vp := toy) toyPrimitives t) = 1 :=
  freePreAdv_advantage (vp := toy) toyPrimitives t

example (t : Adrs) :
    SM_DT_OpenPRE_SourceFinalValidity.advantage
      (winningOpenPre (forsFOpenPreProblem toyPrimitives) t) = 1 :=
  winningOpenPre_advantage (forsFOpenPreProblem toyPrimitives) t (by
    rw [forsFOpenPreProblem_numTargets]
    exact targetCount_pos toyParams toyValid TargetRole.forsF)

section Counting

/-- The DSPR advantage is a truncated difference of probabilities, so it never exceeds one. -/
theorem dspr_advantage_le_one {ix PkS Tw Msg Nd : Type} [Fintype Msg] [DecidableEq Tw]
    [DecidableEq Msg] [DecidableEq Nd]
    {prob : SM_DT_DSPR_SourceFinalValidity.Problem ix PkS Tw Msg Nd}
    (a : SM_DT_DSPR_SourceFinalValidity.Adversary prob) :
    SM_DT_DSPR_SourceFinalValidity.advantage a ≤ 1 :=
  le_trans tsub_le_self (MeasureTheory.measure_le_one _ _)

/-- **The counting interface exists at a winning adversary exactly when `DSPR + 3 · TCR` reaches
one at its two reductions.**  Both directions: the forward one is VCVio's own inequality at an
advantage of one, and the reverse puts all the mass on the fibre-size-two stratum. -/
theorem nonempty_countingInterface_iff {ix PkS Tw Msg Nd : Type} [Fintype Msg] [Inhabited Msg]
    [SampleableType Msg] [DecidableEq Tw] [DecidableEq Msg] [DecidableEq Nd]
    {prob : SM_DT_OpenPRE_SourceFinalValidity.Problem ix PkS Tw Msg Nd}
    (adv : SM_DT_OpenPRE_SourceFinalValidity.Adversary prob)
    (hu : prob.HasUniformInputs) (hcard : 2 ≤ Fintype.card Msg)
    (hone : SM_DT_OpenPRE_SourceFinalValidity.advantage adv = 1) :
    Nonempty (SM_DT_OpenPRE_SourceFinalValidity.CountingInterface adv) ↔
      1 ≤ SM_DT_OpenPRE_SourceFinalValidity.TCRDSPRBound adv := by
  constructor
  · rintro ⟨hc⟩
    have h := SM_DT_OpenPRE_SourceFinalValidity.advantage_le_tcrDsprBound adv hc
    rwa [hone] at h
  · intro h
    have : NeZero (Fintype.card Msg - 1) := ⟨by omega⟩
    set D := SM_DT_DSPR_SourceFinalValidity.advantage
      (SM_DT_OpenPRE_SourceFinalValidity.toDSPR adv) with hD
    set T := SM_DT_TCR_SourceFinalValidity.advantage
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
               simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
               exact (tsub_add_cancel_of_le hc1).symm
             dspr_decomposition := by
               rw [SM_DT_OpenPRE_SourceFinalValidity.reciprocalMass]
               simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
                 Fin.val_zero, zero_add, Nat.cast_ofNat]
               rw [tsub_tsub, hsum, he]
               exact (ENNReal.sub_sub_cancel one_ne_top hD1).symm
             tcr_strata_le := by
               rw [SM_DT_OpenPRE_SourceFinalValidity.collisionMass]
               simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
                 Fin.val_zero, zero_add, Nat.cast_ofNat]
               rw [show ((2 - 1 : ℕ) : ℝ≥0∞) = 1 by norm_num, hhalf]
               exact hTle }⟩

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  [SampleableType prims.PkSeed] [SampleableType prims.Y] [DecidableEq prims.AdrsKey]
  [DecidableEq prims.Y] [Fintype prims.Y] [Inhabited prims.Y]

/-- **The counting interface at the FORS-`F` open-preimage game.**  That problem has uniform
inputs and `winningOpenPre` wins it, so the interface exists there exactly when one inequality
between two advantages holds — over a node type with at least two elements, which is the one
hypothesis this statement carries. -/
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

/-! ### The same equivalence at the toy bundle

The statement above is at an arbitrary bundle, and the one hypothesis it leaves undischarged is
about the node type.  At this file's bundle that hypothesis is `2 ≤ Fintype.card (Bytes 1)`, which
`decide` settles, so the equivalence is not a statement about an empty class of bundles.  Both
`decide`s need a deeper recursion limit than the default: 2048 is enough for neither and 4096 is
enough for both. -/

set_option maxRecDepth 4096 in
example : 2 ≤ Fintype.card toyPrimitives.Y := by decide

set_option maxRecDepth 4096 in
example (t : Adrs) :
    Nonempty (SM_DT_OpenPRE_SourceFinalValidity.CountingInterface
        (winningOpenPre (forsFOpenPreProblem toyPrimitives) t)) ↔
      1 ≤ SM_DT_OpenPRE_SourceFinalValidity.TCRDSPRBound
        (winningOpenPre (forsFOpenPreProblem toyPrimitives) t) :=
  nonempty_counting_winningOpenPre_iff (vp := toy) toyPrimitives t (by decide)

end OpenPreimage

/-- Run the three check groups in order, then report. -/
def main : IO Unit := do
  checkCoefficients
  checkCaps
  checkTlDiscrimination
  IO.println "SLH-DSA canonical game cap tests: PASS"

end SLHDSA.CanonicalGameCapsTest

/-- Entry point for `slhdsa_canonical_game_cap_tests`. -/
def main : IO Unit := SLHDSA.CanonicalGameCapsTest.main
