/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import HashSig.SLHDSA.Params

/-!
# Exact target counts for the current `d = 1` SLH-DSA construction

The concrete reductions for SPHINCS+/SLH-DSA do not assume an unquantified “multi-target”
property.  Each reduction commits to every relevant target in the stateless key structure before
the public seed is revealed.  This file records those target caps for the repository's current
single-XMSS-tree (`d = 1`) construction.

Write `L = 2^h'` for the number of XMSS leaves and `t = 2^a` for the number of leaves in one
FORS tree.  There is one FORS instance per XMSS leaf.  Consequently the source proof uses

* `L * k * t` arity-one FORS-leaf targets;
* `L * k * (t - 1)` arity-two FORS-tree targets;
* `L` arity-`k` FORS-root-compression targets;
* `L * len` arity-one WOTS-chain targets for UD-C and PRE-C;
* `L * len * w` arity-one WOTS-chain targets for TCR-C;
* `L` arity-`len` WOTS-public-key-compression targets; and
* `L - 1` arity-two XMSS-tree targets.

These are construction counts, not adversary query bounds.  The message-compression/ITSR target
cap is instead determined by the signing-oracle query bound and belongs to that game.

## References

* Barbosa, Dupressoir, Hülsing, Meijers, and Strub, “A Tight Security Proof for SPHINCS+,
  Formally Verified”, Figure 12 and the reductions in `FORS_ES.ec` and
  `FL_SL_XMSS_MT_ES.ec`.
* Hülsing and Kudinov, “Recovering the Tight Security Proof of SPHINCS+”.
-/

@[expose] public section

namespace SLHDSA

/-- Exact multi-target caps used by the concrete reductions for the current `d = 1` scheme. -/
structure D1TargetProfile where
  /-- Arity-one `F` targets covering all FORS secret leaves. -/
  forsLeaf : ℕ
  /-- Arity-two `H` targets covering all non-leaf FORS nodes. -/
  forsTree : ℕ
  /-- Arity-`k` `Tℓ` targets covering every FORS-root compression. -/
  forsRoots : ℕ
  /-- Arity-one `F` targets for the WOTS UD-C game. -/
  wotsUd : ℕ
  /-- Arity-one `F` targets for the WOTS TCR-C game, including every chain position. -/
  wotsTcr : ℕ
  /-- Arity-one `F` targets for the WOTS PRE-C game. -/
  wotsPre : ℕ
  /-- Arity-`len` `Tℓ` targets covering every WOTS public-key compression. -/
  wotsPk : ℕ
  /-- Arity-two `H` targets covering every non-leaf node of the single XMSS tree. -/
  xmssTree : ℕ
deriving Repr, DecidableEq

namespace Params

/-- The structural parameter condition under which the target ledger and the repository's
single-tree signing algorithm describe a `d = 1` SLH-DSA construction.  Consumers of the ledger
must carry this hypothesis; the formulas below are total as Lean functions but are only claimed as
security-reduction counts under `IsD1`. -/
def IsD1 (p : Params) : Prop := p.d = 1 ∧ p.h = p.hp

instance (p : Params) : Decidable p.IsD1 := by
  unfold IsD1
  infer_instance

/-- Arithmetic side conditions needed before a generic parameter record may be used in a
`d = 1` concrete security theorem.  The word-size clauses are the first-order obligations behind
reachable-address separation for the 32-bit ADRS fields; the final separation theorem must still
reason about the actual reachable address families, because the concrete address encoding is not
globally injective. -/
def D1SecurityProfile (p : Params) : Prop :=
  p.IsD1 ∧ 0 < p.n ∧ 0 < p.hp ∧ 0 < p.a ∧ 0 < p.k ∧ 0 < p.lgw ∧
    p.hp ≤ 32 ∧ p.k * p.t ≤ 2 ^ 32 ∧ p.len ≤ 2 ^ 32 ∧ p.w ≤ 2 ^ 32

instance (p : Params) : Decidable p.D1SecurityProfile := by
  unfold D1SecurityProfile
  infer_instance

/-- The repository's supported SHA2-128-24 parameter record satisfies every arithmetic side
condition of the single-tree security profile. -/
theorem slhdsaSha2_128_24_d1SecurityProfile :
    slhdsaSha2_128_24.D1SecurityProfile := by
  have hlog : Nat.log 4 192 = 3 := by decide
  norm_num [D1SecurityProfile, IsD1, slhdsaSha2_128_24, ParameterSet.params,
    Params.len, Params.len1, Params.len2, Params.w, Params.t, hlog]

/-- The SP 800-230 Initial Public Draft usage cap for the reduced parameter sets.  This is a
draft-profile bound, not an FIPS 205 approval claim. -/
def sp800230IpdSignatureLimit : ℕ := 2 ^ 24

/-- Number `L = 2^h'` of leaves in the current single XMSS tree. -/
def d1LeafCount (p : Params) : ℕ := 2 ^ p.hp

/-- Exact target profile for the repository's current `d = 1` SLH-DSA construction.  Reduction
theorems using it must assume `p.IsD1`. -/
def d1TargetProfile (p : Params) : D1TargetProfile where
  forsLeaf := p.d1LeafCount * p.k * p.t
  forsTree := p.d1LeafCount * p.k * (p.t - 1)
  forsRoots := p.d1LeafCount
  wotsUd := p.d1LeafCount * p.len
  wotsTcr := p.d1LeafCount * p.len * p.w
  wotsPre := p.d1LeafCount * p.len
  wotsPk := p.d1LeafCount
  xmssTree := p.d1LeafCount - 1

/-- Concrete target ledger for the only parameter set presently implemented by the repository.
The WOTS-TCR entry is the source proof's loose `L * len * w` cap. -/
theorem slhdsaSha2_128_24_d1TargetProfile :
    slhdsaSha2_128_24.d1TargetProfile =
      { forsLeaf := 422212465065984
        forsTree := 422212439900160
        forsRoots := 4194304
        wotsUd := 285212672
        wotsTcr := 1140850688
        wotsPre := 285212672
        wotsPk := 4194304
        xmssTree := 4194303 } := by
  have hlog : Nat.log 4 192 = 3 := by decide
  norm_num [slhdsaSha2_128_24, ParameterSet.params, d1TargetProfile, d1LeafCount,
    Params.len, Params.len1, Params.len2, Params.w, Params.t, hlog]

@[simp] theorem d1TargetProfile_forsLeaf (p : Params) :
    p.d1TargetProfile.forsLeaf = 2 ^ p.hp * p.k * 2 ^ p.a := rfl

@[simp] theorem d1TargetProfile_forsTree (p : Params) :
    p.d1TargetProfile.forsTree = 2 ^ p.hp * p.k * (2 ^ p.a - 1) := rfl

@[simp] theorem d1TargetProfile_forsRoots (p : Params) :
    p.d1TargetProfile.forsRoots = 2 ^ p.hp := rfl

@[simp] theorem d1TargetProfile_wotsUd (p : Params) :
    p.d1TargetProfile.wotsUd = 2 ^ p.hp * p.len := rfl

@[simp] theorem d1TargetProfile_wotsTcr (p : Params) :
    p.d1TargetProfile.wotsTcr = 2 ^ p.hp * p.len * p.w := rfl

@[simp] theorem d1TargetProfile_wotsPre (p : Params) :
    p.d1TargetProfile.wotsPre = 2 ^ p.hp * p.len := rfl

@[simp] theorem d1TargetProfile_wotsPk (p : Params) :
    p.d1TargetProfile.wotsPk = 2 ^ p.hp := rfl

@[simp] theorem d1TargetProfile_xmssTree (p : Params) :
    p.d1TargetProfile.xmssTree = 2 ^ p.hp - 1 := rfl

end Params

end SLHDSA
