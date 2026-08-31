/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Scheme
public import Mathlib.Data.Finset.Union

/-!
# SLH-DSA Security Notions

Typed data and predicates used by the SLH-DSA security architecture.  This module fixes the
message/interface boundary, the FIPS digest-to-target map, EUF-CMA freshness, ITSR, and the
distinct-tweak hash predicates needed by the repaired SPHINCS+-TW proof.

The definitions are finite and classical.  They do not assert a reduction theorem and do not
provide a quantum-oracle interpretation.  A QROM result requires a separate quantum state space,
query semantics, and lifting proof; `ClassicalModel` intentionally provides none of those.

## References

- NIST FIPS 205, Algorithms 2 and 4 and Section 10
- Hülsing--Kudinov, "Recovering the Tight Security Proof of SPHINCS+"
- Barbosa et al., "A Tight Security Proof for SPHINCS+, Formally Verified"
-/

@[expose] public section

namespace SLHDSA.Security

/-! ## Interface and parameter contracts -/

/-- The external message mode that is part of an EUF-CMA request.  A pre-hash mode carries its
function identifier and declared output length; it is not conflated with the pure interface. -/
inductive InterfaceMode where
  | pure
  | prehash (functionId : List Byte) (outputLength : ℕ)
deriving Repr, DecidableEq

/-- A signing request, including all data covered by freshness and verification. -/
structure MessageInput where
  mode : InterfaceMode
  context : List Byte
  message : List Byte
deriving Repr, DecidableEq

/-- The parameter facts needed by the security architecture.  The generic arithmetic contract is
the canonical `Params.Valid`; security adds only the restriction to the Winternitz exponents used
by the approved theorem. -/
structure ParameterConditions (p : Params) : Prop where
  valid : p.Valid
  lgw_approved : p.lgw = 2 ∨ p.lgw = 4 ∨ p.lgw = 8

namespace ParameterConditions

theorem n_pos {p : Params} (conditions : ParameterConditions p) : 0 < p.n :=
  conditions.valid.n_pos

theorem hp_pos {p : Params} (conditions : ParameterConditions p) : 0 < p.hp :=
  conditions.valid.hp_pos

theorem d_pos {p : Params} (conditions : ParameterConditions p) : 0 < p.d :=
  conditions.valid.d_pos

theorem a_pos {p : Params} (conditions : ParameterConditions p) : 0 < p.a :=
  conditions.valid.a_pos

theorem k_pos {p : Params} (conditions : ParameterConditions p) : 0 < p.k :=
  conditions.valid.k_pos

theorem len_pos {p : Params} (_conditions : ParameterConditions p) : 0 < p.len := by
  simp [Params.len, Params.len2]

theorem lgw_pos {p : Params} (conditions : ParameterConditions p) : 0 < p.lgw :=
  conditions.valid.lgw_pos

theorem h_eq {p : Params} (conditions : ParameterConditions p) : p.h = p.hp * p.d := by
  simpa [Nat.mul_comm] using conditions.valid.h_eq_layers

theorem lgw_ne_one {p : Params} (conditions : ParameterConditions p) :
    p.lgw ≠ 1 := by
  rcases conditions.lgw_approved with h | h | h <;> omega

end ParameterConditions

/-- A target cardinality whose positivity is part of the data.  Security games use `Fin value`,
so this wrapper rules out `Fin 0` before a reduction or challenge family can be formed. -/
structure PositiveTargetCount where
  value : ℕ
  positive : 0 < value

namespace PositiveTargetCount

instance : Coe PositiveTargetCount ℕ := ⟨PositiveTargetCount.value⟩

@[simp]
theorem value_ne_zero (count : PositiveTargetCount) : count.value ≠ 0 :=
  Nat.ne_of_gt count.positive

/-- There is no positive target count whose underlying cardinality is zero. -/
theorem not_exists_value_eq_zero : ¬ ∃ count : PositiveTargetCount, count.value = 0 := by
  rintro ⟨count, h⟩
  exact count.value_ne_zero h

end PositiveTargetCount

/-! ## FIPS digest mapping and ITSR -/

/-- The indices selected by `H_msg`: a FORS instance in the bottom hypertree layer and one leaf
from each of the `k` FORS trees.  Modular reduction is the bit-mask operation from FIPS 205. -/
structure DigestIndex (p : Params) where
  tree : Fin (2 ^ (p.h - p.hp))
  leaf : Fin (2 ^ p.hp)
  fors : Fin p.k → Fin (2 ^ p.a)

/-- Interpret a natural as a bit string of width `bits`. -/
def finOfNatPowTwo (bits value : ℕ) : Fin (2 ^ bits) :=
  ⟨value % (2 ^ bits), Nat.mod_lt _ (Nat.two_pow_pos bits)⟩

/-- The FIPS 205 digest-to-`(idx_tree, idx_leaf, FORS indices)` map.  Tree and leaf parsing is
delegated to the canonical `splitDigest`; only the FORS digits are added here. -/
def digestIndex (p : Params) (digest : Bytes p.m) : DigestIndex p :=
  let parts := splitDigest p digest
  let forsDigits : Vector ℕ p.k :=
    ⟨(base2b parts.md.toList p.a p.k).toArray, by simp⟩
  {
    tree := parts.idxTree
    leaf := parts.idxLeaf
    fors := fun i => finOfNatPowTwo p.a (forsDigits.get i)
  }

@[simp] theorem digestIndex_tree (p : Params) (digest : Bytes p.m) :
    (digestIndex p digest).tree = (splitDigest p digest).idxTree := rfl

@[simp] theorem digestIndex_leaf (p : Params) (digest : Bytes p.m) :
    (digestIndex p digest).leaf = (splitDigest p digest).idxLeaf := rfl

/-- One leaf target selected by an `H_msg` digest. -/
structure ITSRTarget (p : Params) where
  tree : Fin (2 ^ (p.h - p.hp))
  leaf : Fin (2 ^ p.hp)
  forsTree : Fin p.k
  forsLeaf : Fin (2 ^ p.a)
deriving DecidableEq

/-- The exact `k`-element target set selected by a digest. -/
def digestTargetSet (p : Params) (digest : Bytes p.m) : Finset (ITSRTarget p) :=
  Finset.univ.image fun i =>
    let index := digestIndex p digest
    ⟨index.tree, index.leaf, i, index.fors i⟩

/-- The keyed input to `H_msg`; `randomizer` is the ITSR key and the complete signing request is
the message input.  `PK.seed` and `PK.root` are owned by the surrounding experiment transcript. -/
structure ITSRInput {p : Params} (prims : Primitives p) where
  randomizer : prims.Y
  request : MessageInput

/-- A completed `H_msg` evaluation and its digest-derived target set. -/
structure ITSRRecord {p : Params} (prims : Primitives p) where
  input : ITSRInput prims
  digest : Bytes p.m

/-- A recorded digest is the result of the attacked key's actual `H_msg` function. -/
def ITSRRecord.Coherent {p : Params} {prims : Primitives p} (pk : PublicKeyCore prims.core)
    (encode : MessageInput → List Byte) (record : ITSRRecord prims) : Prop :=
  record.digest = prims.Hmsg record.input.randomizer pk.pkSeed pk.pkRoot
    (encode record.input.request)

/-- Union of all target sets disclosed by earlier honest `H_msg` evaluations. -/
def itsrHistoryTargets {p : Params} {prims : Primitives p} :
    List (ITSRRecord prims) → Finset (ITSRTarget p) :=
  List.foldr (fun record targets => digestTargetSet p record.digest ∪ targets) ∅

/-- ITSR success: a fresh `(randomizer, request)` pair selects only FORS targets already
interleaved among prior honest digest outputs. -/
def ITSRBreak {p : Params} {prims : Primitives p} [DecidableEq prims.Y]
    (pk : PublicKeyCore prims.core) (encode : MessageInput → List Byte)
    (history : List (ITSRRecord prims)) (forgery : ITSRRecord prims) : Prop :=
  (∀ record ∈ history, record.Coherent pk encode) ∧ forgery.Coherent pk encode ∧
    (forgery.input.randomizer, forgery.input.request) ∉
      history.map (fun record => (record.input.randomizer, record.input.request)) ∧
    digestTargetSet p forgery.digest ⊆ itsrHistoryTargets history

/-! ## EUF-CMA and tweakable-hash predicates -/

/-- Message-level EUF-CMA freshness.  Mode, context, and pre-hash identifier are included because
they are fields of `MessageInput`. -/
def Fresh (signed : List MessageInput) (forged : MessageInput) : Prop :=
  forged ∉ signed

/-- Strong-unforgeability freshness: the exact candidate request/signature pair was not returned
by the signing oracle.  A previously signed request may therefore still be fresh when paired with
a distinct signature. -/
def StrongFresh {Signature : Type} (signed : List (MessageInput × Signature))
    (forged : MessageInput × Signature) : Prop :=
  forged ∉ signed

/-- The residual strong-unforgeability case: the request was signed before, but the exact
request/signature pair is new. -/
def SameMessageNewSignature {Signature : Type} (signed : List (MessageInput × Signature))
    (forged : MessageInput × Signature) : Prop :=
  forged.1 ∈ signed.map Prod.fst ∧ StrongFresh signed forged

/-- Exact-pair freshness partitions into a new request or a previously signed request carrying a
new signature. -/
theorem strongFresh_iff_fresh_or_sameMessageNewSignature {Signature : Type}
    (signed : List (MessageInput × Signature)) (forged : MessageInput × Signature) :
    StrongFresh signed forged ↔
      Fresh (signed.map Prod.fst) forged.1 ∨ SameMessageNewSignature signed forged := by
  classical
  by_cases hrequest : forged.1 ∈ signed.map Prod.fst
  · simp [Fresh, SameMessageNewSignature, StrongFresh, hrequest]
  · constructor
    · intro _
      exact Or.inl hrequest
    · intro h
      rcases h with h | h
      · intro hpair
        exact h (List.mem_map_of_mem hpair)
      · exact h.2

/-- The new-request and same-message/new-signature freshness branches are disjoint. -/
theorem not_fresh_and_sameMessageNewSignature {Signature : Type}
    (signed : List (MessageInput × Signature)) (forged : MessageInput × Signature) :
    ¬ (Fresh (signed.map Prod.fst) forged.1 ∧ SameMessageNewSignature signed forged) := by
  intro h
  exact h.1 h.2.1

/-- A tweak/input pair selected from an honest transcript.  The game output is always computed
with its `eval` argument; it is not a caller-supplied field. -/
structure TweakableTarget (Tweak Input : Type) where
  tweak : Tweak
  input : Input

/-- A nonempty target batch whose tweaks are pairwise distinct.  TCR, DSPR, PRE, and UD games
accept this structure rather than a raw list, so distinctness cannot be omitted at a call site. -/
structure DistinctTargetBatch (Tweak Input : Type) [DecidableEq Tweak] where
  targets : List (TweakableTarget Tweak Input)
  nonempty : targets ≠ []
  distinctTweaks : (targets.map TweakableTarget.tweak).Nodup

/-- Single-function multi-target target-collision success for a selected honest target. -/
def TCRBreak {Tweak Input Output : Type}
    [DecidableEq Tweak] [DecidableEq Input] [DecidableEq Output]
    (eval : Tweak → Input → Output)
    (batch : DistinctTargetBatch Tweak Input)
    (target : TweakableTarget Tweak Input) (replacement : Input) : Prop :=
  target ∈ batch.targets ∧ replacement ≠ target.input ∧
    eval target.tweak replacement = eval target.tweak target.input

/-- A target has a distinct second preimage under its fixed tweak. -/
def HasSecondPreimage {Tweak Input Output : Type}
    (eval : Tweak → Input → Output) (target : TweakableTarget Tweak Input) : Prop :=
  ∃ replacement, replacement ≠ target.input ∧
    eval target.tweak replacement = eval target.tweak target.input

/-- Correctness predicate for the decisional second-preimage experiment.  The quantitative
SM-DT-DSPR advantage compares this game with its `SPprob` baseline; it is not a collision
probability inserted directly into the master bound. -/
def DSPRGuessCorrect {Tweak Input Output : Type}
    [DecidableEq Tweak] [DecidableEq Input] [DecidableEq Output]
    (eval : Tweak → Input → Output) (batch : DistinctTargetBatch Tweak Input)
    (target : TweakableTarget Tweak Input)
    (guess : Bool) : Prop :=
  target ∈ batch.targets ∧ (guess = true ↔ HasSecondPreimage eval target)

/-- Preimage success against a selected honest target. -/
def PREBreak {Tweak Input Output : Type}
    [DecidableEq Tweak] [DecidableEq Input] [DecidableEq Output]
    (eval : Tweak → Input → Output) (batch : DistinctTargetBatch Tweak Input)
    (target : TweakableTarget Tweak Input)
    (candidate : Input) : Prop :=
  target ∈ batch.targets ∧
    eval target.tweak candidate = eval target.tweak target.input

/-- Correct classification in the uniform-distinguishing game used by the repaired WOTS-TW
step.  Its advantage is an absolute difference of the two experiment probabilities. -/
def UDGuessCorrect {Tweak Input : Type} [DecidableEq Tweak]
    (_batch : DistinctTargetBatch Tweak Input) (real guess : Bool) : Prop :=
  guess = real

/-- The collection-oracle separation condition used by repaired WOTS-TW composition. -/
def CollectionCompatible {Tweak Input : Type} [DecidableEq Tweak]
    (batch : DistinctTargetBatch Tweak Input)
    (externalQueries : List Tweak) : Prop :=
  ∀ target ∈ batch.targets, target.tweak ∉ externalQueries

/-! ## Classical/QROM boundary -/

/-- Marker for the VCVio `OracleComp` semantics used by the master architecture. -/
inductive ClassicalModel where
  | oracleComp
deriving Repr, DecidableEq

/-- Marker for a possible quantum random-oracle claim.  It deliberately has no constructors:
this architecture contains no quantum state space, superposition-query semantics, or lifting
theorem. -/
inductive QROMClaim (p : Params) (prims : Primitives p)

end SLHDSA.Security
