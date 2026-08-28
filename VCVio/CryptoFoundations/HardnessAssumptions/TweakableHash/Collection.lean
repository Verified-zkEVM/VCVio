/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.TweakableHash

/-!
# The collection oracle for the single-function, distinct-tweak, multi-target games

A reduction attacking one member of a tweakable-hash family must still evaluate the others to
simulate the rest of the structure — SLH-DSA's `F`, `H` and `T_ℓ` share one public seed and one
address space — and cannot do so once the seed is withheld from it. This oracle is that access.

The collection is a parameter of each problem rather than a second game beside it. The stand-alone
notion is the instance at the empty collection (`TweakableHashCollection.empty`), where the query
type is uninhabited — pinned by `isEmpty_domain_collectionSpec_empty`; the games' `standalone`
constructors package that instantiation.

The target tweaks must be distinct from each other and from every tweak submitted to the collection
oracle. The original proofs enforce that in the winning condition; here the oracles enforce it, this
one rejecting a tweak already in the challenge history, and each game's challenge oracle rejecting a
tweak already in its own history or in the collection list. The two admit the same winning
adversaries: a violating transcript loses on the winning condition, and a rejected query yields `⊥`
and no information. Enforcing it in the oracles makes the restriction unviolatable rather than a
side condition a reduction can forget to discharge.

## References

- Hülsing and Kudinov, *Recovering the Tight Security Proof of SPHINCS+*,
  [ePrint 2022/346](https://eprint.iacr.org/2022/346), Def. 7 and Thm. 3.
- Barbosa, Dupressoir, Hülsing, Meijers and Strub, *A Tight Security Proof for SPHINCS+, Formally
  Verified*, [ePrint 2024/910](https://eprint.iacr.org/2024/910), Fig. 5 and Fig. 7.
-/

@[expose] public section

namespace TweakableHash

open OracleComp OracleSpec

variable {ι PkSeed Tweak Y : Type}

/-! ## The oracle -/

/-- The collection oracle's signature: a query names a member `i`, a tweak, and a message of *that
member's* type, and the response is `Option Y`, with `none` the rejection of a tweak reserved by the
challenge oracle. -/
abbrev collectionSpec (thColl : TweakableHashCollection ι PkSeed Tweak Y) :
    OracleSpec ((i : ι) × Tweak × thColl.Msg i) :=
  _ →ₒ Option Y

/-- The collection oracle at a public seed, over the two-part game state
`(challenge history, collection tweaks)`.

A query is rejected with `none` exactly when its tweak already occurs in the challenge history; the
state is then untouched. Otherwise the answer is the queried member evaluated at the game's seed,
and the tweak is appended to the collection tweak list. Repeated collection tweaks are accepted.

The challenge history's element type is `Tweak × X`, which covers both the `Tweak × M` of SM-TCR and
the `Tweak × M'` of SM-PRE; only the tweak component is read here. -/
def collectionOracle [DecidableEq Tweak] {X : Type}
    (thColl : TweakableHashCollection ι PkSeed Tweak Y) (pk : PkSeed) :
    QueryImpl (collectionSpec thColl) (StateT (List (Tweak × X) × List Tweak) ProbComp) :=
  fun q => do
    let (qsChal, twsColl) ← get
    if qsChal.any fun e => e.1 = q.2.1 then
      return none
    else
      set (qsChal, twsColl ++ [q.2.1])
      return some (thColl.eval q.1 pk q.2.1 q.2.2)

/-- At the empty collection (`ι := Empty`) the oracle's query type is uninhabited, so a game
instantiated there cannot issue a collection query at all. This is what makes the stand-alone notion
recovered rather than merely approximated, so it is pinned rather than asserted. -/
theorem isEmpty_domain_collectionSpec_empty :
    IsEmpty (collectionSpec (TweakableHashCollection.empty PkSeed Tweak Y)).Domain :=
  ⟨fun q => q.1.elim⟩

/-! ## Pinning the conventions

A kernel-debt gate cannot see a game that disagrees with the paper, so each branch of
`collectionOracle` is fixed by an equation lemma, and the accepting behaviour on a repeated
collection tweak gets one of its own. -/

variable [DecidableEq Tweak] {X : Type} {thColl : TweakableHashCollection ι PkSeed Tweak Y}
  {pk : PkSeed} {qsChal : List (Tweak × X)} {twsColl : List Tweak}

/-- A collection query whose tweak is absent from the challenge history is answered with that
member's hash, and its tweak is appended to the end of the collection tweak list. -/
theorem collectionOracle_run_of_fresh (q : ((i : ι) × Tweak × thColl.Msg i))
    (hnew : ∀ e ∈ qsChal, e.1 ≠ q.2.1) :
    (collectionOracle (X := X) thColl pk q).run (qsChal, twsColl) =
      pure (some (thColl.eval q.1 pk q.2.1 q.2.2), (qsChal, twsColl ++ [q.2.1])) := by
  have hany : (qsChal.any fun e => decide (e.1 = q.2.1)) = false := by simpa using hnew
  simp [collectionOracle, hany]

/-- A collection query at a tweak the challenge oracle has already issued is rejected, and the state
is unchanged. This is one half of the disjointness of the two tweak sets; the other half is each
game's challenge oracle rejecting a tweak already in the collection list. -/
theorem collectionOracle_run_of_challenge_clash (q : ((i : ι) × Tweak × thColl.Msg i)) (x : X)
    (hmem : (q.2.1, x) ∈ qsChal) :
    (collectionOracle (X := X) thColl pk q).run (qsChal, twsColl) =
      pure (none, (qsChal, twsColl)) := by
  have hany : (qsChal.any fun e => decide (e.1 = q.2.1)) = true :=
    List.any_eq_true.mpr ⟨(q.2.1, x), hmem, by simp⟩
  simp [collectionOracle, hany]

/-- Repeating a collection tweak is **accepted**: querying the same tweak twice in a row is answered
both times, and both occurrences are appended. Only disjointness from the target tweaks is required,
not distinctness among the collection tweaks themselves, and a reduction may legitimately evaluate
one address more than once.

Stated over two consecutive queries rather than one, because the single-query statement is a
corollary of `collectionOracle_run_of_fresh` and so would still hold if the oracle grew a
self-distinctness check. This form fails outright if it does, and it fixes the append order at the
same time. -/
theorem collectionOracle_run_of_repeated_tweak (q : ((i : ι) × Tweak × thColl.Msg i))
    (hnew : ∀ e ∈ qsChal, e.1 ≠ q.2.1) :
    ((collectionOracle (X := X) thColl pk q).run (qsChal, twsColl) >>= fun r =>
        (collectionOracle (X := X) thColl pk q).run r.2) =
      pure (some (thColl.eval q.1 pk q.2.1 q.2.2), (qsChal, twsColl ++ [q.2.1, q.2.1])) := by
  have hany : (qsChal.any fun e => decide (e.1 = q.2.1)) = false := by simpa using hnew
  simp [collectionOracle, hany]

end TweakableHash
