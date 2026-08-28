/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.TweakableHash
public import VCVio.OracleComp.SimSemantics.Append

/-!
# The collection oracle shared by the multi-target games

SLH-DSA does not attack a lone tweakable hash. `F`, `H` and `T_ℓ` share one public seed and one
address space, and a reduction that attacks one of them must still be able to *evaluate* the others
in order to simulate the parts of the structure it is not attacking. Once the public seed is
withheld during target selection — which is the whole point of a single-function multi-target notion
— the reduction cannot do that on its own. It needs an oracle.

Both analyses state their tweakable-hash assumptions in this collection form rather than
stand-alone: HK22 Def. 7 writes `SM-TCR(Th_m ∈ Th_λ)`, and BDHMS24 gives the `-C` variants, with the
collection appearing as outlined code inside the game (Fig. 5) and the oracle itself in Fig. 7.
Every tweakable-hash term of HK22 Thm. 3 carries `∈ Th`.

## Collection as a parameter, not a parallel game family

Following BDHMS24 Fig. 5, the collection is a parameter of each problem rather than a second `-C`
game beside each stand-alone one. The stand-alone notion is the instance at `ι := Empty`, where
`collectionSpec` is indexed by an uninhabited type and therefore cannot be queried at all. That
gives one definition per notion instead of two; `TweakableHashCollection.empty` and the
`standalone` constructors of the individual games package the instantiation.

## Distinct tweaks across the two oracles

BDHMS24's `VQS_t` requires the target tweaks to be distinct from each other *and* from every tweak
submitted to the collection oracle. Disjointness is enforced here from both sides: the collection
oracle rejects a tweak that already occurs in the challenge history, and each game's challenge
oracle rejects a tweak that already occurs in the collection tweak list.

`VQS_t` does **not** require collection tweaks to be distinct *among themselves*, and neither does
this oracle — repeated collection queries at one tweak are answered, and each appends. Over-
restricting here would rule out reductions that legitimately evaluate one address twice, so it is
pinned by `collectionOracle_run_of_repeated_tweak` below.

HK22 `DIST` and BDHMS `VQS_t` both express distinctness as a predicate checked at the end of the
game, where this oracle rejects the offending query as it arrives. The two admit the same winning
adversaries: an adversary whose transcript violates distinctness loses under the end-of-game check,
and under rejection it instead receives `⊥` for the offending query and is free to continue, having
gained nothing. Rejecting makes the restriction unviolatable rather than a side condition a
reduction can forget to discharge.

## References

- Hülsing and Kudinov, *Recovering the Tight Security Proof of SPHINCS+*,
  [ePrint 2022/346](https://eprint.iacr.org/2022/346), Def. 7 and Thm. 3.
- Barbosa, Dupressoir, Hülsing, Meijers and Strub, *A Tight Security Proof for SPHINCS+, Formally
  Verified*, [ePrint 2024/910](https://eprint.iacr.org/2024/910), Fig. 5, Fig. 7 and the `VQS_t`
  description.
-/

@[expose] public section

namespace MultiTarget

open OracleComp OracleSpec

variable {ι PkSeed Tweak Y : Type}

/-! ## The oracle -/

/-- The collection oracle's signature: a query names a member `i`, a tweak, and a message of *that
member's* message type, and the response is `Option Y`, with `none` the rejection of a tweak
reserved by the challenge oracle. -/
abbrev collectionSpec (coll : TweakableHashCollection ι PkSeed Tweak Y) :
    OracleSpec ((i : ι) × Tweak × coll.Msg i) :=
  _ →ₒ Option Y

/-- The collection oracle at a public seed, over the two-part game state
`(challenge history, collection tweaks)`.

A query is rejected with `none` exactly when its tweak already occurs in the challenge history; the
state is then untouched. Otherwise the answer is the queried member evaluated at the game's seed,
and the tweak is appended to the collection tweak list. Repeated collection tweaks are accepted.

The challenge history's element type is `Tweak × X`, which covers both the `Tweak × M` of SM-TCR and
the `Tweak × M'` of SM-PRE; only the tweak component is read here. -/
def collectionOracle [DecidableEq Tweak] {X : Type}
    (coll : TweakableHashCollection ι PkSeed Tweak Y) (pk : PkSeed) :
    QueryImpl (collectionSpec coll) (StateT (List (Tweak × X) × List Tweak) ProbComp) :=
  fun q => do
    let (chal, colls) ← get
    if chal.any fun e => e.1 = q.2.1 then
      return none
    else
      set (chal, colls ++ [q.2.1])
      return some (coll.eval q.1 pk q.2.1 q.2.2)

/-- At the empty collection the oracle's query type is uninhabited, so a game instantiated there
cannot issue a collection query at all. This is what makes "collection as a parameter" recover the
stand-alone notion rather than merely approximate it, so it is pinned rather than asserted. -/
theorem isEmpty_domain_collectionSpec_empty :
    IsEmpty (collectionSpec (TweakableHashCollection.empty PkSeed Tweak Y)).Domain :=
  ⟨fun q => q.1.elim⟩

/-! ## Pinning the collection oracle's conventions

A kernel-debt gate cannot see a game that disagrees with the paper, so each branch of
`collectionOracle` is fixed by an equation lemma, and the accepting behaviour on a repeated
collection tweak — the easiest convention to over-restrict — gets a lemma of its own. -/

variable [DecidableEq Tweak] {X : Type} {coll : TweakableHashCollection ι PkSeed Tweak Y}
  {pk : PkSeed} {chal : List (Tweak × X)} {colls : List Tweak}

/-- A collection query whose tweak is absent from the challenge history is answered with that
member's hash, and its tweak is appended to the end of the collection tweak list. -/
theorem collectionOracle_run_of_fresh (q : ((i : ι) × Tweak × coll.Msg i))
    (hnew : ∀ e ∈ chal, e.1 ≠ q.2.1) :
    (collectionOracle (X := X) coll pk q).run (chal, colls) =
      pure (some (coll.eval q.1 pk q.2.1 q.2.2), (chal, colls ++ [q.2.1])) := by
  have hany : (chal.any fun e => decide (e.1 = q.2.1)) = false := by simpa using hnew
  simp [collectionOracle, hany]

/-- A collection query at a tweak the challenge oracle has already issued is rejected, and the state
is unchanged. This is one half of the disjointness of the two tweak sets; the other half is each
game's challenge oracle rejecting a tweak already in the collection list. -/
theorem collectionOracle_run_of_challenge_clash (q : ((i : ι) × Tweak × coll.Msg i)) (x : X)
    (hmem : (q.2.1, x) ∈ chal) :
    (collectionOracle (X := X) coll pk q).run (chal, colls) = pure (none, (chal, colls)) := by
  have hany : (chal.any fun e => decide (e.1 = q.2.1)) = true :=
    List.any_eq_true.mpr ⟨(q.2.1, x), hmem, by simp⟩
  simp [collectionOracle, hany]

/-- Repeating a collection tweak is **accepted**: querying the same tweak twice in a row is answered
both times, and both occurrences are appended. `VQS_t` requires the collection tweaks to be disjoint
from the target tweaks, not distinct among themselves, and a reduction may legitimately evaluate one
address more than once.

Stated over two consecutive queries rather than one, because the single-query statement is a
corollary of `collectionOracle_run_of_fresh` and so would still hold if the oracle grew a
self-distinctness check. This form fails outright if it does, and it fixes the append order at the
same time. -/
theorem collectionOracle_run_of_repeated_tweak (q : ((i : ι) × Tweak × coll.Msg i))
    (hnew : ∀ e ∈ chal, e.1 ≠ q.2.1) :
    ((collectionOracle (X := X) coll pk q).run (chal, colls) >>= fun r =>
        (collectionOracle (X := X) coll pk q).run r.2) =
      pure (some (coll.eval q.1 pk q.2.1 q.2.2), (chal, colls ++ [q.2.1, q.2.1])) := by
  have hany : (chal.any fun e => decide (e.1 = q.2.1)) = false := by simpa using hnew
  simp [collectionOracle, hany]

end MultiTarget
