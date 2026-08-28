/-
Copyright (c) 2026 Nicolas Consigny, Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.MultiTarget.Collection
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.SimSemantics.Append

/-!
# Single-function multi-target preimage resistance for distinct tweaks (SM-PRE)

The two-phase shape is that of SM-TCR — the public seed is sampled by the experiment, withheld while
the adversary selects targets, then revealed with the challenge oracle removed — but the challenge
oracle differs: the adversary supplies only a *tweak*, and the oracle draws the message itself from
the subspace `M′`. Winning means producing *any* preimage of a recorded image; unlike SM-TCR there
is no requirement that it differ from the recorded message.

That the adversary chooses the tweaks is essential, not cosmetic. A reduction has to place its
challenges at the specific addresses where the scheme it is simulating will use them; a game in
which the challenger picks the tweaks cannot be used that way.

## The subspace `M′`

`M′` is carried as its own type `M'` together with `emb : M' → M`, so the papers' `x ←$ M′` is
`$ᵗ M'` and the requirement that the adversary's output lie in `M′` holds by typing rather than by a
runtime check. A subspace carved out of an existing `M` by a predicate is the case
`M' := Subtype p`, `emb := Subtype.val`; the common special case `|M′| = |M|` is `M' := M`,
`emb := id`.

## Distinct tweaks, and the two query counts

The challenge oracle answers `none` — the papers' `⊥` — once `numTargets` queries have been
answered, whenever the queried tweak already appears in the challenge history, and whenever it
appears in the collection oracle's tweak list. Every bound assumes all three restrictions. See
`MultiTarget.collectionOracle` for why rejecting is used in place of an end-of-game predicate.

`numTargets` is the papers' `p`, the number of classical queries to the challenge oracle, and it is
the only query bound this game carries. The `q` appearing in concrete bounds counts queries to the
hash function itself, a quantity of the random-oracle analysis in which `Th` is an oracle rather
than a function; it is not a parameter of the game and must not be conflated with `p`.

## References

- Hülsing and Kudinov, *Recovering the Tight Security Proof of SPHINCS+*,
  [ePrint 2022/346](https://eprint.iacr.org/2022/346), Def. 3 and Def. 7.
- Barbosa, Dupressoir, Hülsing, Meijers and Strub, *A Tight Security Proof for SPHINCS+, Formally
  Verified*, [ePrint 2024/910](https://eprint.iacr.org/2024/910), Fig. 7 for the collection oracle.
  Their preimage notion is SM-DT-OpenPRE (Fig. 10, challenge oracle in Fig. 11), which is the
  nearest analogue of this game rather than the same one.
- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055), §3.1 Def. 4.
-/

@[expose] public section

namespace MultiTarget

open OracleComp OracleSpec ENNReal

variable {ι PkSeed Tweak M M' Y : Type}

/-! ## The game -/

/-- The challenge oracle's signature: a query is a tweak alone — the oracle picks the message — and
the response is `Option Y`, with `none` the papers' `⊥` for a rejected query. -/
abbrev preChallengeSpec (Tweak Y : Type) : OracleSpec Tweak := Tweak →ₒ Option Y

/-- An SM-PRE problem: the tweakable hash under attack, the subspace `M′` of its message space that
the challenge oracle samples from, the collection its other members form, and the bound `p` on the
number of targets. -/
structure PreProblem (ι PkSeed Tweak M M' Y : Type) where
  /-- The tweakable hash whose preimage resistance is in question. -/
  th : TweakableHash PkSeed Tweak M Y
  /-- The inclusion `M′ ⊆ M` of the subspace the challenge oracle samples from. -/
  emb : M' → M
  /-- The rest of the collection, evaluable by the adversary at the game's seed. -/
  coll : TweakableHashCollection ι PkSeed Tweak Y
  /-- The papers' `p`: the cap on classical queries to the challenge oracle. -/
  numTargets : ℕ

/-- The stand-alone SM-PRE problem, at the empty collection: the collection oracle's query type is
uninhabited, so the adversary has only the challenge oracle. -/
def PreProblem.standalone (th : TweakableHash PkSeed Tweak M Y) (emb : M' → M) (numTargets : ℕ) :
    PreProblem Empty PkSeed Tweak M M' Y where
  th := th
  emb := emb
  coll := .empty PkSeed Tweak Y
  numTargets := numTargets

/-- The state threaded through both oracles of the SM-PRE game: the challenge history `Q` of
accepted `(tweak, sampled message)` targets, and the list of tweaks spent on the collection
oracle. -/
abbrev PreState (Tweak M' : Type) : Type := List (Tweak × M') × List Tweak

/-- An SM-PRE adversary. `choose` selects tweaks through the challenge oracle, and may evaluate the
rest of the collection, without access to the public seed; `invert` receives the seed and the
private state, and has no oracle. -/
structure PreAdversary (prob : PreProblem ι PkSeed Tweak M M' Y) where
  /-- Private state carried from `choose` to `invert`. -/
  State : Type
  /-- Select tweaks through the challenge oracle, with collection access. The public seed is not an
  input. -/
  choose : OracleComp (preChallengeSpec Tweak Y + collectionSpec prob.coll) State
  /-- Given the revealed public seed, name a target index and a preimage in `M′`. -/
  invert : State → PkSeed → ProbComp (ℕ × M')

/-- The challenge oracle at a public seed: it draws `x` uniformly from `M′`, answers `Th(P, T, x)`
and records `(T, x)` in the challenge history `Q`. A query is rejected with `none` when the target
cap is reached, when its tweak already occurs in the challenge history, or when its tweak has been
spent on the collection oracle; a rejected query leaves the state untouched and draws nothing.

Accepted queries are appended, so the history is in issue order and `Q[j]` is the `j`-th target. -/
noncomputable def preChallengeOracle [DecidableEq Tweak] [SampleableType M']
    (prob : PreProblem ι PkSeed Tweak M M' Y) (pk : PkSeed) :
    QueryImpl (preChallengeSpec Tweak Y) (StateT (PreState Tweak M') ProbComp) :=
  fun t => do
    let (chal, colls) ← get
    if prob.numTargets ≤ chal.length ∨ (chal.any fun e => e.1 = t) ∨
        colls.any fun s => s = t then
      return none
    else
      let x ← (($ᵗ M' : ProbComp M') : StateT (PreState Tweak M') ProbComp M')
      set (chal ++ [(t, x)], colls)
      return some (prob.th.eval pk t (prob.emb x))

/-- Both oracles of the SM-PRE game over the shared state, at a public seed. -/
noncomputable def preOracles [DecidableEq Tweak] [SampleableType M']
    (prob : PreProblem ι PkSeed Tweak M M' Y) (pk : PkSeed) :
    QueryImpl (preChallengeSpec Tweak Y + collectionSpec prob.coll)
      (StateT (PreState Tweak M') ProbComp) :=
  preChallengeOracle prob pk + collectionOracle (X := M') prob.coll pk

/-- The SM-PRE experiment. The public seed is sampled, the first phase runs against both oracles
without it, the second phase runs with it and without them, and the adversary wins by naming a
recorded target `j` and any message of `M′` whose image under the `j`-th recorded tweak agrees with
that of the `j`-th recorded message. An index outside the challenge history loses. -/
noncomputable def preExperiment [DecidableEq Tweak] [DecidableEq Y] [SampleableType M']
    {prob : PreProblem ι PkSeed Tweak M M' Y} (adv : PreAdversary prob) : ProbComp Bool := do
  let pk ← prob.th.seedGen
  let (st, chal, _) ← (simulateQ (preOracles prob pk) adv.choose).run ([], [])
  let (j, m) ← adv.invert st pk
  match chal[j]? with
  | none => return false
  | some (t, x) =>
      return decide (prob.th.eval pk t (prob.emb m) = prob.th.eval pk t (prob.emb x))

/-- The SM-PRE advantage of an adversary. -/
noncomputable def preAdvantage [DecidableEq Tweak] [DecidableEq Y] [SampleableType M']
    {prob : PreProblem ι PkSeed Tweak M M' Y} (adv : PreAdversary prob) : ℝ≥0∞ :=
  Pr[= true | preExperiment adv]

/-! ## Pinning the challenge oracle's conventions

A kernel-debt gate cannot see a game that disagrees with the paper. The lemmas below fix the four
branches of `preChallengeOracle` and the order of the history, so that a change of convention breaks
a proof rather than passing silently. -/

variable [DecidableEq Tweak] [SampleableType M'] {prob : PreProblem ι PkSeed Tweak M M' Y}
  {pk : PkSeed} {t : Tweak} {chal : List (Tweak × M')} {colls : List Tweak}

/-- A query with a tweak fresh to both histories, below the target cap, draws its message from `M′`,
answers with the hash of that message and appends it to the end of the challenge history. -/
theorem preChallengeOracle_run_of_fresh (hlen : chal.length < prob.numTargets)
    (hnew : ∀ e ∈ chal, e.1 ≠ t) (hcoll : t ∉ colls) :
    (preChallengeOracle prob pk t).run (chal, colls) =
      (fun x => (some (prob.th.eval pk t (prob.emb x)), (chal ++ [(t, x)], colls))) <$>
        ($ᵗ M') := by
  have hany : (chal.any fun e => decide (e.1 = t)) = false := by simpa using hnew
  have hcany : (colls.any fun s => decide (s = t)) = false := by
    simpa using fun s hs (h : s = t) => hcoll (h ▸ hs)
  simp [preChallengeOracle, Nat.not_le.mpr hlen, hany, hcany, Functor.map_map]

/-- A query reusing a tweak already in the challenge history is rejected, and the state is
unchanged. -/
theorem preChallengeOracle_run_of_reused (x : M') (hmem : (t, x) ∈ chal) :
    (preChallengeOracle prob pk t).run (chal, colls) = pure (none, (chal, colls)) := by
  have hany : (chal.any fun e => decide (e.1 = t)) = true :=
    List.any_eq_true.mpr ⟨(t, x), hmem, by simp⟩
  simp [preChallengeOracle, hany]

/-- A query at the target cap is rejected, and the state is unchanged. -/
theorem preChallengeOracle_run_of_full (hlen : prob.numTargets ≤ chal.length) :
    (preChallengeOracle prob pk t).run (chal, colls) = pure (none, (chal, colls)) := by
  simp [preChallengeOracle, hlen]

/-- A query at a tweak already spent on the collection oracle is rejected, and the state is
unchanged. This is the half of the two tweak sets' disjointness that the challenge oracle enforces;
`collectionOracle_run_of_challenge_clash` is the other. -/
theorem preChallengeOracle_run_of_collection_clash (hmem : t ∈ colls) :
    (preChallengeOracle prob pk t).run (chal, colls) = pure (none, (chal, colls)) := by
  have hcany : (colls.any fun s => decide (s = t)) = true :=
    List.any_eq_true.mpr ⟨t, hmem, by simp⟩
  simp [preChallengeOracle, hcany]

/-! ## An end-to-end order check

`Q[j]` must be the `j`-th accepted challenge query, and the two oracles must share one state. Both
conventions are invisible at a single query and mis-attribute every index at two, so they are pinned
on a concrete probe interleaving the two oracles. -/

namespace PreProbe

/-- A tweakable hash on `Bool` tweaks with a trivial seed, used only by the order check. -/
def hash : TweakableHash Unit Bool Bool Bool where
  seedGen := pure ()
  eval _ t m := t && m

/-- A one-member collection at the probe's types, so the probe can issue collection queries.

Reducible: `collectionSpec` is indexed by `(i : ι) × Tweak × coll.Msg i`, so the probe's oracles and
its query sequence only share a spec up to unfolding this and `problem`. At default transparency
that mismatch stops instance matching inside `simp`. -/
abbrev coll : TweakableHashCollection Unit Unit Bool Bool where
  Msg _ := Bool
  eval _ _ t m := t || m

/-- The order-check problem: the probe hash and collection, sampling from all of `Bool`, with room
for both target queries. Reducible for the reason given on `coll`. -/
abbrev problem : PreProblem Unit Unit Bool Bool Bool Bool where
  th := hash
  emb := id
  coll := coll
  numTargets := 2

/-- Two accepted challenge queries at distinct tweaks, with a collection query interleaved between
them at an already-issued target tweak, so it is rejected. -/
def queries : OracleComp (preChallengeSpec Bool Bool + collectionSpec coll) Unit := do
  let _ ← (preChallengeSpec Bool Bool + collectionSpec coll).query (.inl false)
  let _ ← (preChallengeSpec Bool Bool + collectionSpec coll).query (.inr ⟨(), false, true⟩)
  let _ ← (preChallengeSpec Bool Bool + collectionSpec coll).query (.inl true)
  return ()

/-- Whatever messages the oracle draws, the tweaks in the challenge history appear in issue order,
so `Q[0]` belongs to the first target and `Q[1]` to the second, and the interleaved collection query
at an already-issued target tweak is rejected, leaving the collection list empty. Appending is what
makes the order hold; consing would reverse it. -/
theorem history_in_issue_order :
    ∀ p ∈ support ((simulateQ (preOracles problem ()) queries).run ([], [])),
      p.2.1.map Prod.fst = [false, true] ∧ p.2.2 = [] := by
  simp [queries, preOracles, preChallengeOracle, collectionOracle]
  grind

end PreProbe

end MultiTarget
