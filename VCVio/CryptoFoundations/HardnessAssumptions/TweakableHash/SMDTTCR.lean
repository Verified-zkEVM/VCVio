/-
Copyright (c) 2026 Nicolas Consigny, Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.Collection
public import VCVio.OracleComp.SimSemantics.Append

/-!
# Single-function, distinct-tweak, multi-target target-collision resistance (SM-DT-TCR)

The adversary first selects up to `numTargets` targets through an oracle evaluating the tweakable
hash at a public seed it does not know, then learns the seed and must collide with one of the images
it received. It may evaluate the other members of the collection throughout, through
`collectionOracle`.

Shortened to `SM-TCR` in the prose below; the declaration names keep the full label.

The seed is sampled by `SM_DT_TCR_Experiment` and passed only to `SM_DT_TCR_Adversary.forge`; it
never reaches `SM_DT_TCR_Adversary.choose`. The two phases are separate fields at different types,
`OracleComp (SM_DT_TCR_challengeSpec …)` against `ProbComp`, so "the oracle is removed once the seed
is revealed" is a typing fact and not a runtime convention: `forge` has no oracle to query.

`numTargets` bounds the accepted challenge queries and is the only query bound the game carries. See
`TweakableHash.collectionOracle` for why the tweak restrictions are enforced in the oracles rather
than in the winning condition.

## References

- Hülsing and Kudinov, *Recovering the Tight Security Proof of SPHINCS+*,
  [ePrint 2022/346](https://eprint.iacr.org/2022/346), Def. 2 and Def. 7.
- Barbosa, Dupressoir, Hülsing, Meijers and Strub, *A Tight Security Proof for SPHINCS+, Formally
  Verified*, [ePrint 2024/910](https://eprint.iacr.org/2024/910), Fig. 5 and Fig. 6.
- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055), §3.1 Def. 3.
-/

@[expose] public section

namespace TweakableHash

open OracleComp OracleSpec ENNReal

variable {ι PkSeed Tweak M Y : Type}

/-! ## The game -/

/-- The challenge oracle's signature: a query is a `(tweak, message)` pair, and the response is
`Option Y`, with `none` marking a rejected query. -/
abbrev SM_DT_TCR_challengeSpec (Tweak M Y : Type) : OracleSpec (Tweak × M) :=
  (Tweak × M) →ₒ Option Y

/-- An SM-TCR problem: the tweakable hash under attack, the collection its other members form, and
the bound on the number of targets the adversary may select. -/
structure SM_DT_TCR_Problem (ι PkSeed Tweak M Y : Type) where
  /-- The tweakable hash whose target-collision resistance is in question. -/
  th : TweakableHash PkSeed Tweak M Y
  /-- The rest of the collection, evaluable by the adversary at the game's seed. -/
  coll : TweakableHashCollection ι PkSeed Tweak Y
  /-- The cap on accepted challenge-oracle queries. -/
  numTargets : ℕ

/-- The stand-alone SM-TCR problem, at the empty collection: the collection oracle's query type is
uninhabited, so the adversary has only the challenge oracle. -/
def SM_DT_TCR_Problem.standalone (th : TweakableHash PkSeed Tweak M Y) (numTargets : ℕ) :
    SM_DT_TCR_Problem Empty PkSeed Tweak M Y where
  th := th
  coll := .empty PkSeed Tweak Y
  numTargets := numTargets

/-- The state threaded through both oracles of the SM-TCR game: the challenge history of accepted
`(tweak, message)` targets, and the list of tweaks spent on the collection oracle. -/
abbrev SM_DT_TCR_State (Tweak M : Type) : Type := List (Tweak × M) × List Tweak

/-- An SM-TCR adversary. `choose` selects targets through the challenge oracle, and may evaluate the
rest of the collection, without access to the public seed; `forge` receives the seed and the private
state, and has no oracle. -/
structure SM_DT_TCR_Adversary (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) where
  /-- Private state carried from `choose` to `forge`. -/
  State : Type
  /-- Select targets through the challenge oracle, with collection access. The public seed is not an
  input. -/
  choose : OracleComp (SM_DT_TCR_challengeSpec Tweak M Y + collectionSpec prob.coll) State
  /-- Given the revealed public seed, name a target index and a colliding message. -/
  forge : State → PkSeed → ProbComp (ℕ × M)

/-- The challenge oracle at a public seed, answering with the hash of the queried `(tweak, message)`
pair and recording that pair in the challenge history. A query is rejected with `none` when the
target cap is reached, when its tweak already occurs in the challenge history, or when its tweak has
been spent on the collection oracle; a rejected query leaves the state untouched.

Accepted queries are appended, so the history is in issue order and its `j`-th entry is the `j`-th
target. -/
def SM_DT_TCR_challengeOracle [DecidableEq Tweak]
    (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) (pk : PkSeed) :
    QueryImpl (SM_DT_TCR_challengeSpec Tweak M Y) (StateT (SM_DT_TCR_State Tweak M) ProbComp) :=
  fun tm => do
    let (chal, colls) ← get
    if prob.numTargets ≤ chal.length ∨ (chal.any fun e => e.1 = tm.1) ∨
        colls.any fun t => t = tm.1 then
      return none
    else
      set (chal ++ [tm], colls)
      return some (prob.th.eval pk tm.1 tm.2)

/-- Both oracles of the SM-TCR game over the shared state, at a public seed. -/
def SM_DT_TCR_oracles [DecidableEq Tweak] (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y)
    (pk : PkSeed) :
    QueryImpl (SM_DT_TCR_challengeSpec Tweak M Y + collectionSpec prob.coll)
      (StateT (SM_DT_TCR_State Tweak M) ProbComp) :=
  SM_DT_TCR_challengeOracle prob pk + collectionOracle (X := M) prob.coll pk

/-- The SM-TCR experiment. The public seed is sampled, the first phase runs against both oracles
without it, the second phase runs with it and without them, and the adversary wins by naming a
recorded target `j` and a message colliding with — and differing from — the `j`-th recorded message.
An index outside the challenge history loses. -/
noncomputable def SM_DT_TCR_Experiment [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (adv : SM_DT_TCR_Adversary prob) :
    ProbComp Bool := do
  let pk ← prob.th.seedGen
  let (st, chal, _) ← (simulateQ (SM_DT_TCR_oracles prob pk) adv.choose).run ([], [])
  let (j, m) ← adv.forge st pk
  match chal[j]? with
  | none => return false
  | some (t, mj) => return decide (m ≠ mj ∧ prob.th.eval pk t m = prob.th.eval pk t mj)

/-- The SM-TCR advantage of an adversary. -/
noncomputable def SM_DT_TCR_Advantage [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y} (adv : SM_DT_TCR_Adversary prob) : ℝ≥0∞ :=
  Pr[= true | SM_DT_TCR_Experiment adv]

/-! ## Pinning the challenge oracle's conventions

A kernel-debt gate cannot see a game that disagrees with the paper. The lemmas below fix the four
branches of `SM_DT_TCR_challengeOracle` and the order of the history, so that a change of convention
breaks a proof rather than passing silently. -/

variable [DecidableEq Tweak] {prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y} {pk : PkSeed}
  {t : Tweak} {m : M} {chal : List (Tweak × M)} {colls : List Tweak}

/-- A query with a tweak fresh to both histories, below the target cap, is answered with the hash
and appended to the end of the challenge history. -/
theorem SM_DT_TCR_challengeOracle_run_of_fresh (hlen : chal.length < prob.numTargets)
    (hnew : ∀ e ∈ chal, e.1 ≠ t) (hcoll : t ∉ colls) :
    (SM_DT_TCR_challengeOracle prob pk (t, m)).run (chal, colls) =
      pure (some (prob.th.eval pk t m), (chal ++ [(t, m)], colls)) := by
  have hany : (chal.any fun e => decide (e.1 = t)) = false := by simpa using hnew
  have hcany : (colls.any fun s => decide (s = t)) = false := by
    simpa using fun s hs (h : s = t) => hcoll (h ▸ hs)
  simp [SM_DT_TCR_challengeOracle, Nat.not_le.mpr hlen, hany, hcany]

/-- A query reusing a tweak already in the challenge history is rejected, and the state is
unchanged. -/
theorem SM_DT_TCR_challengeOracle_run_of_reused (m' : M) (hmem : (t, m') ∈ chal) :
    (SM_DT_TCR_challengeOracle prob pk (t, m)).run (chal, colls) =
      pure (none, (chal, colls)) := by
  have hany : (chal.any fun e => decide (e.1 = t)) = true :=
    List.any_eq_true.mpr ⟨(t, m'), hmem, by simp⟩
  simp [SM_DT_TCR_challengeOracle, hany]

/-- A query at the target cap is rejected, and the state is unchanged. -/
theorem SM_DT_TCR_challengeOracle_run_of_full (hlen : prob.numTargets ≤ chal.length) :
    (SM_DT_TCR_challengeOracle prob pk (t, m)).run (chal, colls) =
      pure (none, (chal, colls)) := by
  simp [SM_DT_TCR_challengeOracle, hlen]

/-- A query at a tweak already spent on the collection oracle is rejected, and the state is
unchanged. This is the half of the two tweak sets' disjointness that the challenge oracle enforces;
`collectionOracle_run_of_challenge_clash` is the other. -/
theorem SM_DT_TCR_challengeOracle_run_of_collection_clash (hmem : t ∈ colls) :
    (SM_DT_TCR_challengeOracle prob pk (t, m)).run (chal, colls) =
      pure (none, (chal, colls)) := by
  have hcany : (colls.any fun s => decide (s = t)) = true :=
    List.any_eq_true.mpr ⟨t, hmem, by simp⟩
  simp [SM_DT_TCR_challengeOracle, hcany]

/-! ## An end-to-end order check

The challenge history's `j`-th entry must be the `j`-th accepted challenge query, and the two
oracles must share one state. Both conventions are invisible at a single query and mis-attribute
every index at two, so they are pinned on a concrete probe interleaving the two oracles.

Everything in the probe is deterministic, so the whole run reduces and `rfl` decides the history
outright. `SM_DT_PRE_Probe` cannot do this — its challenge oracle samples — and states the
corresponding check over `support` instead. -/

namespace SM_DT_TCR_Probe

/-- A tweakable hash on `Bool` tweaks with a trivial seed, used only by the order check. -/
def hash : TweakableHash Unit Bool Bool Bool where
  seedGen := pure ()
  eval _ t m := t && m

/-- A one-member collection at the probe's types, so the probe can issue collection queries. -/
def coll : TweakableHashCollection Unit Unit Bool Bool where
  Msg _ := Bool
  eval _ _ t m := t || m

/-- The order-check problem: the probe hash and collection, with room for both target queries. -/
def problem : SM_DT_TCR_Problem Unit Unit Bool Bool Bool where
  th := hash
  coll := coll
  numTargets := 2

/-- Two accepted challenge queries, at tweaks `false` then `true`, with a collection query
interleaved between them at tweak `false` — already spent as a target, so it is rejected. That
rejection is itself part of what the check pins. -/
def queries : OracleComp (SM_DT_TCR_challengeSpec Bool Bool Bool + collectionSpec coll) Unit := do
  let _ ← (SM_DT_TCR_challengeSpec Bool Bool Bool + collectionSpec coll).query
    (.inl (false, true))
  let _ ← (SM_DT_TCR_challengeSpec Bool Bool Bool + collectionSpec coll).query
    (.inr ⟨(), false, true⟩)
  let _ ← (SM_DT_TCR_challengeSpec Bool Bool Bool + collectionSpec coll).query
    (.inl (true, false))
  return ()

/-- The challenge history after `SM_DT_TCR_Probe.queries` lists the two targets in issue order, so
its first entry is the first target and its second the second; the interleaved collection query at
an already-issued target tweak is rejected and leaves both lists untouched. Appending is what makes
the order hold; consing would reverse it. -/
theorem history_in_issue_order :
    (simulateQ (SM_DT_TCR_oracles problem ()) queries).run ([], []) =
      pure ((), ([(false, true), (true, false)], [])) := by
  rfl

/-- A collection query at a fresh tweak, then a challenge query at that same tweak. -/
def crossQueries :
    OracleComp (SM_DT_TCR_challengeSpec Bool Bool Bool + collectionSpec coll) Unit := do
  let _ ← (SM_DT_TCR_challengeSpec Bool Bool Bool + collectionSpec coll).query
    (.inr ⟨(), false, true⟩)
  let _ ← (SM_DT_TCR_challengeSpec Bool Bool Bool + collectionSpec coll).query
    (.inl (false, true))
  return ()

/-- The collection oracle's tweak list is the same list the challenge oracle reads: after a
collection query at tweak `false`, a target query at `false` is rejected, so the challenge history
stays empty while the collection list holds `false`.

`SM_DT_TCR_challengeOracle_run_of_collection_clash` cannot catch a mis-wiring here, because it
takes the collection list as a free variable and so never checks that `collectionOracle` is the
thing writing it. Routing the two oracles to separate state slots would satisfy every branch lemma
and break only this. -/
theorem challenge_reads_collection_tweaks :
    (simulateQ (SM_DT_TCR_oracles problem ()) crossQueries).run ([], []) =
      pure ((), ([], [false])) := by
  rfl

end SM_DT_TCR_Probe

end TweakableHash
