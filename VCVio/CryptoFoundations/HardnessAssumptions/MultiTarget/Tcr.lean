/-
Copyright (c) 2026 Nicolas Consigny, Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.MultiTarget.Collection

/-!
# Single-function multi-target target-collision resistance for distinct tweaks (SM-TCR)

The adversary first selects up to `p` targets through an oracle evaluating `Th(P, ·, ·)` at a public
seed it does not know, then learns `P` and must collide with one of the images it received. It may
evaluate the other members of the collection throughout, through `collectionOracle`.

## The hidden first phase

`P` is sampled by `tcrExperiment` and passed only to `TcrAdversary.forge`. It never reaches
`TcrAdversary.choose`. This is what separates the notion from plain collision resistance: with `P`
available during target selection, an adversary could search offline for a colliding pair and
register one endpoint as its target, giving a birthday bound of `2 ^ (n / 2)` in place of `2 ^ n`
and losing the collision resilience that the tweakable-hash framework exists to provide. The bound
is instead *linear* in the query count — HK22 gives `(2q + 1) / |H| + 2q / |P|`, which is vacuous at
`|P| = 1`, and the parameter requirements of the schemes size `P` precisely to control that second
term.

The two phases are separate fields at different types, `OracleComp (tcrChallengeSpec …)` against
`ProbComp`, so "the oracle is removed once `P` is revealed" is a typing fact rather than a runtime
convention: `forge` has no oracle to query.

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
  [ePrint 2022/346](https://eprint.iacr.org/2022/346), Def. 2 and Def. 7.
- Barbosa, Dupressoir, Hülsing, Meijers and Strub, *A Tight Security Proof for SPHINCS+, Formally
  Verified*, [ePrint 2024/910](https://eprint.iacr.org/2024/910), Fig. 5 and Fig. 6.
- Drake, Khovratovich, Kudinov and Wagner, *Hash-Based Multi-Signatures for Post-Quantum Ethereum*,
  [ePrint 2025/055](https://eprint.iacr.org/2025/055), §3.1 Def. 3.
-/

@[expose] public section

namespace MultiTarget

open OracleComp OracleSpec ENNReal

variable {ι PkSeed Tweak M Y : Type}

/-! ## The game -/

/-- The challenge oracle's signature: a query is a `(tweak, message)` pair, and the response is
`Option Y`, with `none` the papers' `⊥` for a rejected query. -/
abbrev tcrChallengeSpec (Tweak M Y : Type) : OracleSpec (Tweak × M) := (Tweak × M) →ₒ Option Y

/-- An SM-TCR problem: the tweakable hash under attack, the collection its other members form, and
the bound `p` on the number of targets the adversary may select. -/
structure TcrProblem (ι PkSeed Tweak M Y : Type) where
  /-- The tweakable hash whose target-collision resistance is in question. -/
  th : TweakableHash PkSeed Tweak M Y
  /-- The rest of the collection, evaluable by the adversary at the game's seed. -/
  coll : TweakableHashCollection ι PkSeed Tweak Y
  /-- The papers' `p`: the cap on classical queries to the challenge oracle. -/
  numTargets : ℕ

/-- The stand-alone SM-TCR problem, at the empty collection: the collection oracle's query type is
uninhabited, so the adversary has only the challenge oracle. -/
def TcrProblem.standalone (th : TweakableHash PkSeed Tweak M Y) (numTargets : ℕ) :
    TcrProblem Empty PkSeed Tweak M Y where
  th := th
  coll := .empty PkSeed Tweak Y
  numTargets := numTargets

/-- The state threaded through both oracles of the SM-TCR game: the challenge history `Q` of
accepted `(tweak, message)` targets, and the list of tweaks spent on the collection oracle. -/
abbrev TcrState (Tweak M : Type) : Type := List (Tweak × M) × List Tweak

/-- An SM-TCR adversary. `choose` selects targets through the challenge oracle, and may evaluate the
rest of the collection, without access to the public seed; `forge` receives the seed and the private
state, and has no oracle. -/
structure TcrAdversary (prob : TcrProblem ι PkSeed Tweak M Y) where
  /-- Private state carried from `choose` to `forge`. -/
  State : Type
  /-- Select targets through the challenge oracle, with collection access. The public seed is not an
  input. -/
  choose : OracleComp (tcrChallengeSpec Tweak M Y + collectionSpec prob.coll) State
  /-- Given the revealed public seed, name a target index and a colliding message. -/
  forge : State → PkSeed → ProbComp (ℕ × M)

/-- The challenge oracle at a public seed, answering `Th(P, T, M)` and recording `(T, M)` in the
challenge history `Q`. A query is rejected with `none` when the target cap is reached, when its
tweak already occurs in the challenge history, or when its tweak has been spent on the collection
oracle; a rejected query leaves the state untouched.

Accepted queries are appended, so the history is in issue order and `Q[j]` is the `j`-th target. -/
def tcrChallengeOracle [DecidableEq Tweak] (prob : TcrProblem ι PkSeed Tweak M Y) (pk : PkSeed) :
    QueryImpl (tcrChallengeSpec Tweak M Y) (StateT (TcrState Tweak M) ProbComp) :=
  fun tm => do
    let (chal, colls) ← get
    if prob.numTargets ≤ chal.length ∨ (chal.any fun e => e.1 = tm.1) ∨
        colls.any fun t => t = tm.1 then
      return none
    else
      set (chal ++ [tm], colls)
      return some (prob.th.eval pk tm.1 tm.2)

/-- Both oracles of the SM-TCR game over the shared state, at a public seed. -/
def tcrOracles [DecidableEq Tweak] (prob : TcrProblem ι PkSeed Tweak M Y) (pk : PkSeed) :
    QueryImpl (tcrChallengeSpec Tweak M Y + collectionSpec prob.coll)
      (StateT (TcrState Tweak M) ProbComp) :=
  tcrChallengeOracle prob pk + collectionOracle (X := M) prob.coll pk

/-- The SM-TCR experiment. The public seed is sampled, the first phase runs against both oracles
without it, the second phase runs with it and without them, and the adversary wins by naming a
recorded target `j` and a message colliding with — and differing from — the `j`-th recorded message.
An index outside the challenge history loses. -/
noncomputable def tcrExperiment [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {prob : TcrProblem ι PkSeed Tweak M Y} (adv : TcrAdversary prob) : ProbComp Bool := do
  let pk ← prob.th.seedGen
  let (st, chal, _) ← (simulateQ (tcrOracles prob pk) adv.choose).run ([], [])
  let (j, m) ← adv.forge st pk
  match chal[j]? with
  | none => return false
  | some (t, mj) => return decide (m ≠ mj ∧ prob.th.eval pk t m = prob.th.eval pk t mj)

/-- The SM-TCR advantage of an adversary. -/
noncomputable def tcrAdvantage [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {prob : TcrProblem ι PkSeed Tweak M Y} (adv : TcrAdversary prob) : ℝ≥0∞ :=
  Pr[= true | tcrExperiment adv]

/-! ## Pinning the challenge oracle's conventions

A kernel-debt gate cannot see a game that disagrees with the paper. The lemmas below fix the four
branches of `tcrChallengeOracle` and the order of the history, so that a change of convention breaks
a proof rather than passing silently. -/

variable [DecidableEq Tweak] {prob : TcrProblem ι PkSeed Tweak M Y} {pk : PkSeed} {t : Tweak}
  {m : M} {chal : List (Tweak × M)} {colls : List Tweak}

/-- A query with a tweak fresh to both histories, below the target cap, is answered with the hash
and appended to the end of the challenge history. -/
theorem tcrChallengeOracle_run_of_fresh (hlen : chal.length < prob.numTargets)
    (hnew : ∀ e ∈ chal, e.1 ≠ t) (hcoll : t ∉ colls) :
    (tcrChallengeOracle prob pk (t, m)).run (chal, colls) =
      pure (some (prob.th.eval pk t m), (chal ++ [(t, m)], colls)) := by
  have hany : (chal.any fun e => decide (e.1 = t)) = false := by simpa using hnew
  have hcany : (colls.any fun s => decide (s = t)) = false := by
    simpa using fun s hs (h : s = t) => hcoll (h ▸ hs)
  simp [tcrChallengeOracle, Nat.not_le.mpr hlen, hany, hcany]

/-- A query reusing a tweak already in the challenge history is rejected, and the state is
unchanged. -/
theorem tcrChallengeOracle_run_of_reused (m' : M) (hmem : (t, m') ∈ chal) :
    (tcrChallengeOracle prob pk (t, m)).run (chal, colls) = pure (none, (chal, colls)) := by
  have hany : (chal.any fun e => decide (e.1 = t)) = true :=
    List.any_eq_true.mpr ⟨(t, m'), hmem, by simp⟩
  simp [tcrChallengeOracle, hany]

/-- A query at the target cap is rejected, and the state is unchanged. -/
theorem tcrChallengeOracle_run_of_full (hlen : prob.numTargets ≤ chal.length) :
    (tcrChallengeOracle prob pk (t, m)).run (chal, colls) = pure (none, (chal, colls)) := by
  simp [tcrChallengeOracle, hlen]

/-- A query at a tweak already spent on the collection oracle is rejected, and the state is
unchanged. This is the half of the two tweak sets' disjointness that the challenge oracle enforces;
`collectionOracle_run_of_challenge_clash` is the other. -/
theorem tcrChallengeOracle_run_of_collection_clash (hmem : t ∈ colls) :
    (tcrChallengeOracle prob pk (t, m)).run (chal, colls) = pure (none, (chal, colls)) := by
  have hcany : (colls.any fun s => decide (s = t)) = true :=
    List.any_eq_true.mpr ⟨t, hmem, by simp⟩
  simp [tcrChallengeOracle, hcany]

/-! ## An end-to-end order check

`Q[j]` must be the `j`-th accepted challenge query, and the two oracles must share one state. Both
conventions are invisible at a single query and mis-attribute every index at two, so they are pinned
on a concrete probe interleaving the two oracles.

Everything in the probe is deterministic, so the whole run reduces and `rfl` decides the history
outright. `PreProbe` cannot do this — its challenge oracle samples — and states the corresponding
check over `support` instead. -/

namespace TcrProbe

/-- A tweakable hash on `Bool` tweaks with a trivial seed, used only by the order check. -/
def hash : TweakableHash Unit Bool Bool Bool where
  seedGen := pure ()
  eval _ t m := t && m

/-- A one-member collection at the probe's types, so the probe can issue collection queries. -/
def coll : TweakableHashCollection Unit Unit Bool Bool where
  Msg _ := Bool
  eval _ _ t m := t || m

/-- The order-check problem: the probe hash and collection, with room for both target queries. -/
def problem : TcrProblem Unit Unit Bool Bool Bool where
  th := hash
  coll := coll
  numTargets := 2

/-- Two accepted challenge queries, at tweaks `false` then `true`, with a collection query
interleaved between them at tweak `false` — already spent as a target, so it is rejected. That
rejection is itself part of what the check pins. -/
def queries : OracleComp (tcrChallengeSpec Bool Bool Bool + collectionSpec coll) Unit := do
  let _ ← (tcrChallengeSpec Bool Bool Bool + collectionSpec coll).query (.inl (false, true))
  let _ ← (tcrChallengeSpec Bool Bool Bool + collectionSpec coll).query (.inr ⟨(), false, true⟩)
  let _ ← (tcrChallengeSpec Bool Bool Bool + collectionSpec coll).query (.inl (true, false))
  return ()

/-- The challenge history after `TcrProbe.queries` lists the two targets in issue order, so `Q[0]`
is the first target and `Q[1]` the second; the interleaved collection query at an already-issued
target tweak is rejected and leaves both lists untouched. Appending is what makes the order hold;
consing would reverse it. -/
theorem history_in_issue_order :
    (simulateQ (tcrOracles problem ()) queries).run ([], []) =
      pure ((), ([(false, true), (true, false)], [])) := by
  rfl

/-- A collection query at a fresh tweak, then a challenge query at that same tweak. -/
def crossQueries : OracleComp (tcrChallengeSpec Bool Bool Bool + collectionSpec coll) Unit := do
  let _ ← (tcrChallengeSpec Bool Bool Bool + collectionSpec coll).query (.inr ⟨(), false, true⟩)
  let _ ← (tcrChallengeSpec Bool Bool Bool + collectionSpec coll).query (.inl (false, true))
  return ()

/-- The collection oracle's tweak list is the same list the challenge oracle reads: after a
collection query at tweak `false`, a target query at `false` is rejected, so the challenge history
stays empty while the collection list holds `false`.

`tcrChallengeOracle_run_of_collection_clash` cannot catch a mis-wiring here, because it takes the
collection list as a free variable and so never checks that `collectionOracle` is the thing writing
it. Routing the two oracles to separate state slots would satisfy every branch lemma and break only
this. -/
theorem challenge_reads_collection_tweaks :
    (simulateQ (tcrOracles problem ()) crossQueries).run ([], []) =
      pure ((), ([], [false])) := by
  rfl

end TcrProbe

end MultiTarget
