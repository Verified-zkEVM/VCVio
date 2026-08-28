/-
Copyright (c) 2026 Nicolas Consigny, Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.Collection
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.SimSemantics.Append

/-!
# Single-function, distinct-tweak, multi-target preimage resistance (SM-DT-PRE)

The two-phase shape is that of SM-TCR — the public seed is sampled by the experiment, withheld while
the adversary selects targets, then revealed with the challenge oracle removed — but the challenge
oracle differs: the adversary supplies only a tweak, and the oracle draws the message itself from
the subspace `M'`. Winning means producing *any* preimage of a recorded image; unlike SM-TCR there
is no requirement that it differ from the recorded message.

Shortened to `SM-PRE` in the prose below; the declaration names keep the full label.

The adversary rather than the challenger choosing the tweaks is what makes the game usable in a
reduction, which has to place its challenges at the specific addresses where the scheme it simulates
will use them.

`M'` is carried as its own type together with an injective `emb : M' → M`, so the requirement that
the adversary's output lie in the subspace holds by typing rather than by a runtime check. A
subspace carved out of `M` by a predicate is the case `M' := Subtype p`, `emb := Subtype.val`
(`Subtype.val_injective`); the unrestricted notion is `M' := M`, `emb := id`
(`Function.injective_id`).

A strict subspace is needed when the challenge must be distributed as the value a reduction replaces
— a digest, for a hash chain. SM-TCR carries no subspace: there nothing is drawn.

`numTargets` bounds the accepted challenge queries and is the only query bound the game carries. See
`TweakableHash.collectionOracle` for why the tweak restrictions are enforced in the oracles rather
than in the winning condition.

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

namespace TweakableHash

open OracleComp OracleSpec ENNReal

variable {ι PkSeed Tweak M M' Y : Type}

/-! ## The game -/

/-- The challenge oracle's signature: a query is a tweak alone — the oracle picks the message — and
the response is `Option Y`, with `none` marking a rejected query. -/
abbrev SM_DT_PRE_challengeSpec (Tweak Y : Type) : OracleSpec Tweak := Tweak →ₒ Option Y

/-- An SM-PRE problem: the tweakable hash under attack, the subspace `M'` of its message space that
the challenge oracle samples from, the collection its other members form, and the bound on the
number of targets. -/
structure SM_DT_PRE_Problem (ι PkSeed Tweak M M' Y : Type) where
  /-- The tweakable hash whose preimage resistance is in question. -/
  th : TweakableHash PkSeed Tweak M Y
  /-- The map into `M` of the subspace the challenge oracle samples from. -/
  emb : M' → M
  /-- `emb` identifies `M'` with a subset of `M`. This is what makes the oracle's uniform draw on
  `M'` a uniform draw on a subset of `M`: under a non-injective `emb` the law of `emb x` is the
  pushforward of the uniform distribution, which is not uniform on the image. -/
  emb_injective : Function.Injective emb
  /-- The rest of the collection, evaluable by the adversary at the game's seed. -/
  coll : TweakableHashCollection ι PkSeed Tweak Y
  /-- The cap on accepted challenge-oracle queries. -/
  numTargets : ℕ

/-- The stand-alone SM-PRE problem, at the empty collection: the collection oracle's query type is
uninhabited, so the adversary has only the challenge oracle. -/
def SM_DT_PRE_Problem.standalone (th : TweakableHash PkSeed Tweak M Y) (emb : M' → M)
    (emb_injective : Function.Injective emb) (numTargets : ℕ) :
    SM_DT_PRE_Problem Empty PkSeed Tweak M M' Y where
  th := th
  emb := emb
  emb_injective := emb_injective
  coll := .empty PkSeed Tweak Y
  numTargets := numTargets

/-- The state threaded through both oracles of the SM-PRE game: the challenge history of accepted
`(tweak, sampled message)` targets, and the list of tweaks spent on the collection oracle. -/
abbrev SM_DT_PRE_State (Tweak M' : Type) : Type := List (Tweak × M') × List Tweak

/-- An SM-PRE adversary. `choose` selects tweaks through the challenge oracle, and may evaluate the
rest of the collection, without access to the public seed; `invert` receives the seed and the
private state, and has no oracle. -/
structure SM_DT_PRE_Adversary (prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y) where
  /-- Private state carried from `choose` to `invert`. -/
  State : Type
  /-- Select tweaks through the challenge oracle, with collection access. The public seed is not an
  input. -/
  choose : OracleComp (SM_DT_PRE_challengeSpec Tweak Y + collectionSpec prob.coll) State
  /-- Given the revealed public seed, name a target index and a preimage in `M'`. -/
  invert : State → PkSeed → ProbComp (ℕ × M')

/-- The challenge oracle at a public seed: it draws a message uniformly from `M'`, answers with the
hash of that message under the queried tweak, and records the pair in the challenge history. A query
is rejected with `none` when the target cap is reached, when its tweak already occurs in the
challenge history, or when its tweak has been spent on the collection oracle; a rejected query
leaves the state untouched and draws nothing.

Accepted queries are appended, so the history is in issue order and its `j`-th entry is the `j`-th
target. -/
noncomputable def SM_DT_PRE_challengeOracle [DecidableEq Tweak] [SampleableType M']
    (prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y) (pk : PkSeed) :
    QueryImpl (SM_DT_PRE_challengeSpec Tweak Y) (StateT (SM_DT_PRE_State Tweak M') ProbComp) :=
  fun t => do
    let (chal, colls) ← get
    if prob.numTargets ≤ chal.length ∨ (chal.any fun e => e.1 = t) ∨
        colls.any fun s => s = t then
      return none
    else
      let x ← (($ᵗ M' : ProbComp M') : StateT (SM_DT_PRE_State Tweak M') ProbComp M')
      set (chal ++ [(t, x)], colls)
      return some (prob.th.eval pk t (prob.emb x))

/-- Both oracles of the SM-PRE game over the shared state, at a public seed. -/
noncomputable def SM_DT_PRE_oracles [DecidableEq Tweak] [SampleableType M']
    (prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y) (pk : PkSeed) :
    QueryImpl (SM_DT_PRE_challengeSpec Tweak Y + collectionSpec prob.coll)
      (StateT (SM_DT_PRE_State Tweak M') ProbComp) :=
  SM_DT_PRE_challengeOracle prob pk + collectionOracle (X := M') prob.coll pk

/-- The SM-PRE experiment. The public seed is sampled, the first phase runs against both oracles
without it, the second phase runs with it and without them, and the adversary wins by naming a
recorded target `j` and any message of `M'` whose image under the `j`-th recorded tweak agrees with
that of the `j`-th recorded message. An index outside the challenge history loses. -/
noncomputable def SM_DT_PRE_Experiment [DecidableEq Tweak] [DecidableEq Y] [SampleableType M']
    {prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y} (adv : SM_DT_PRE_Adversary prob) :
    ProbComp Bool := do
  let pk ← prob.th.seedGen
  let (st, chal, _) ← (simulateQ (SM_DT_PRE_oracles prob pk) adv.choose).run ([], [])
  let (j, m) ← adv.invert st pk
  match chal[j]? with
  | none => return false
  | some (t, x) =>
      return decide (prob.th.eval pk t (prob.emb m) = prob.th.eval pk t (prob.emb x))

/-- The SM-PRE advantage of an adversary. -/
noncomputable def SM_DT_PRE_Advantage [DecidableEq Tweak] [DecidableEq Y] [SampleableType M']
    {prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y} (adv : SM_DT_PRE_Adversary prob) : ℝ≥0∞ :=
  Pr[= true | SM_DT_PRE_Experiment adv]

/-! ## Pinning the challenge oracle's conventions

A kernel-debt gate cannot see a game that disagrees with the paper. The lemmas below fix the four
branches of `SM_DT_PRE_challengeOracle` and the order of the history, so that a change of convention
breaks a proof rather than passing silently. -/

variable [DecidableEq Tweak] [SampleableType M'] {prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y}
  {pk : PkSeed} {t : Tweak} {chal : List (Tweak × M')} {colls : List Tweak}

/-- A query with a tweak fresh to both histories, below the target cap, draws its message from `M'`,
answers with the hash of that message and appends it to the end of the challenge history. -/
theorem SM_DT_PRE_challengeOracle_run_of_fresh (hlen : chal.length < prob.numTargets)
    (hnew : ∀ e ∈ chal, e.1 ≠ t) (hcoll : t ∉ colls) :
    (SM_DT_PRE_challengeOracle prob pk t).run (chal, colls) =
      (fun x => (some (prob.th.eval pk t (prob.emb x)), (chal ++ [(t, x)], colls))) <$>
        ($ᵗ M') := by
  have hany : (chal.any fun e => decide (e.1 = t)) = false := by simpa using hnew
  have hcany : (colls.any fun s => decide (s = t)) = false := by
    simpa using fun s hs (h : s = t) => hcoll (h ▸ hs)
  simp [SM_DT_PRE_challengeOracle, Nat.not_le.mpr hlen, hany, hcany, Functor.map_map]

/-- A query reusing a tweak already in the challenge history is rejected, and the state is
unchanged. -/
theorem SM_DT_PRE_challengeOracle_run_of_reused (x : M') (hmem : (t, x) ∈ chal) :
    (SM_DT_PRE_challengeOracle prob pk t).run (chal, colls) =
      pure (none, (chal, colls)) := by
  have hany : (chal.any fun e => decide (e.1 = t)) = true :=
    List.any_eq_true.mpr ⟨(t, x), hmem, by simp⟩
  simp [SM_DT_PRE_challengeOracle, hany]

/-- A query at the target cap is rejected, and the state is unchanged. -/
theorem SM_DT_PRE_challengeOracle_run_of_full (hlen : prob.numTargets ≤ chal.length) :
    (SM_DT_PRE_challengeOracle prob pk t).run (chal, colls) =
      pure (none, (chal, colls)) := by
  simp [SM_DT_PRE_challengeOracle, hlen]

/-- A query at a tweak already spent on the collection oracle is rejected, and the state is
unchanged. This is the half of the two tweak sets' disjointness that the challenge oracle enforces;
`collectionOracle_run_of_challenge_clash` is the other. -/
theorem SM_DT_PRE_challengeOracle_run_of_collection_clash (hmem : t ∈ colls) :
    (SM_DT_PRE_challengeOracle prob pk t).run (chal, colls) =
      pure (none, (chal, colls)) := by
  have hcany : (colls.any fun s => decide (s = t)) = true :=
    List.any_eq_true.mpr ⟨t, hmem, by simp⟩
  simp [SM_DT_PRE_challengeOracle, hcany]

end TweakableHash
