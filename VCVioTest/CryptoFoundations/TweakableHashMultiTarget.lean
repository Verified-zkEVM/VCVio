/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module

public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR

/-!
# End-to-end canaries for the distinct-tweak multi-target games

The pins in `HardnessAssumptions/TweakableHash/` stop at an oracle's `run`; these run the whole
game, winning condition included, on a collapsing tweakable hash where every pair of messages
collides. What is being measured is therefore the bookkeeping, not the hash: which queries the
oracles accept, in what order the challenge history records them, and which index the winning
condition then reads.

Each toy problem places the attacked member inside its own collection
(`TweakableHashCollection.cons`), so the collection oracle can reach it at non-target tweaks and the
interaction between the two histories is observable.

The SM-TCR canaries are chosen so that each one is the sole canary whose verdict changes under one
specific weakening of the oracles: prepending rather than appending an accepted target, dropping
either half of the two histories' disjointness, dropping the target cap, and dropping the
challenge-history tweak check. A canary that merely restates an oracle pin would not separate
those.

`win_challengeThenCollection` is the load-bearing one. The tweak restriction is enforced when a
query arrives, so spending a challenge tweak on the collection oracle *afterwards* costs the
adversary nothing — the collection query is the one rejected. Under the alternative reading, where
a transcript is judged at the end, that same run loses. The two conventions differ on exactly this
execution, and nothing else here distinguishes them.

`win_coin` pins that the target-selection phase can sample. A reduction that simulates a signer
needs coins before the seed is revealed, so `SM_DT_TCR_oracleSpec` carries `unifSpec`; this canary
stops elaborating if that summand goes away.
-/

@[expose] public section

open OracleComp OracleSpec TweakableHash

namespace TweakableHashMultiTargetTest

/-! ## A collapsing tweakable hash

`Unit` seeds keep `seedGen` deterministic, and a constant `eval` makes every message a collision,
so a canary that loses can only be losing on the tweak discipline or the index lookup. -/

/-- The attacked member: one seed, Boolean tweaks and messages, and a constant digest. -/
def toyTh : TweakableHash Unit Bool Bool Bool where
  seedGen := pure ()
  eval _ _ _ := false

/-! ## SM-DT-TCR -/

/-- One target, and the attacked member is the sole member of its own collection. -/
def tcrProb : SM_DT_TCR_Problem (Option Empty) Unit Bool Bool Bool where
  th := toyTh
  thColl := .cons toyTh (.empty Unit Bool Bool)
  numTargets := 1

/-- The same problem at a cap of two, for the canaries that need a second target. -/
def tcrProbTwo : SM_DT_TCR_Problem (Option Empty) Unit Bool Bool Bool :=
  { tcrProb with numTargets := 2 }

variable {ι PkSeed Tweak M Y : Type}

/-- Query the challenge oracle on `(t, m)`. -/
def tcrChallenge (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) (t : Tweak) (m : M) :
    OracleComp (SM_DT_TCR_oracleSpec prob) (Option Y) :=
  liftM ((SM_DT_TCR_oracleSpec prob).query (.inr (.inl (t, m))))

/-- Query the collection oracle on the member, tweak and message named by `q`. -/
def tcrCollection (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y)
    (q : (i : ι) × Tweak × prob.thColl.Msg i) :
    OracleComp (SM_DT_TCR_oracleSpec prob) (Option Y) :=
  liftM ((SM_DT_TCR_oracleSpec prob).query (.inr (.inr q)))

/-- Place one target, then collide with it. -/
def advChallengeOnly : SM_DT_TCR_Adversary tcrProb where
  State := Unit
  choose := do let _ ← tcrChallenge tcrProb true false; return ()
  forge _ _ := pure (0, true)

/-- Spend the tweak on the collection oracle before challenging at it. -/
def advCollectionThenChallenge : SM_DT_TCR_Adversary tcrProb where
  State := Unit
  choose := do
    let _ ← tcrCollection tcrProb ⟨none, true, false⟩
    let _ ← tcrChallenge tcrProb true false
    return ()
  forge _ _ := pure (0, true)

/-- Challenge first, then touch the same tweak through the collection oracle, carrying that oracle's
answer into the second phase. Forging `true` collides and `false` does not, so the game's verdict
reports whether the collection query was rejected. -/
def advChallengeThenCollection : SM_DT_TCR_Adversary tcrProb where
  State := Option Bool
  choose := do
    let _ ← tcrChallenge tcrProb true false
    tcrCollection tcrProb ⟨none, true, false⟩
  forge r _ := pure (0, r.isNone)

/-- Two challenge queries at distinct tweaks against a cap of one, forging at the second. -/
def advOverCap : SM_DT_TCR_Adversary tcrProb where
  State := Unit
  choose := do
    let _ ← tcrChallenge tcrProb true false
    let _ ← tcrChallenge tcrProb false false
    return ()
  forge _ _ := pure (1, true)

/-- Two challenge queries at the *same* tweak with different messages, below the cap, forging
against the second. -/
def advReusedTweak : SM_DT_TCR_Adversary tcrProbTwo where
  State := Unit
  choose := do
    let _ ← tcrChallenge tcrProbTwo true false
    let _ ← tcrChallenge tcrProbTwo true true
    return ()
  forge _ _ := pure (1, false)

/-- Two targets whose messages differ, forging the second one's own message at index `1`. Colliding
with a message requires differing from it, so this loses exactly when index `1` holds the *second*
target. -/
def advOrder : SM_DT_TCR_Adversary tcrProbTwo where
  State := Unit
  choose := do
    let _ ← tcrChallenge tcrProbTwo true false
    let _ ← tcrChallenge tcrProbTwo false true
    return ()
  forge _ _ := pure (1, true)

/-- Place one target and forge against an index the challenge history does not have. -/
def advOutOfRange : SM_DT_TCR_Adversary tcrProb where
  State := Unit
  choose := do let _ ← tcrChallenge tcrProb true false; return ()
  forge _ _ := pure (5, true)

/-- Flip a coin during target selection, carry it into the second phase, and collide. -/
def advCoin : SM_DT_TCR_Adversary tcrProb where
  State := Fin 2
  choose := do
    let b ← (liftM ((SM_DT_TCR_oracleSpec tcrProb).query (.inl 1)) :
      OracleComp (SM_DT_TCR_oracleSpec tcrProb) (Fin 2))
    let _ ← tcrChallenge tcrProb true false
    return b
  forge _ _ := pure (0, true)

/-- A target placed through the challenge oracle and collided with at its own index wins. -/
theorem win_challengeOnly : SM_DT_TCR_Game advChallengeOnly = pure true := by rfl

/-- Reaching a tweak through the collection oracle first makes the later challenge query at that
tweak be rejected, so nothing is recorded and index `0` is out of range. -/
theorem lose_collectionThenChallenge :
    SM_DT_TCR_Game advCollectionThenChallenge = pure false := by rfl

/-- The same two queries in the other order still win: the challenge is recorded, and it is the
collection query that gets rejected. Rejection happens on arrival, so a challenge tweak spent
afterwards does not retroactively invalidate the target. Winning here also requires the collection
oracle to have answered `none`, which the adversary reads off its own state. -/
theorem win_challengeThenCollection :
    SM_DT_TCR_Game advChallengeThenCollection = pure true := by rfl

/-- A challenge query past the target cap is rejected, so the second target never exists. -/
theorem lose_overCap : SM_DT_TCR_Game advOverCap = pure false := by rfl

/-- A second challenge query at a tweak already in the challenge history is rejected even below the
cap, so no second target exists to forge against. -/
theorem lose_reusedTweak : SM_DT_TCR_Game advReusedTweak = pure false := by rfl

/-- Accepted targets are appended, so index `1` holds the second one and forging its own message
fails to differ from it. -/
theorem lose_order : SM_DT_TCR_Game advOrder = pure false := by rfl

/-- An index outside the challenge history loses. -/
theorem lose_outOfRange : SM_DT_TCR_Game advOutOfRange = pure false := by rfl

/-- The coin drawn during target selection is threaded through to the result, and the collision wins
on either draw. -/
theorem win_coin :
    SM_DT_TCR_Game advCoin =
      (liftM (unifSpec.query 1) : ProbComp (Fin 2)) >>= fun _ => pure true := by
  rfl

/-! ## SM-DT-PRE -/

/-- A singleton subspace of the message space. The `SampleableType` instance below is written out
rather than inferred, so that the challenge oracle's draw reduces and the canaries below close by
`rfl`. -/
inductive Digest
  /-- The only element. -/
  | zero
  deriving DecidableEq

instance : SampleableType Digest where
  selectElem := pure .zero
  mem_support_selectElem := by simp
  probOutput_selectElem_eq x y := by cases x; cases y; rfl

/-- One target, drawing its challenge preimages from `Digest`. -/
def preProb : SM_DT_PRE_Problem (Option Empty) Unit Bool Bool Digest Bool where
  th := toyTh
  emb := fun _ => false
  emb_injective := fun a b _ => by cases a; cases b; rfl
  thColl := .cons toyTh (.empty Unit Bool Bool)
  numTargets := 1

/-- Query the challenge oracle at tweak `t`; the oracle picks the preimage. -/
def preChallenge (t : Bool) : OracleComp (SM_DT_PRE_oracleSpec preProb) (Option Bool) :=
  liftM ((SM_DT_PRE_oracleSpec preProb).query (.inr (.inl t)))

/-- Query the collection oracle on the attacked member at `(t, m)`. -/
def preCollection (t m : Bool) : OracleComp (SM_DT_PRE_oracleSpec preProb) (Option Bool) :=
  liftM ((SM_DT_PRE_oracleSpec preProb).query (.inr (.inr ⟨none, t, m⟩)))

/-- Place one target, then invert it. -/
def preAdvChallengeOnly : SM_DT_PRE_Adversary preProb where
  State := Unit
  choose := do let _ ← preChallenge true; return ()
  invert _ _ := pure (0, .zero)

/-- Spend the tweak on the collection oracle before challenging at it. -/
def preAdvCollectionThenChallenge : SM_DT_PRE_Adversary preProb where
  State := Unit
  choose := do
    let _ ← preCollection true false
    let _ ← preChallenge true
    return ()
  invert _ _ := pure (0, .zero)

/-- A target placed through the challenge oracle and inverted at its own index wins. -/
theorem pre_win_challengeOnly : SM_DT_PRE_Game preAdvChallengeOnly = pure true := by rfl

/-- Reaching a tweak through the collection oracle first makes the later challenge query at that
tweak be rejected, so nothing is drawn and index `0` is out of range. -/
theorem pre_lose_collectionThenChallenge :
    SM_DT_PRE_Game preAdvCollectionThenChallenge = pure false := by rfl

end TweakableHashMultiTargetTest
