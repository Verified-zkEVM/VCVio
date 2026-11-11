/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ShareGame
public import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# The two games raise the flag equally often

Off the flag the lenient and the blind handler take the same step. The flag is raised by exactly
the queries at which their answers could differ — a canonical input at a closed node is a
sensitive probe, a `PRF_msg` input at the real seed is in its class, and a drawn randomiser
equal to the seed is the signer's coincidence — so VCVio's identical-until-bad law
(`OracleComp.ProgramLogic.Relational.prEvent_simulateQ_run_bad_eq`) gives the flag the same
probability in both.

The two facts about the table that make "closed" mean "sensitive" are here too:
`openAt_le_warm` (the open table is part of the full one) and `sens_of_closed` (a canonical
entry the open table lacks has exactly one child, unavailable).
-/

public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.SHAKE128s.ShareUntilBad

variable {α : Type}

open Security CanonicalGraph ShareGame

/-! ## The open table inside the full one -/

/-- An entry of the open table is an entry of the warm cache. -/
theorem openAt_le_warm (setup : Setup) (served : List HashOutput) (input : Bytes)
    (answer : HashOutput) (hopen : openAt setup served input = some answer) :
    setup.warm input = some answer := by
  classical
  have hne : openAt setup served input ≠ none := by rw [hopen]; simp
  obtain ⟨parent, rfl⟩ := Programming.cacheFrom_empty_canonical _ _ _ _ input hne
  rw [openAt, OpenCache.openCache, Programming.cacheFrom_lookup] at hopen
  split_ifs at hopen with hmem
  · rw [Setup.warm, Programming.cacheFrom_lookup, ite_eq_left (Programming.mem_order parent)]
    exact hopen
  · simp at hopen

/-- The revealed digits never exceed the last chain position. -/
theorem revealed_le (setup : Setup) (key : WotsKey) (chain : Fin chains) :
    ShareCells.revealedOf setup.table.1 key chain ≤ w - 1 :=
  ShareCells.revealedOf_le setup.table.1 key chain

/-- **A canonical entry the open table lacks is a sensitive probe.** -/
theorem sens_of_closed (setup : Setup) (served : List HashOutput) (input : Bytes)
    (answer : HashOutput) (hwarm : setup.warm input = some answer)
    (hclosed : openAt setup served input = none) : Sens setup served input := by
  classical
  obtain ⟨parent, rfl⟩ := Programming.cacheFrom_empty_canonical setup.publicSeed setup.table.1
    (fullOutput setup.table.1 setup.table.2) Programming.order input
    (by rw [Setup.warm] at hwarm; rw [hwarm]; simp)
  have hnotOpen : parent ∉ OpenCache.openNodes (available setup served) := by
    intro hmem
    rw [openAt, OpenCache.openCache, Programming.cacheFrom_lookup, ite_eq_left hmem] at hclosed
    exact absurd hclosed (by simp)
  rw [OpenCache.mem_openNodes] at hnotOpen
  push Not at hnotOpen
  obtain ⟨child, hchild, hunavailable⟩ := hnotOpen
  rcases children_alwaysAvailable_or_singleton parent with halways | ⟨single, hsingle⟩
  · exact absurd (available_of_alwaysAvailable _ _ (revealed_le setup) (halways child hchild))
      hunavailable
  · rw [hsingle, List.mem_singleton] at hchild
    subst hchild
    refine ⟨⟨parent, child, hsingle⟩, hunavailable, ?_⟩
    exact GraphStakes.inputOf_eq_canonicalInput setup.publicSeed ⟨parent, child, hsingle⟩
      setup.table.1

/-! ## Off the flag, the routing agrees -/

/-- A `SK.prf` input of the setup lies in the `SK.prf` class of its key. -/
theorem prfClass_of_isPrfInput (setup : Setup) (input : Bytes)
    (hprf : IsPrfInput setup input) : RandomizerGate.PrfClass setup.prf input :=
  ⟨setup.publicSeed, prfFrame input, hprf⟩

/-- **A hash query that is no guess is routed the same way by both handlers.** -/
theorem route_eq (setup : Setup) (state : St) (input : Bytes)
    (hguess : ¬ Guess setup state.served input) :
    route true setup state input = route false setup state input := by
  classical
  have hnotSens : ¬ Sens setup state.served input := fun h => hguess (Or.inl h)
  have hnotPrf : ¬ IsPrfInput setup input := fun h =>
    hguess (Or.inr (prfClass_of_isPrfInput setup input h))
  have hsame : setup.warm input = openAt setup state.served input := by
    cases hopen : openAt setup state.served input with
    | some answer => exact openAt_le_warm setup state.served input answer hopen
    | none =>
      cases hwarm : setup.warm input with
      | none => rfl
      | some answer =>
        exact (hnotSens (sens_of_closed setup state.served input answer hwarm hopen)).elim
  unfold route
  rw [ite_eq_left rfl, ite_eq_right Bool.false_ne_true, hsame]
  cases openAt setup state.served input with
  | some value => rfl
  | none => simp [hnotPrf]

/-! ## A good walk keeps the digest input cold -/

/-- On a good setup, the warm cache holds no message-digest input. -/
theorem warm_messageInput (setup : Setup) (hgood : setup.Good) (randomizer : Digest)
    (framed : Bytes) : setup.warm (Hashing.messageInput randomizer setup.pk framed) = none := by
  by_contra hsome
  obtain ⟨parent, hparent⟩ := Programming.cacheFrom_empty_canonical setup.publicSeed
    setup.table.1 (fullOutput setup.table.1 setup.table.2) Programming.order _ hsome
  rw [canonicalInput] at hparent
  exact HashSeparation.message_tweakable_ne (randomizer := randomizer) (pk := setup.pk)
    (message := framed) (seed := setup.publicSeed) hgood.2 (withinBounds_structural parent)
    hparent

/-- On a good setup, the open table holds no message-digest input. -/
theorem openAt_messageInput (setup : Setup) (hgood : setup.Good) (served : List HashOutput)
    (randomizer : Digest) (framed : Bytes) :
    openAt setup served (Hashing.messageInput randomizer setup.pk framed) = none :=
  ServedAgreement.openCache_messageInput_eq_none setup.publicSeed randomizer setup.pk
    framed hgood.2 _ setup.table

/-- **The signer's digest query is routed the same way**, off its coincidence. -/
theorem route_digest_eq (setup : Setup) (hgood : setup.Good) (state : St)
    (randomizer : Digest) (framed : Bytes)
    (hnotPrf : ¬ IsPrfInput setup (Hashing.messageInput randomizer setup.pk framed)) :
    route true setup state (Hashing.messageInput randomizer setup.pk framed) =
      route false setup state (Hashing.messageInput randomizer setup.pk framed) := by
  classical
  simp only [route, ite_true, warm_messageInput setup hgood, Bool.false_eq_true, false_and,
    ite_false, true_and, hnotPrf, openAt_messageInput setup hgood]

/-! ## The step law off the flag -/

open scoped Classical in
/-- **Off the flag, the two handlers take the same step.** -/
theorem agree_good (setup : Setup) (queried : ShareSpec.Domain) (state : St)
    (answer : ShareSpec.Range queried) (next : St) :
    Pr{let x ← ((handler true setup) queried).run (state, false)}[x = (answer, (next, false))] =
      Pr{let x ← ((handler false setup) queried).run (state, false)}[
        x = (answer, (next, false))] := by
  classical
  rcases queried with ((world | request) | ⟨request, drawn⟩) | forgery
  · rcases world with coin | input
    · rfl
    · by_cases hflag : ¬ setup.Good ∨ Guess setup state.served input
      · -- both raise the flag
        have hzero : ∀ lenient : Bool,
            Pr{let x ← (((handler lenient setup)
              (Sum.inl (Sum.inl (Sum.inl (Sum.inr input))))).run (state, false))}[
                x = (answer, (next, false))] = 0 := by
          intro lenient
          refine (prEvent_eq_zero_of_not_mem_support _) fun hmem => ?_
          simp only [handler, StateT.run, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at hmem
          obtain ⟨step, -, heq⟩ := hmem
          have := congrArg (fun z => z.2.2) heq
          simp only [Bool.false_or] at this
          exact absurd (decide_eq_true hflag) (by rw [← this]; simp)
        rw [hzero true, hzero false]
      · have hguess : ¬ Guess setup state.served input := fun h => hflag (Or.inr h)
        simp only [handler, StateT.run, route_eq setup state input hguess]
  · cases hframe : request.frame with
    | none => simp only [handler, StateT.run, hframe]
    | some framed =>
      simp only [handler, StateT.run, hframe]
      rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
      refine tsum_congr fun seed => ?_
      congr 1
      by_cases hflag : ¬ setup.Good ∨ Guess setup state.served
        (Hashing.messageInput (Hashing.truncate seed.1) setup.pk framed)
      · rw [(prEvent_eq_zero_of_not_mem_support _), (prEvent_eq_zero_of_not_mem_support _)] <;>
        · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff, not_exists,
            not_and]
          intro digest _ heq
          simp [hflag] at heq
      · push Not at hflag
        rw [route_digest_eq setup hflag.1 seed.2 _ framed fun h =>
          hflag.2 (Or.inr (prfClass_of_isPrfInput setup _ h))]
  · rfl
  · rfl

/-- **Once raised, the flag stays.** -/
theorem mono (lenient : Bool) (setup : Setup) (queried : ShareSpec.Domain)
    (state : St × Bool) (hbad : state.2 = true)
    (z : ShareSpec.Range queried × (St × Bool))
    (hz : z ∈ support (((handler lenient setup) queried).run state)) : z.2.2 = true := by
  classical
  obtain ⟨inner, flag⟩ := state
  subst hbad
  rcases queried with ((world | request) | ⟨request, drawn⟩) | forgery
  · rcases world with coin | input
    · simp only [handler, StateT.run, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨value, -, rfl⟩ := hz
      rfl
    · simp only [handler, StateT.run, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨step, -, rfl⟩ := hz
      simp
  · cases hframe : request.frame with
    | none =>
      simp only [handler, StateT.run, hframe, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
    | some framed =>
      simp only [handler, StateT.run, hframe, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hz
      obtain ⟨seed, -, digest, -, rfl⟩ := hz
      simp
  · cases drawn with
    | none =>
      simp only [handler, StateT.run, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
    | some pair =>
      obtain ⟨randomizer, digest⟩ := pair
      simp only [handler, StateT.run] at hz
      split_ifs at hz <;>
      · rw [support_pure, Set.mem_singleton_iff] at hz
        rw [hz]
  · simp only [handler, StateT.run, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    simp

/-- **The flag has the same law in both games.** -/
theorem prEvent_bad_eq (setup : Setup) {α : Type} (computation : OracleComp ShareSpec α)
    (start : St) :
    Pr{let z ← (simulateQ (handler true setup) computation).run (start, false)}[z.2.2 = true] =
      Pr{let z ← (simulateQ (handler false setup) computation).run (start, false)}[z.2.2 = true] :=
  OracleComp.ProgramLogic.Relational.prEvent_simulateQ_run_bad_eq _ _ (fun s => s.2 = true)
    (fun queried state hgood q => by
      obtain ⟨inner, flag⟩ := state
      obtain rfl : flag = false := by simpa using hgood
      exact OracleComp.ProgramLogic.Relational.prEvent_and_not_flag_eq_of_forall_prEvent_eq
        (fun answer next => agree_good setup queried inner answer next) q)
    (fun queried state hbad z hz => mono true setup queried state hbad z hz)
    (fun queried state hbad z hz => mono false setup queried state hbad z hz)
    computation (start, false)

end SLHDSA.SHAKE128s.ShareUntilBad
