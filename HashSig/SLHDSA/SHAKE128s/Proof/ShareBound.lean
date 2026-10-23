/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ShareBlindFacts
public import HashSig.SLHDSA.SHAKE128s.Proof.VerifyBound
public import HashSig.SLHDSA.SHAKE128s.Proof.BlockViews
public import HashSig.SLHDSA.SHAKE128s.Proof.Target127

/-!
# The blind game's bound

The flag of the blind game is a union of guesses, each charged `2 ^ -128`, against the entries
of the record that a charge pays for (`charged`); `blind_bound_of` bounds the flag by `bound`
over `2 ^ 128` for any game whose blind runs keep the charged entries within `bound`.

* **the cell guesses**: an entry that is a sensitive probe guesses a cell the blind run has not
  read, `BlindCharge.prob_sensitive_le` with the facts of `ShareBlindFacts` (`sens_le`);
* **the `SK.prf` guesses**: the blind run never reads `SK.prf`, so it may be drawn after the
  run, and an entry not prefixed by the public seed guesses it at most once (`prf_le`).

The claims file nothing once the flag is up, so the charge is taken at the blind handler's
filing form (`ShareBlindFacts.filing`), which files them whatever the flag: its flag has the blind
game's law (`probEvent_flagGame_eq`).

An entry locating a node is prefixed by the public seed, so the two kinds of guess are counted
against disjoint parts of the record and add to at most its length (`charged_le_length`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SlhDsaSecurity.ShareBound

variable {β γ : Type}

open Security CanonicalGraph ShareGame ShareFlag ShareBlindFacts

/-! ## The record's length -/

/-- The game's handler, read at the verifier's oracles. -/
noncomputable def worldImpl (lenient : Bool) (setup : Setup) :
    QueryImpl OracleWorld (StateT (St × Bool) ProbComp) :=
  QueryImpl.compose (handler lenient setup) fun world =>
    (query (spec := ShareSpec) (worldQuery world) : OracleComp ShareSpec (OracleWorld.Range world))

/-- The game's verifier under the handler is the scheme's verifier under `worldImpl`. -/
theorem verifyShare_run (lenient : Bool) (setup : Setup) (pk : PublicKey) (forgery : Forgery)
    (p : St × Bool) :
    (simulateQ (handler lenient setup) (verifyShare pk forgery)).run p =
      (simulateQ (worldImpl lenient setup)
        (Scheme.verify (m := OracleComp OracleWorld) pk forgery.message
          forgery.signature)).run p := by
  exact congrArg (StateT.run · p) (QueryImpl.simulateQ_compose (handler lenient setup)
    (fun world => (query (spec := ShareSpec) (worldQuery world) :
      OracleComp ShareSpec (OracleWorld.Range world)))
    (Scheme.verify (m := OracleComp OracleWorld) pk forgery.message forgery.signature)).symm

/-- A world query, at a handler that is the game's away from the claims. -/
theorem simulateQ_inl_query (impl : QueryImpl ShareSpec (StateT (St × Bool) ProbComp))
    (lenient : Bool) (setup : Setup)
    (hinl : ∀ queried, impl (Sum.inl queried) = handler lenient setup (Sum.inl queried))
    (queried : (OracleWorld + DrawSpec + AssembleSpec).Domain) :
    simulateQ impl (query (spec := ShareSpec) (Sum.inl queried) :
        OracleComp ShareSpec (ShareSpec.Range (Sum.inl queried))) =
      simulateQ (handler lenient setup) (query (spec := ShareSpec) (Sum.inl queried) :
        OracleComp ShareSpec (ShareSpec.Range (Sum.inl queried))) := by
  erw [simulateQ_spec_query, simulateQ_spec_query]
  exact hinl queried

/-- **Away from the claims, a handler that is the game's reads the adversary's oracles as the
game does.** -/
theorem compose_splitter_of (impl : QueryImpl ShareSpec (StateT (St × Bool) ProbComp))
    (lenient : Bool) (setup : Setup)
    (hinl : ∀ queried, impl (Sum.inl queried) = handler lenient setup (Sum.inl queried)) :
    QueryImpl.compose impl splitter = advImpl lenient setup := by
  funext queried
  rcases queried with world | request
  · exact simulateQ_inl_query impl lenient setup hinl _
  · simp only [advImpl, QueryImpl.apply_compose, splitter, simulateQ_bind]
    rw [simulateQ_inl_query impl lenient setup hinl]
    refine bind_congr fun drawn => ?_
    exact simulateQ_inl_query impl lenient setup hinl _

/-- The same at the verifier's oracles. -/
theorem compose_world_of (impl : QueryImpl ShareSpec (StateT (St × Bool) ProbComp))
    (lenient : Bool) (setup : Setup)
    (hinl : ∀ queried, impl (Sum.inl queried) = handler lenient setup (Sum.inl queried)) :
    QueryImpl.compose impl (fun world =>
      (query (spec := ShareSpec) (worldQuery world) :
        OracleComp ShareSpec (OracleWorld.Range world))) = worldImpl lenient setup := by
  funext world
  exact simulateQ_inl_query impl lenient setup hinl _

/-! ## The blind step never reads `SK.prf` -/

/-- The public key does not depend on `SK.prf`. -/
theorem pk_prf (publicSeed : Digest) (cells : Cells) (prf prf' : Digest) (pad : Padding) :
    (setupOf publicSeed cells (prf, pad)).pk = (setupOf publicSeed cells (prf', pad)).pk := rfl

/-- The strict hash route does not depend on `SK.prf`. -/
theorem route_prf (publicSeed : Digest) (cells : Cells) (prf prf' : Digest) (pad : Padding)
    (state : St) (input : Bytes) :
    route false (setupOf publicSeed cells (prf, pad)) state input =
      route false (setupOf publicSeed cells (prf', pad)) state input := by
  classical
  unfold route
  rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true,
    ite_eq_right (fun h => Bool.false_ne_true h.1), ite_eq_right (fun h => Bool.false_ne_true h.1)]
  rfl

/-- The cell signer does not depend on `SK.prf`. -/
theorem cellSig_prf (publicSeed : Digest) (cells : Cells) (prf prf' : Digest) (pad : Padding)
    (randomizer : Digest) (digest : HashOutput) :
    ShareSigner.cellSig (setupOf publicSeed cells (prf, pad)).warm
        (setupOf publicSeed cells (prf, pad)).sk randomizer digest =
      ShareSigner.cellSig (setupOf publicSeed cells (prf', pad)).warm
        (setupOf publicSeed cells (prf', pad)).sk randomizer digest :=
  ShareSignCongr.cellSig_congr publicSeed prf prf' (cells, pad) (cells, pad)
    (fun _ => Finset.univ) (fun _ _ => rfl) randomizer digest (fun _ => Finset.mem_univ _)

/-- The claims do not depend on `SK.prf`. -/
theorem claimsOf_prf (publicSeed : Digest) (cells : Cells) (prf prf' : Digest) (pad : Padding)
    (state : St) (forgery : Forgery) :
    claimsOf (setupOf publicSeed cells (prf, pad)) state forgery =
      claimsOf (setupOf publicSeed cells (prf', pad)) state forgery := rfl

/-- **The blind step is the same at every `SK.prf`.** -/
theorem blindStep_prf (publicSeed : Digest) (cells : Cells) (prf prf' : Digest) (pad : Padding) :
    blindStep (setupOf publicSeed cells (prf, pad)) =
      blindStep (setupOf publicSeed cells (prf', pad)) := by
  classical
  funext queried state
  rcases queried with ((world | request) | ⟨request, drawn⟩) | forgery
  · rcases world with coin | input
    · rfl
    · simp only [blindStep, route_prf publicSeed cells prf prf' pad]
  · cases hframe : request.frame with
    | none => simp only [blindStep, hframe]
    | some framed =>
      simp only [blindStep, hframe, route_prf publicSeed cells prf prf' pad,
        pk_prf publicSeed cells prf prf' pad]
  · cases drawn with
    | none => rfl
    | some pair =>
      obtain ⟨randomizer, digest⟩ := pair
      simp only [blindStep, cellSig_prf publicSeed cells prf prf' pad]
  · simp only [blindStep, claimsOf_prf publicSeed cells prf prf' pad]

/-! ## Expectations, on the support -/

/-- The expectation is monotone in a functional, pointwise on the support. -/
theorem ex_mono_support {β : Type} (mx : ProbComp β) {f g : β → ℝ≥0∞}
    (h : ∀ x ∈ support mx, f x ≤ g x) : BlindCharge.ex mx f ≤ BlindCharge.ex mx g := by
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · exact mul_le_mul' le_rfl (h x hx)
  · rw [(prEvent_eq_zero_of_not_mem_support _) hx, zero_mul, zero_mul]

/-- The expectation of a constant is at most that constant. -/
theorem ex_const_le {β : Type} (mx : ProbComp β) (c : ℝ≥0∞) :
    BlindCharge.ex mx (fun _ => c) ≤ c := by
  unfold BlindCharge.ex
  rw [ENNReal.tsum_mul_right]
  exact le_trans (mul_le_mul' (OracleComp.tsum_prEvent_le_one _) le_rfl) (by rw [one_mul])

/-- The expectation is additive in the functional. -/
theorem ex_add {β : Type} (mx : ProbComp β) (f g : β → ℝ≥0∞) :
    BlindCharge.ex mx f + BlindCharge.ex mx g = BlindCharge.ex mx (fun x => f x + g x) := by
  unfold BlindCharge.ex
  rw [← ENNReal.tsum_add]
  exact tsum_congr fun x => (mul_add _ _ _).symm

/-- A draw nothing after it reads leaves an event's chance alone. -/
theorem probEvent_bind_const {β γ : Type} (mx : ProbComp β) (f : β → ProbComp γ)
    (event : γ → Prop) (c : ℝ≥0∞) (h : ∀ x, Pr{let y ← f x}[event y] = c) :
    Pr{let x ← mx >>= f}[event x] = c := by
  rw [OracleComp.prEvent_bind_eq_tsum]
  simp only [h]
  rw [ENNReal.tsum_mul_right, OracleComp.tsum_prEvent_eq_one, one_mul]

/-! ## A located entry is prefixed by the public seed -/

/-- An input locating a node is prefixed by the public seed. -/
theorem seedPrefixed_of_locate (publicSeed : Digest) (input : Bytes)
    (hlocate : ((GraphStakes.stakes publicSeed).locate input).isSome) :
    Target127.SeedPrefixed publicSeed input := by
  classical
  change (GraphStakes.locate publicSeed input).isSome at hlocate
  unfold GraphStakes.locate at hlocate
  split at hlocate
  · rename_i hsome
    obtain ⟨node, cell, rfl⟩ := hsome
    exact ⟨node.parent.address.toBytes ++ bytesBE n cell,
      by simp [GraphStakes.inputOf, Hashing.tweakableInput, List.append_assoc]⟩
  · simp at hlocate

open scoped Classical in
/-- Each entry is a locating one or one not prefixed by the public seed, not both. -/
theorem countP_located_add_le (publicSeed : Digest) (entries : List (Bytes × List HashOutput)) :
    entries.countP (fun entry => ((GraphStakes.stakes publicSeed).locate entry.1).isSome) +
        entries.countP (fun entry => decide (¬ Target127.SeedPrefixed publicSeed entry.1)) ≤
      entries.length := by
  induction entries with
  | nil => simp
  | cons entry rest ih =>
    simp only [List.countP_cons, List.length_cons]
    by_cases hlocate : ((GraphStakes.stakes publicSeed).locate entry.1).isSome
    · have hprefixed := seedPrefixed_of_locate publicSeed entry.1 hlocate
      have h1 : (if ((GraphStakes.stakes publicSeed).locate entry.1).isSome = true then 1 else 0)
          = 1 := ite_eq_left hlocate
      have h2 : (if decide (¬ Target127.SeedPrefixed publicSeed entry.1) = true then 1 else 0)
          = 0 := ite_eq_right (by simpa using hprefixed)
      rw [h1, h2]
      omega
    · have h1 : (if ((GraphStakes.stakes publicSeed).locate entry.1).isSome = true then 1 else 0)
          = 0 := ite_eq_right hlocate
      have h2 : (if decide (¬ Target127.SeedPrefixed publicSeed entry.1) = true then 1 else 0)
          ≤ 1 := by split_ifs <;> omega
      rw [h1]
      omega

/-! ## The two games at a public seed -/

/-- The blind run at a setup, flag carried. -/
noncomputable def flagRun (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool))
    (setup : Setup) : ProbComp ((Forgery × Bool) × (St × Bool)) :=
  (simulateQ (handler false setup) (comp setup.pk)).run (St.start, false)

/-- The blind run at a setup, flag dropped. -/
noncomputable def blindRun (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool))
    (setup : Setup) : ProbComp ((Forgery × Bool) × St) :=
  (simulateQ (blindStep setup) (comp setup.pk)).run St.start

/-- The blind run at a setup in its filing form, flag carried. -/
noncomputable def filingRun (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool))
    (setup : Setup) : ProbComp ((Forgery × Bool) × (St × Bool)) :=
  (simulateQ (filing setup) (comp setup.pk)).run (St.start, false)

/-- The filing run, flag dropped, is the blind run. -/
theorem map_filingRun (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) (setup : Setup) :
    (fun z => (z.1, z.2.1)) <$> filingRun comp setup = blindRun comp setup :=
  map_run_filing setup _ St.start false

/-- The blind run does not depend on `SK.prf`. -/
theorem blindRun_prf (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool))
    (publicSeed prf prf' : Digest) (table : Cells × Padding) :
    blindRun comp ⟨prf, publicSeed, table⟩ =
      blindRun comp ⟨prf', publicSeed, table⟩ := by
  change (simulateQ (blindStep (setupOf publicSeed table.1 (prf, table.2)))
      (comp (setupOf publicSeed table.1 (prf, table.2)).pk)).run St.start =
    (simulateQ (blindStep (setupOf publicSeed table.1 (prf', table.2)))
      (comp (setupOf publicSeed table.1 (prf', table.2)).pk)).run St.start
  rw [blindStep_prf publicSeed table.1 prf prf' table.2, pk_prf publicSeed table.1 prf prf' table.2]

/-- **The blind game at a public seed**: `SK.prf` and the table drawn, the run beside them. -/
noncomputable def flagGame (publicSeed : Digest)
    (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) :
    ProbComp (Setup × ((Forgery × Bool) × (St × Bool))) := do
  let prf ← ($ᵗ Digest : ProbComp Digest)
  let table ← ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding))
  let z ← flagRun comp ⟨prf, publicSeed, table⟩
  pure (⟨prf, publicSeed, table⟩, z)

/-- The same, flag dropped. -/
noncomputable def blindGame (publicSeed : Digest)
    (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) :
    ProbComp (Setup × ((Forgery × Bool) × St)) := do
  let prf ← ($ᵗ Digest : ProbComp Digest)
  let table ← ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding))
  let z ← blindRun comp ⟨prf, publicSeed, table⟩
  pure (⟨prf, publicSeed, table⟩, z)

/-- The same, in the filing form. -/
noncomputable def filingGame (publicSeed : Digest)
    (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) :
    ProbComp (Setup × ((Forgery × Bool) × (St × Bool))) := do
  let prf ← ($ᵗ Digest : ProbComp Digest)
  let table ← ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding))
  let z ← filingRun comp ⟨prf, publicSeed, table⟩
  pure (⟨prf, publicSeed, table⟩, z)

/-- The filing game, flag dropped, is the blind game. -/
theorem map_filingGame (publicSeed : Digest)
    (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) :
    (fun w => (w.1, (w.2.1, w.2.2.1))) <$> filingGame publicSeed comp =
      blindGame publicSeed comp := by
  simp only [filingGame, blindGame, map_bind, map_pure, ← map_filingRun, bind_map_left]

/-- **The flag, off a bad walk, has the same law in the blind run and its filing form.** -/
theorem probEvent_flagRun_eq (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool))
    (setup : Setup) :
    Pr{let z ← flagRun comp setup}[setup.Good ∧ z.2.2 = true] =
      Pr{let z ← filingRun comp setup}[setup.Good ∧ z.2.2 = true] := by
  by_cases hgood : setup.Good
  · simp only [hgood, true_and]
    exact (probEvent_filing_eq _ _ St.start).symm
  · simp [hgood]

/-- **The same in the game.** -/
theorem probEvent_flagGame_eq (publicSeed : Digest)
    (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) :
    Pr{let w ← flagGame publicSeed comp}[w.1.Good ∧ w.2.2.2 = true] =
      Pr{let w ← filingGame publicSeed comp}[w.1.Good ∧ w.2.2.2 = true] := by
  unfold flagGame filingGame
  rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
  refine tsum_congr fun prf => congrArg (_ * ·) ?_
  rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
  refine tsum_congr fun table => congrArg (_ * ·) ?_
  rw [bind_pure_comp, bind_pure_comp, prEvent_map, prEvent_map]
  exact probEvent_flagRun_eq comp _

/-- The blind run at a drawn table, `SK.prf` fixed at a default. -/
noncomputable def tableGame (publicSeed : Digest)
    (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) :
    ProbComp ((Cells × Padding) × ((Forgery × Bool) × St)) := do
  let table ← ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding))
  let z ← blindRun comp ⟨default, publicSeed, table⟩
  pure (table, z)

/-! ## The flag is a union of guesses -/

/-- **Off a bad walk, the flag is a guess the record holds**: a sensitive probe, or a probe not
prefixed by the public seed that is in the `PRF_msg` class at `SK.prf`. -/
theorem flag_le (publicSeed : Digest) (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) :
    Pr{let w ← flagGame publicSeed comp}[w.1.Good ∧ w.2.2.2 = true] ≤
      Pr{let w ← blindGame publicSeed comp}[(∃ entry ∈ w.2.2.record, Sens w.1 entry.2 entry.1) ∨
          (∃ entry ∈ w.2.2.record, ¬ Target127.SeedPrefixed publicSeed entry.1 ∧
            RandomizerGate.PrfClass w.1.prf entry.1)] := by
  rw [probEvent_flagGame_eq, ← map_filingGame, prEvent_map]
  refine prEvent_mono_of_support _ _ _ fun w hw hevent => ?_
  obtain ⟨hgood, hflag⟩ := hevent
  simp only [filingGame, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw
  obtain ⟨prf, -, table, -, z, hz, rfl⟩ := hw
  rcases filing_witness _ _ St.start z hz hflag with hbad | ⟨entry, hentry, hguess⟩
  · exact absurd hgood hbad
  · rcases hguess with hsens | hprf
    · exact Or.inl ⟨entry, hentry, hsens⟩
    · refine Or.inr ⟨entry, hentry, fun hprefixed => ?_, hprf⟩
      exact hgood.1 (Target127.eq_of_seedPrefixed (Target127.seedPrefixed_of_prfClass hprf)
        hprefixed)

/-! ## The cell guesses -/

/-- What a frozen run answers: anything. -/
def stall : (queried : ShareSpec.Domain) → ShareSpec.Range queried
  | Sum.inl (Sum.inl (Sum.inl (Sum.inl coin))) => (0 : Fin (coin + 1))
  | Sum.inl (Sum.inl (Sum.inl (Sum.inr _))) => (0 : HashOutput)
  | Sum.inl (Sum.inl (Sum.inr _)) => none
  | Sum.inl (Sum.inr _) => none
  | Sum.inr _ => ()

/-- **The cell guesses cost one unit per locating entry.** -/
theorem sens_le (publicSeed : Digest) (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) :
    Pr{let w ← blindGame publicSeed comp}[∃ entry ∈ w.2.2.record, Sens w.1 entry.2 entry.1] ≤
      BlindCharge.ex (tableGame publicSeed comp) (fun tz =>
        ((tz.2.2.record.countP fun entry =>
          ((GraphStakes.stakes publicSeed).locate entry.1).isSome : Nat) : ℝ≥0∞)) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  have hmarginal : Pr{let w ← blindGame publicSeed comp}[∃ entry ∈ w.2.2.record,
        Sens w.1 entry.2 entry.1] =
      Pr{let tz ← tableGame publicSeed comp}[∃ entry ∈ tz.2.2.record,
        Sens ⟨default, publicSeed, tz.1⟩ entry.2 entry.1] := by
    unfold blindGame
    refine probEvent_bind_const _ _ _ _ fun prf => ?_
    unfold tableGame
    simp only [blindRun_prf comp publicSeed prf default]
    rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
    refine tsum_congr fun table => ?_
    congr 1
    rw [bind_pure_comp, bind_pure_comp, prEvent_map, prEvent_map]
    rfl
  have hexperiment : tableGame publicSeed comp =
      (fun w => ((w.2.1, w.2.2), w.1)) <$> BlindCharge.experiment ($ᵗ Padding : ProbComp Padding)
        (fun cells pad => blindRun comp (setupOf publicSeed cells (default, pad))) := by
    unfold tableGame BlindCharge.experiment
    rw [BlockViews.uniformSample_prod_eq_bind]
    simp only [bind_assoc, pure_bind, map_bind, map_pure]
    rfl
  rw [hmarginal, hexperiment, prEvent_map, BlindCharge.ex_map]
  exact BlindCharge.prob_sensitive_le (GraphStakes.stakes publicSeed) St.record St.served
    ($ᵗ Padding : ProbComp Padding)
    (fun cells pad => blindStep (setupOf publicSeed cells (default, pad)))
    (fun cells pad => comp (setupOf publicSeed cells (default, pad)).pk)
    St.start rfl (fun cells pad served node => ¬ available (setupOf publicSeed cells (default, pad))
      served node) stall (fun index => ¬ AlwaysAvailable index)
    (fun cells pad served index hunavailable =>
      not_alwaysAvailable_of_unavailable _ served index hunavailable)
    (fun _ _ _ _ => OracleComp.prFail_eq_zero _)
    (fun cells pad => files_blindStep _)
    (fun index _ cells pad t st hst z hz hunavailable => hunavailable
      (available_mono _ (fun digest hdigest => (served_prefix _ t st z hz).subset hdigest) index
        (not_not.mp hst)))
    (fun index _ cells other pad hagree t st hunavailable =>
      blindStep_congr publicSeed index cells other (default, pad) hagree t st hunavailable)
    (fun index hindex cells other pad hagree served => by
      rw [available_congr publicSeed cells other (default, pad)
        (agree_alwaysAvailable index hindex cells other hagree)])
    (fun index hindex cells other pad hagree => by
      show comp (setupOf publicSeed cells (default, pad)).pk =
        comp (setupOf publicSeed other (default, pad)).pk
      rw [pk_congr publicSeed index hindex cells other (default, pad) hagree])

/-! ## The `SK.prf` guesses -/

open scoped Classical in
/-- **Against a fresh `SK.prf`, an entry not prefixed by the public seed is one guess.** -/
theorem prob_prf_list_le (publicSeed : Digest) (entries : List (Bytes × List HashOutput)) :
    Pr{let prf ← ($ᵗ Digest : ProbComp Digest)}[∃ entry ∈ entries,
        ¬ Target127.SeedPrefixed publicSeed entry.1 ∧ RandomizerGate.PrfClass prf entry.1] ≤
      ((entries.countP fun entry => decide (¬ Target127.SeedPrefixed publicSeed entry.1) : Nat) :
        ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (prEvent_mono _ _ (fun prf : Digest =>
    ∃ entry ∈ (entries.filter fun entry =>
        decide (¬ Target127.SeedPrefixed publicSeed entry.1)).toFinset,
      RandomizerGate.prfGuess entry.1 = prf) ?_) ?_
  · rintro prf ⟨entry, hentry, hprefixed, hclass⟩
    refine ⟨entry, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hentry, by simpa using hprefixed⟩),
      ?_⟩
    obtain ⟨seed, message, hinput⟩ := hclass
    rw [hinput, RandomizerGate.prfGuess_randomizerInput]
  refine le_trans (prEvent_exists_finset_le _ _ _) ?_
  refine le_trans (Finset.sum_le_sum fun entry _ =>
    le_of_eq (SecretGuessCharge.prob_single_guess (RandomizerGate.prfGuess entry.1))) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  rw [List.countP_eq_length_filter]
  exact List.toFinset_card_le _

open scoped Classical in
/-- **The `SK.prf` guesses cost one unit per entry not prefixed by the public seed.** -/
theorem prf_le (publicSeed : Digest) (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) :
    Pr{let w ← blindGame publicSeed comp}[∃ entry ∈ w.2.2.record,
        ¬ Target127.SeedPrefixed publicSeed entry.1 ∧ RandomizerGate.PrfClass w.1.prf entry.1] ≤
      BlindCharge.ex (tableGame publicSeed comp) (fun tz =>
        ((tz.2.2.record.countP fun entry =>
          decide (¬ Target127.SeedPrefixed publicSeed entry.1) : Nat) : ℝ≥0∞)) /
        ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  have hlaw : blindGame publicSeed comp =ᵈ
      (tableGame publicSeed comp >>= fun tz =>
        ($ᵗ Digest : ProbComp Digest) >>= fun prf =>
          (pure (⟨prf, publicSeed, tz.1⟩, tz.2) : ProbComp (Setup × ((Forgery × Bool) × St)))) := by
    unfold blindGame tableGame
    simp only [blindRun_prf comp publicSeed _ default]
    have hshape : ∀ prf : Digest,
        (do
          let table ← ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding))
          let z ← blindRun comp ⟨default, publicSeed, table⟩
          (pure (⟨prf, publicSeed, table⟩, z) : ProbComp (Setup × ((Forgery × Bool) × St)))) =
        (do
          let table ← ($ᵗ (Cells × Padding) : ProbComp (Cells × Padding))
          let z ← blindRun comp ⟨default, publicSeed, table⟩
          pure (table, z)) >>= fun tz =>
            (pure (⟨prf, publicSeed, tz.1⟩, tz.2) :
              ProbComp (Setup × ((Forgery × Bool) × St))) := by
      intro prf
      simp only [bind_assoc, pure_bind]
    simp only [hshape]
    exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
  rw [hlaw.prEvent_eq, BlindCharge.probEvent_eq_ex_bind, ← BlindCharge.ex_div_const]
  refine BlindCharge.ex_mono _ fun tz => ?_
  rw [bind_pure_comp, prEvent_map]
  exact prob_prf_list_le publicSeed tz.2.2.record

/-! ## The bound -/

open scoped Classical in
/-- **The entries a charge pays for**: those locating a node, and those not prefixed by the
public seed. -/
noncomputable def charged (publicSeed : Digest) (record : List (Bytes × List HashOutput)) : Nat :=
  record.countP (fun entry => ((GraphStakes.stakes publicSeed).locate entry.1).isSome) +
    record.countP (fun entry => decide (¬ Target127.SeedPrefixed publicSeed entry.1))

/-- The charged entries are at most the record's length. -/
theorem charged_le_length (publicSeed : Digest) (record : List (Bytes × List HashOutput)) :
    charged publicSeed record ≤ record.length := by
  classical
  unfold charged
  convert countP_located_add_le publicSeed record

/-- **The blind game's flag, off a bad walk, is at most the charged entries over `2 ^ 128`**,
for any game whose blind runs keep the charged entries within `bound`. -/
theorem blind_bound_of (publicSeed : Digest)
    (comp : PublicKey → OracleComp ShareSpec (Forgery × Bool)) (bound : Nat)
    (hbound : ∀ setup : Setup, setup.publicSeed = publicSeed →
      ∀ z ∈ support (blindRun comp setup), charged publicSeed z.2.record ≤ bound) :
    Pr{let w ← flagGame publicSeed comp}[w.1.Good ∧ w.2.2.2 = true] ≤
      (bound : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
  classical
  refine le_trans (flag_le publicSeed comp) ?_
  refine le_trans (prEvent_or_le _ _ _) ?_
  refine le_trans (add_le_add (sens_le publicSeed comp)
    (prf_le publicSeed comp)) ?_
  rw [ENNReal.div_add_div_same, ex_add]
  refine ENNReal.div_le_div_right ?_ _
  refine le_trans (ex_mono_support _ fun tz htz => ?_) (ex_const_le _ _)
  rw [← Nat.cast_add]
  refine Nat.cast_le.mpr ?_
  simp only [tableGame, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at htz
  obtain ⟨table, -, z, hz, rfl⟩ := htz
  have h := hbound _ rfl z hz
  unfold charged at h
  convert h

end SlhDsaSecurity.ShareBound
