/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.CoverageRun

/-!
# One- and two-position credits for FORS disclosure

For an arbitrary validated parameter set and core hash primitives, the terminal credit for a
designated actual-key query is bounded by its initial potential. Two designated queries admit
a product bound under the same randomizer discipline. The finite initial credit uses the
cache invariant that holds at the start of the experiment.
-/

@[expose] public section
open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal
open SLHDSA.Security

namespace SLHDSA.Security.Coverage.ActualKeyPotential

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-- The current actual-key point occupying the designated forger-tape slot, if any. -/
def ActualSlot (pk : PublicKeyCore core) (s : RoleState core) (index : Nat) : Prop :=
  ∃ R M, s.2.1.cls (hmsgPoint core pk R M) = some TapeClass.forger ∧
    s.2.1.pos (hmsgPoint core pk R M) = some index

/-- A designated actual-key point has already fired. -/
def Fired (pk : PublicKeyCore core) (s : RoleState core) (index : Nat) : Prop :=
  ∃ R M, s.2.1.cls (hmsgPoint core pk R M) = some TapeClass.forger ∧
    s.2.1.pos (hmsgPoint core pk R M) = some index ∧ hmsgPoint core pk R M ∈ s.2.2

/-- An assigned actual-key point has its unique deterministic nonce cell still uncached. -/
def Live (pk : PublicKeyCore core) (kappa : PublicKeyCore core → core.Y)
    (s : RoleState core) (index : Nat) : Prop :=
  ∃ R M, s.2.1.cls (hmsgPoint core pk R M) = some TapeClass.forger ∧
    s.2.1.pos (hmsgPoint core pk R M) = some index ∧
      s.1.1 (.inr (.inr (kappa pk, M))) = none

/-- A randomizer point uses the one deterministic salt at this public key. -/
def GoodPoint (pk : PublicKeyCore core) (kappa : PublicKeyCore core → core.Y) :
    (jointSpec core).Domain → Prop
  | .inr (.inr (salt, _)) => salt = kappa pk
  | _ => True

/-- Ambient uniform queries and correctly salted randomizer queries are allowed. -/
def GoodQuery (pk : PublicKeyCore core) (kappa : PublicKeyCore core → core.Y) :
    (roleSpec core).Domain → Prop
  | .inl _ => True
  | .inr (.inl point) | .inr (.inr point) => GoodPoint core pk kappa point

/-- The signer's query at the one deterministic nonce cell for a message. -/
abbrev nonceQuery (pk : PublicKeyCore core) (kappa : PublicKeyCore core → core.Y)
    (M : List Byte) : (roleSpec core).Domain :=
  .inr (.inr (.inr (.inr (kappa pk, M))))

/-- A correctly salted point related to the target is its unique nonce cell. -/
theorem randRel_key (pk : PublicKeyCore core) (kappa : PublicKeyCore core → core.Y)
    (R : core.Y) (M : List Byte) (point : (jointSpec core).Domain)
    (answer : (jointSpec core).Range point) (good : GoodPoint core pk kappa point)
    (related : randRel core point answer (hmsgPoint core pk R M)) :
    point = .inr (.inr (kappa pk, M)) := by
  rcases point with ((point | point) | (point | ⟨salt, message⟩))
  · exact related.elim
  · exact related.elim
  · exact related.elim
  · change R = answer ∧ M = message at related
    change salt = kappa pk at good
    cases good
    cases related.2
    rfl

/-- Once the deterministic nonce cell is cached, a new allowed draw cannot hit its target. -/
theorem not_mem_freshHit_of_cached (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y) (R : core.Y) (M : List Byte)
    (cache : (jointSpec core).QueryCache) (hits : Set (jointSpec core).Domain)
    (cached : cache (.inr (.inr (kappa pk, M))) ≠ none)
    (notHit : hmsgPoint core pk R M ∉ hits)
    (point : (jointSpec core).Domain) (answer : (jointSpec core).Range point)
    (good : GoodPoint core pk kappa point) :
    hmsgPoint core pk R M ∉
      AnswerTape.freshHitStep (IsRandPoint core) (randRel core) cache point answer hits := by
  classical
  by_cases fresh : cache point = none ∧ IsRandPoint core point
  · rw [AnswerTape.freshHitStep, ite_eq_left fresh]
    rintro (old | ⟨_, related⟩)
    · exact notHit old
    · have same := randRel_key core pk kappa R M point answer good related
      exact cached (same ▸ fresh.1)
  · rw [AnswerTape.freshHitStep, ite_eq_right fresh]
    exact notHit

/-- A new allowed hit must be drawn at the target's deterministic nonce cell. -/
theorem freshHit_new_key (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y) (R : core.Y) (M : List Byte)
    (cache : (jointSpec core).QueryCache) (hits : Set (jointSpec core).Domain)
    (notHit : hmsgPoint core pk R M ∉ hits)
    (point : (jointSpec core).Domain) (answer : (jointSpec core).Range point)
    (good : GoodPoint core pk kappa point)
    (hit : hmsgPoint core pk R M ∈
      AnswerTape.freshHitStep (IsRandPoint core) (randRel core) cache point answer hits) :
    point = .inr (.inr (kappa pk, M)) := by
  classical
  by_cases fresh : cache point = none ∧ IsRandPoint core point
  · rw [AnswerTape.freshHitStep, ite_eq_left fresh] at hit
    rcases hit with old | ⟨_, related⟩
    · exact (notHit old).elim
    · exact randRel_key core pk kappa R M point answer good related
  · rw [AnswerTape.freshHitStep, ite_eq_right fresh] at hit
    exact (notHit hit).elim

/-- The banked single-nonce credit, with the existing hit invariant as its domain guard. -/
noncomputable def potential (pk : PublicKeyCore core) (kappa : PublicKeyCore core →
  core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j)) (index : Nat)
    (s : RoleState core) : ℝ≥0∞ := by
  classical
  exact if AnswerTape.HitInv (tapeClass core) L s then
    if Fired core pk s index then 1
    else if ¬ActualSlot core pk s index ∨ Live core pk kappa s index then
      (Nat.card core.Y : ℝ≥0∞)⁻¹ else 0
  else ⊤

/-- An assigned actual-key tape slot has already been reached by the query counter. -/
theorem actualSlot_reached (pk : PublicKeyCore core)
    (L : (j : TapeClass) → List (tapeClassRange core j))
    {s : RoleState core} (hs : AnswerTape.HitInv (tapeClass core) L s) {index : Nat}
    (hslot : ActualSlot core pk s index) : index < s.2.1.cnt TapeClass.forger := by
  obtain ⟨R, M, hc, hp⟩ := hslot
  exact lt_of_lt_of_le (hs.1.pos_spec _ _ _ hc hp).1 (hs.1.next_le_cnt _)

/-- A fired actual-key position is necessarily reached. -/
theorem fired_reached (pk : PublicKeyCore core)
    (L : (j : TapeClass) → List (tapeClassRange core j))
    {s : RoleState core} (hs : AnswerTape.HitInv (tapeClass core) L s) {index : Nat}
    (hfired : Fired core pk s index) : index < s.2.1.cnt TapeClass.forger := by
  obtain ⟨R, M, hc, hp, -⟩ := hfired
  exact actualSlot_reached core pk L hs ⟨R, M, hc, hp⟩

/-- Terminal credit covers a hit and the unused credit on every not-reached branch. -/
noncomputable def terminalValue (pk : PublicKeyCore core) (index : Nat)
    (s : RoleState core) : ℝ≥0∞ := by
  classical
  exact (if Fired core pk s index then (1 : ℝ≥0∞) else 0) +
    (if ¬index < s.2.1.cnt TapeClass.forger then (Nat.card core.Y : ℝ≥0∞)⁻¹ else 0)

/-- Terminal credit is dominated by the native potential at every state. -/
theorem terminal_credit (pk : PublicKeyCore core) (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j)) (index : Nat) (s : RoleState core) :
    terminalValue core pk index s ≤ potential core pk kappa L index s := by
  classical
  unfold terminalValue
  by_cases hs : AnswerTape.HitInv (tapeClass core) L s
  swap
  · simp only [potential, hs, ↓reduceIte, le_top]
  by_cases hf : Fired core pk s index
  · have reached := fired_reached core pk L hs hf
    simp [potential, hs, hf, reached]
  by_cases hn : ¬index < s.2.1.cnt TapeClass.forger
  · have hslot : ¬ActualSlot core pk s index := fun h =>
      hn (actualSlot_reached core pk L hs h)
    simp [potential, hs, hf, hn, hslot]
  · simp [hf, hn]

/-- A cached nonce cell excludes every live witness at its assigned actual-key slot. -/
theorem not_live_of_cached (pk : PublicKeyCore core) (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j))
    {s : RoleState core} (hs : AnswerTape.HitInv (tapeClass core) L s)
    (index : Nat) (R : core.Y) (M : List Byte)
    (hc : s.2.1.cls (hmsgPoint core pk R M) = some TapeClass.forger)
    (hp : s.2.1.pos (hmsgPoint core pk R M) = some index)
    (cached : s.1.1 (.inr (.inr (kappa pk, M))) ≠ none) :
    ¬Live core pk kappa s index := by
  rintro ⟨otherR, otherM, otherClass, otherPos, fresh⟩
  have same := hs.1.pos_inj (hmsgPoint core pk otherR otherM) (hmsgPoint core pk R M)
    TapeClass.forger index otherClass otherPos hc hp
  have sameMessage := ((hmsgPoint_inj core pk).1 same).2
  exact cached (sameMessage ▸ fresh)

/-- The empty role state banks one nonce credit for every public key and slot. -/
theorem potential_initial (pk : PublicKeyCore core) (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j)) (index : Nat) :
    potential core pk kappa L index ((∅, L), (AnswerTape.ClassPos.init, ∅)) =
      (Nat.card core.Y : ℝ≥0∞)⁻¹ := by
  classical
  have initial : AnswerTape.HitInv (tapeClass core) L
      (((∅, L), (AnswerTape.ClassPos.init, ∅)) : RoleState core) :=
    ⟨AnswerTape.ClassPosInv.empty (tapeClass core) L, fun _ hit => hit.elim⟩
  unfold potential
  rw [ite_eq_left initial]
  simp [Fired, ActualSlot, AnswerTape.ClassPos.init]

section Step

variable [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.Y]
  [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]
  {t : (roleSpec core).Domain} {s : RoleState core}
  {y : (roleSpec core).Range t × RoleState core}

/-- A fired actual-key point was already assigned before the step that recorded it. -/
theorem fired_preassigned (pk : PublicKeyCore core)
    (L : (j : TapeClass) → List (tapeClassRange core j))
    (hs : AnswerTape.HitInv (tapeClass core) L s)
    (hy : y ∈ support ((roleRunImpl core t).run s)) {index : Nat}
    (hf : Fired core pk y.2 index) : ActualSlot core pk s index := by
  obtain ⟨R, M, hc, hp, hh⟩ := hf
  have old := (AnswerTape.hitCleared_iff_of_mem_support_classPosImplFwd_run
    (IsRandPoint core) (randRel core) (tapeClass core) (range_eq_tapeClassRange core)
    hs hy index).1 ⟨hmsgPoint core pk R M, hc, hp, hh⟩
  obtain ⟨point, oldClass, oldPos, -⟩ := old
  have keeps := AnswerTape.cls_pos_of_mem_support_classPosImplFwd_run
    (IsRandPoint core) (randRel core) (tapeClass core) (range_eq_tapeClassRange core)
    hs hy oldClass
  have after := AnswerTape.hitInv_of_mem_support_classPosImplFwd_run
    (IsRandPoint core) (randRel core) (tapeClass core) (range_eq_tapeClassRange core) hs hy
  have same := after.1.pos_inj point (hmsgPoint core pk R M) TapeClass.forger index
    keeps.1 (keeps.2.trans oldPos) hc hp
  subst point
  exact ⟨R, M, oldClass, oldPos⟩

/-- Existing actual-key hits persist through every step. -/
theorem fired_persists (pk : PublicKeyCore core)
    (L : (j : TapeClass) → List (tapeClassRange core j))
    (hs : AnswerTape.HitInv (tapeClass core) L s)
    (hy : y ∈ support ((roleRunImpl core t).run s)) {index : Nat}
    (hf : Fired core pk s index) : Fired core pk y.2 index := by
  obtain ⟨R, M, hc, hp, hh⟩ := hf
  have keeps := AnswerTape.cls_pos_of_mem_support_classPosImplFwd_run
    (IsRandPoint core) (randRel core) (tapeClass core) (range_eq_tapeClassRange core)
    hs hy hc
  have hits := (AnswerTape.mono_of_mem_support_classPosImplFwd_run
    (IsRandPoint core) (randRel core) (tapeClass core) (range_eq_tapeClassRange core)
    t s y hy).2.2.1
  exact ⟨R, M, keeps.1, keeps.2.trans hp, hits hh⟩

/-- The passive hit-set update is exactly the pre-cache update of the underlying query. -/
theorem hits_step (hy : y ∈ support ((roleRunImpl core t).run s)) :
    y.2.2.2 = AnswerTape.freshHitAux (IsRandPoint core) (randRel core)
      t s.1 y.1 y.2.1 s.2.2 := by
  have equation := (QueryImpl.mem_support_extendState_run_iff _ _ t s y).1 hy |>.2
  exact congrArg Prod.snd equation

/-- At an already assigned slot, firing is precisely membership of its one actual-key point. -/
theorem fired_after_iff_hit (pk : PublicKeyCore core)
    (L : (j : TapeClass) → List (tapeClassRange core j))
    (hs : AnswerTape.HitInv (tapeClass core) L s)
    (hy : y ∈ support ((roleRunImpl core t).run s)) (index : Nat)
    (R : core.Y) (M : List Byte)
    (hc : s.2.1.cls (hmsgPoint core pk R M) = some TapeClass.forger)
    (hp : s.2.1.pos (hmsgPoint core pk R M) = some index) :
    Fired core pk y.2 index ↔ hmsgPoint core pk R M ∈ y.2.2.2 := by
  have keeps := AnswerTape.cls_pos_of_mem_support_classPosImplFwd_run
    (IsRandPoint core) (randRel core) (tapeClass core) (range_eq_tapeClassRange core) hs hy hc
  have after := AnswerTape.hitInv_of_mem_support_classPosImplFwd_run
    (IsRandPoint core) (randRel core) (tapeClass core) (range_eq_tapeClassRange core) hs hy
  constructor
  · rintro ⟨otherR, otherM, otherClass, otherPos, hit⟩
    have same := after.1.pos_inj (hmsgPoint core pk otherR otherM) (hmsgPoint core pk R M)
      TapeClass.forger index otherClass otherPos keeps.1 (keeps.2.trans hp)
    exact same ▸ hit
  · exact fun hit => ⟨R, M, keeps.1, keeps.2.trans hp, hit⟩

/-- An assigned unhit target whose nonce cell is cached remains unhit at an allowed query. -/
theorem not_fired_after_cached (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j))
    (hs : AnswerTape.HitInv (tapeClass core) L s)
    (hy : y ∈ support ((roleRunImpl core t).run s)) (index : Nat)
    (R : core.Y) (M : List Byte)
    (hc : s.2.1.cls (hmsgPoint core pk R M) = some TapeClass.forger)
    (hp : s.2.1.pos (hmsgPoint core pk R M) = some index)
    (cached : s.1.1 (.inr (.inr (kappa pk, M))) ≠ none)
    (notFired : ¬Fired core pk s index) (good : GoodQuery core pk kappa t) :
    ¬Fired core pk y.2 index := by
  have notHit : hmsgPoint core pk R M ∉ s.2.2 := fun hit =>
    notFired ⟨R, M, hc, hp, hit⟩
  rw [fired_after_iff_hit core pk L hs hy index R M hc hp]
  rw [hits_step core hy]
  rcases t with n | (point | point)
  · exact notHit
  · exact not_mem_freshHit_of_cached core pk kappa R M s.1.1 s.2.2 cached notHit point y.1 good
  · exact not_mem_freshHit_of_cached core pk kappa R M s.1.1 s.2.2 cached notHit point y.1 good

/-- Zero credit is absorbing at an assigned unhit point with a cached nonce cell. -/
theorem potential_after_cached_eq_zero (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j))
    (hs : AnswerTape.HitInv (tapeClass core) L s)
    (hy : y ∈ support ((roleRunImpl core t).run s)) (index : Nat)
    (R : core.Y) (M : List Byte)
    (hc : s.2.1.cls (hmsgPoint core pk R M) = some TapeClass.forger)
    (hp : s.2.1.pos (hmsgPoint core pk R M) = some index)
    (cached : s.1.1 (.inr (.inr (kappa pk, M))) ≠ none)
    (notFired : ¬Fired core pk s index) (good : GoodQuery core pk kappa t) :
    potential core pk kappa L index y.2 = 0 := by
  classical
  have keeps := AnswerTape.cls_pos_of_mem_support_classPosImplFwd_run
    (IsRandPoint core) (randRel core) (tapeClass core) (range_eq_tapeClassRange core) hs hy hc
  have after := AnswerTape.hitInv_of_mem_support_classPosImplFwd_run
    (IsRandPoint core) (randRel core) (tapeClass core) (range_eq_tapeClassRange core) hs hy
  have cacheMono := (AnswerTape.mono_of_mem_support_classPosImplFwd_run
    (IsRandPoint core) (randRel core) (tapeClass core) (range_eq_tapeClassRange core) t s y hy).1
  have cachedAfter : y.2.1.1 (.inr (.inr (kappa pk, M))) ≠ none := by
    cases old : s.1.1 (.inr (.inr (kappa pk, M))) with
    | none => exact (cached old).elim
    | some value =>
      have found := cacheMono old
      rw [found]
      exact Option.some_ne_none _
  have notFiredAfter := not_fired_after_cached core pk kappa L hs hy index R M hc hp cached
    notFired good
  have notLive := not_live_of_cached core pk kappa L after index R M keeps.1
    (keeps.2.trans hp) cachedAfter
  have slotAfter : ActualSlot core pk y.2 index := ⟨R, M, keeps.1, keeps.2.trans hp⟩
  simp [potential, after, notFiredAfter, notLive, slotAfter]

/-- Before any actual-key assignment, every step's terminal potential is at most its bank. -/
theorem potential_after_unassigned_le (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j))
    (hs : AnswerTape.HitInv (tapeClass core) L s)
    (hy : y ∈ support ((roleRunImpl core t).run s)) (index : Nat)
    (hslot : ¬ActualSlot core pk s index) :
    potential core pk kappa L index y.2 ≤ (Nat.card core.Y : ℝ≥0∞)⁻¹ := by
  classical
  have after := AnswerTape.hitInv_of_mem_support_classPosImplFwd_run
    (IsRandPoint core) (randRel core) (tapeClass core) (range_eq_tapeClassRange core) hs hy
  have notFired : ¬Fired core pk y.2 index := fun hf =>
    hslot (fired_preassigned core pk L hs hy hf)
  simp only [potential, after, ↓reduceIte, notFired]
  split_ifs <;> simp

/-- A fresh deterministic nonce query spends its live credit on a singleton outcome. -/
theorem fresh_candidate_pointwise (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j))
    {s : RoleState core} (hs : AnswerTape.HitInv (tapeClass core) L s)
    (index : Nat) (R : core.Y) (M : List Byte)
    (hc : s.2.1.cls (hmsgPoint core pk R M) = some TapeClass.forger)
    (hp : s.2.1.pos (hmsgPoint core pk R M) = some index)
    (fresh : s.1.1 (.inr (.inr (kappa pk, M))) = none)
    (notFired : ¬Fired core pk s index)
    (y : core.Y × RoleState core)
    (hy : y ∈ support ((roleRunImpl core (nonceQuery core pk kappa M)).run s)) :
    potential core pk kappa L index y.2 ≤ ({R} : Set core.Y).indicator (fun _ => 1) y.1 := by
  classical
  have keeps := AnswerTape.cls_pos_of_mem_support_classPosImplFwd_run
    (IsRandPoint core) (randRel core) (tapeClass core) (range_eq_tapeClassRange core) hs hy hc
  have after := AnswerTape.hitInv_of_mem_support_classPosImplFwd_run
    (IsRandPoint core) (randRel core) (tapeClass core) (range_eq_tapeClassRange core) hs hy
  have cachedAfter : y.2.1.1 (.inr (.inr (kappa pk, M))) ≠ none := by
    rw [(cache_cls_hits_of_mem_support_roleRunImpl_run_inr hy).1]
    exact Option.some_ne_none _
  have notLive := not_live_of_cached core pk kappa L after index R M keeps.1
    (keeps.2.trans hp) cachedAfter
  have slotAfter : ActualSlot core pk y.2 index := ⟨R, M, keeps.1, keeps.2.trans hp⟩
  have notHit : hmsgPoint core pk R M ∉ s.2.2 := fun hit =>
    notFired ⟨R, M, hc, hp, hit⟩
  have targetCached : s.1.1 (hmsgPoint core pk R M) ≠ none := by
    intro absent
    have incompatible := hs.1.cls_none _ absent
    rw [hc] at incompatible
    cases incompatible
  have hitEq := hits_step core hy
  change y.2.2.2 = AnswerTape.freshHitStep (IsRandPoint core) (randRel core)
    s.1.1 (.inr (.inr (kappa pk, M))) y.1 s.2.2 at hitEq
  rw [AnswerTape.freshHitStep_of_eq_none (IsRandPoint core) (randRel core) fresh (by trivial)]
    at hitEq
  have fires : Fired core pk y.2 index ↔ y.1 = R := by
    rw [fired_after_iff_hit core pk L hs hy index R M hc hp, hitEq]
    simp only [Set.mem_union, Set.mem_ofPred_eq, notHit, false_or]
    change (s.1.1 (hmsgPoint core pk R M) ≠ none ∧ (R = y.1 ∧ M = M)) ↔ y.1 = R
    constructor
    · exact fun h => h.2.1.symm
    · exact fun h => ⟨targetCached, h.symm, rfl⟩
  by_cases equal : y.1 = R
  · have fired := fires.mpr equal
    simp [potential, after, fired, equal]
  · have nofire : ¬Fired core pk y.2 index := fun fired => equal (fires.mp fired)
    simp [potential, after, nofire, notLive, slotAfter, equal]

omit [SampleableType (Bytes vp.params.m)] [DecidableEq core.Y] [DecidableEq core.PkSeed]
  [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf] in
/-- A returned uniform first coordinate pays for a singleton-valued potential. -/
theorem integral_le_singleton (mx : ProbComp (core.Y × RoleState core))
    (hmx : Prod.fst <$> mx = ($ᵗ core.Y : ProbComp core.Y))
    (value : RoleState core → ℝ≥0∞) (R : core.Y)
    (pointwise : ∀ y ∈ support mx,
      value y.2 ≤ ({R} : Set core.Y).indicator (fun _ => 1) y.1) :
    ∫⁻ r, r ∂𝒟[(fun y => value y.2) <$> mx] ≤ (Nat.card core.Y : ℝ≥0∞)⁻¹ := by
  classical
  let _ : MeasurableSpace core.Y := ⊤
  let _ : MeasurableSpace (core.Y × RoleState core) := ⊤
  calc
    ∫⁻ r, r ∂𝒟[(fun y => value y.2) <$> mx] ≤
        ∫⁻ r, r ∂𝒟[({R} : Set core.Y).indicator (fun _ => 1) <$> ($ᵗ core.Y : ProbComp _)] := by
      rw [← hmx, Functor.map_map, lintegral_id_evalDist_map, lintegral_id_evalDist_map]
      exact lintegral_mono_ae
        (evalDist.ae_of_forall_mem_support mx _ MeasurableSet.of_discrete pointwise)
    _ = (Nat.card core.Y : ℝ≥0∞)⁻¹ := by
      rw [lintegral_id_evalDist_map, lintegral_indicator_const MeasurableSet.of_discrete]
      simp only [one_mul]
      have singleton := SampleableType.prEvent_uniformSample_eq_singleton_natCard R
      rw [prEvent_eq_evalDist_of_discrete] at singleton
      simpa using singleton

/-- The live candidate's native nonce-query step has expected potential at most its bank. -/
theorem fresh_candidate_integral (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j)) (hL : L .other = [])
    {s : RoleState core} (hs : AnswerTape.HitInv (tapeClass core) L s)
    (index : Nat) (R : core.Y) (M : List Byte)
    (hc : s.2.1.cls (hmsgPoint core pk R M) = some TapeClass.forger)
    (hp : s.2.1.pos (hmsgPoint core pk R M) = some index)
    (fresh : s.1.1 (.inr (.inr (kappa pk, M))) = none)
    (notFired : ¬Fired core pk s index) :
    ∫⁻ r, r ∂𝒟[(fun y => potential core pk kappa L index y.2) <$>
      ((roleRunImpl core (nonceQuery core pk kappa M)).run s)] ≤
        (Nat.card core.Y : ℝ≥0∞)⁻¹ := by
  have currentEmpty : s.1.2 .other = [] := by
    have length := hs.1.length_add TapeClass.other
    rw [hL, List.length_nil] at length
    exact List.eq_nil_of_length_eq_zero (by omega)
  apply integral_le_singleton core _ ?_ (potential core pk kappa L index) R
    (fun y hy => fresh_candidate_pointwise core pk kappa L hs index R M hc hp fresh notFired y hy)
  rw [QueryImpl.extendState_apply]
  simp only [map_bind, map_pure, AnswerTape.tapeImplFwd, QueryImpl.add_apply_inr,
    AnswerTape.tapeCachingImplClass_apply_inr]
  change ((AnswerTape.tapeStep (spec := jointSpec core) (tapeClassRange core) TapeClass.other
    (.inr (.inr (kappa pk, M))) rfl).run (s.1.1, s.1.2) >>=
      pure ∘ Prod.fst) = ($ᵗ core.Y : ProbComp _)
  rw [← map_eq_bind_pure_comp]
  change Prod.fst <$>
    (AnswerTape.tapeStep (spec := jointSpec core) (tapeClassRange core) TapeClass.other
      (.inr (.inr (kappa pk, M))) rfl).run (s.1.1, s.1.2) = ($ᵗ core.Y : ProbComp _)
  rw [AnswerTape.tapeStep_run_nil fresh currentEmpty]
  simp only [Functor.map_map]
  change id <$> ($ᵗ core.Y : ProbComp _) = ($ᵗ core.Y : ProbComp _)
  exact id_map _

/-- A fresh hit of an assigned target identifies one of its two role-query copies. -/
theorem fired_requires_nonce (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j))
    (hs : AnswerTape.HitInv (tapeClass core) L s)
    (hy : y ∈ support ((roleRunImpl core t).run s)) (index : Nat)
    (R : core.Y) (M : List Byte)
    (hc : s.2.1.cls (hmsgPoint core pk R M) = some TapeClass.forger)
    (hp : s.2.1.pos (hmsgPoint core pk R M) = some index)
    (notFired : ¬Fired core pk s index) (good : GoodQuery core pk kappa t)
    (fired : Fired core pk y.2 index) :
    t = .inr (.inl (.inr (.inr (kappa pk, M)))) ∨
      t = nonceQuery core pk kappa M := by
  have notHit : hmsgPoint core pk R M ∉ s.2.2 := fun hit =>
    notFired ⟨R, M, hc, hp, hit⟩
  have hit := (fired_after_iff_hit core pk L hs hy index R M hc hp).mp fired
  rw [hits_step core hy] at hit
  rcases t with n | (point | point)
  · exact (notHit hit).elim
  · exact Or.inl (congrArg (fun x => Sum.inr (Sum.inl x))
      (freshHit_new_key core pk kappa R M s.1.1 s.2.2 notHit point y.1 good hit))
  · exact Or.inr (congrArg (fun x => Sum.inr (Sum.inr x))
      (freshHit_new_key core pk kappa R M s.1.1 s.2.2 notHit point y.1 good hit))

/-- Both role copies of a nonce point have the same native state transition. -/
theorem nonce_role_copies (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y) (M : List Byte) :
    roleRunImpl core (.inr (.inl (.inr (.inr (kappa pk, M))))) =
      roleRunImpl core (nonceQuery core pk kappa M) := by
  funext state
  change ((roleRunImpl core (.inr (.inl (.inr (.inr (kappa pk, M)))))).run state) =
    ((roleRunImpl core (nonceQuery core pk kappa M)).run state)
  simp only [roleRunImpl, AnswerTape.classPosImplFwd, QueryImpl.extendState_apply,
    AnswerTape.tapeImplFwd, QueryImpl.add_apply_inr,
    AnswerTape.tapeCachingImplClass_apply_inl, AnswerTape.tapeCachingImplClass_apply_inr,
    AnswerTape.classPosAuxFwd, AnswerTape.classPosAux_inl, AnswerTape.classPosAux_inr,
    AnswerTape.freshHitAux, tapeClass]
  rfl

/-- At every allowed native step the actual-key potential is a supermartingale. -/
theorem potential_step (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j)) (hL : L .other = [])
    (index : Nat) (t : (roleSpec core).Domain) (good : GoodQuery core pk kappa t)
    (s : RoleState core) :
    ∫⁻ r, r ∂𝒟[(fun y => potential core pk kappa L index y.2) <$>
      ((roleRunImpl core t).run s)] ≤ potential core pk kappa L index s := by
  classical
  by_cases hs : AnswerTape.HitInv (tapeClass core) L s
  swap
  · simp only [potential, hs, ↓reduceIte]
    exact le_top
  by_cases fired : Fired core pk s index
  · have eq : potential core pk kappa L index s = 1 := by
      simp only [potential, hs, fired, ↓reduceIte]
    rw [eq]
    apply lintegral_id_evalDist_map_le_of_le_of_mem_support
    intro y hy
    have after := AnswerTape.hitInv_of_mem_support_classPosImplFwd_run
      (IsRandPoint core) (randRel core) (tapeClass core) (range_eq_tapeClassRange core) hs hy
    have fire := fired_persists core pk L hs hy fired
    simp only [potential, after, fire, ↓reduceIte, le_refl]
  by_cases slot : ActualSlot core pk s index
  swap
  · have eq : potential core pk kappa L index s = (Nat.card core.Y : ℝ≥0∞)⁻¹ := by
      simp only [potential, hs, fired, slot, ↓reduceIte, not_false_eq_true, true_or]
    rw [eq]
    exact lintegral_id_evalDist_map_le_of_le_of_mem_support _
      (fun _ hy => potential_after_unassigned_le core pk kappa L hs hy index slot)
  obtain ⟨R, M, hc, hp⟩ := slot
  by_cases fresh : s.1.1 (.inr (.inr (kappa pk, M))) = none
  · have live : Live core pk kappa s index := ⟨R, M, hc, hp, fresh⟩
    have eq : potential core pk kappa L index s = (Nat.card core.Y : ℝ≥0∞)⁻¹ := by
      simp only [potential, hs, fired, live, ↓reduceIte, or_true]
    rw [eq]
    by_cases signer : t = nonceQuery core pk kappa M
    · subst t
      exact fresh_candidate_integral core pk kappa L hL hs index R M hc hp fresh fired
    by_cases forger : t = .inr (.inl (.inr (.inr (kappa pk, M))))
    · subst t
      rw [nonce_role_copies core pk kappa M]
      exact fresh_candidate_integral core pk kappa L hL hs index R M hc hp fresh fired
    apply lintegral_id_evalDist_map_le_of_le_of_mem_support
    intro y hy
    have after := AnswerTape.hitInv_of_mem_support_classPosImplFwd_run
      (IsRandPoint core) (randRel core) (tapeClass core) (range_eq_tapeClassRange core) hs hy
    have nofire : ¬Fired core pk y.2 index := by
      intro post
      exact (fired_requires_nonce core pk kappa L hs hy index R M hc hp fired good post).elim
        forger signer
    simp only [potential, after, nofire, ↓reduceIte]
    split_ifs <;> simp
  · have notLive := not_live_of_cached core pk kappa L hs index R M hc hp fresh
    have eq : potential core pk kappa L index s = 0 := by
      have slot : ActualSlot core pk s index := ⟨R, M, hc, hp⟩
      simp only [potential, hs, fired, slot, notLive, ↓reduceIte, not_true_eq_false, or_self]
    rw [eq]
    apply lintegral_id_evalDist_map_le_of_le_of_mem_support
    intro y hy
    rw [potential_after_cached_eq_zero core pk kappa L hs hy index R M hc hp fresh fired good]

/-- Zero disallowed-query budget composes the actual-key potential through a program. -/
theorem potential_run (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j)) (hL : L .other = [])
    (index : Nat) {α : Type} (program : OracleComp (roleSpec core) α)
    (allowed : program.AllQueriesSatisfy (GoodQuery core pk kappa))
    (s : RoleState core) :
    ∫⁻ r, r ∂𝒟[(fun y => potential core pk kappa L index y.2) <$>
      ((simulateQ (roleRunImpl core) program).run s)] ≤
        potential core pk kappa L index s := by
  classical
  have bound := (isQueryBoundP_zero_iff program (GoodQuery core pk kappa)).mpr allowed
  let credit : Nat → RoleState core → ℝ≥0∞ :=
    fun n state => if n = 0 then potential core pk kappa L index state else ⊤
  have monotone : ∀ state, Monotone fun n => credit n state := by
    intro state a b hab
    by_cases hb : b = 0
    · have ha : a = 0 := Nat.eq_zero_of_le_zero (hb ▸ hab)
      simp only [credit, ha, hb, ↓reduceIte, le_refl]
    · simp only [credit, hb, ↓reduceIte]
      exact le_top
  have step : ∀ t state n,
      ∫⁻ r, r ∂𝒟[(fun z => credit n z.2) <$> ((roleRunImpl core t).run state)] ≤
        credit (n + if ¬GoodQuery core pk kappa t then 1 else 0) state := by
    intro t state n
    by_cases hn : n = 0
    · subst n
      by_cases hg : GoodQuery core pk kappa t
      · simpa only [credit, hg, not_true_eq_false, ↓reduceIte, Nat.add_zero] using
          potential_step core pk kappa L hL index t hg state
      · simp only [credit, hg, not_false_eq_true, ↓reduceIte, Nat.zero_add, Nat.one_ne_zero]
        exact le_top
    · have positive : n + (if ¬GoodQuery core pk kappa t then 1 else 0) ≠ 0 := by omega
      simp only [credit, positive, ↓reduceIte]
      exact le_top
  simpa only [credit, ↓reduceIte] using
    (lintegral_run_le_of_isQueryBoundP (roleRunImpl core)
      (fun t => ¬GoodQuery core pk kappa t) credit monotone step program 0 bound s)

end Step

end SLHDSA.Security.Coverage.ActualKeyPotential
/-! ## Two designated actual-key slot credits -/

open OracleComp OracleSpec SignatureAlg MeasureTheory
open scoped ENNReal

namespace SLHDSA.Security.Coverage.ActualKeyPotential.Pair
open ActualKeyPotential
variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-- An assigned live watch whose fresh deterministic nonce cell is the current query. -/
private def ActiveCandidate (pk : PublicKeyCore core) (kappa : PublicKeyCore core → core.Y)
    (s : RoleState core) (index : Nat) (t : (roleSpec core).Domain) : Prop :=
  ∃ R M,
    s.2.1.cls (hmsgPoint core pk R M) = some TapeClass.forger ∧
    s.2.1.pos (hmsgPoint core pk R M) = some index ∧
    ¬Fired core pk s index ∧ s.1.1 (.inr (.inr (kappa pk, M))) = none ∧
    (t = .inr (.inl (.inr (.inr (kappa pk, M)))) ∨ t = nonceQuery core pk kappa M)

/-- The two native slot watches share their actual-key product potential. -/
noncomputable def productPotential (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j)) (first second : Nat)
    (s : RoleState core) : ℝ≥0∞ :=
  potential core pk kappa L first s * potential core pk kappa L second s

variable [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.Y]
  [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]
  {t : (roleSpec core).Domain} {s : RoleState core}
  {y : (roleSpec core).Range t × RoleState core}

/-- Outside its active fresh nonce query a watch cannot increase pointwise. -/
private theorem potential_after_not_active_le (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j)) (index : Nat)
    (good : GoodQuery core pk kappa t)
    (inactive : ¬ActiveCandidate core pk kappa s index t)
    (hy : y ∈ support ((roleRunImpl core t).run s)) :
    potential core pk kappa L index y.2 ≤ potential core pk kappa L index s := by
  classical
  by_cases hs : AnswerTape.HitInv (tapeClass core) L s
  swap
  · have eq : potential core pk kappa L index s = ⊤ := by
      simp only [potential, hs, ↓reduceIte]
    rw [eq]
    exact le_top
  have after := AnswerTape.hitInv_of_mem_support_classPosImplFwd_run
    (IsRandPoint core) (randRel core) (tapeClass core) (range_eq_tapeClassRange core) hs hy
  by_cases fired : Fired core pk s index
  · have fire := fired_persists core pk L hs hy fired
    simp only [potential, hs, after, fired, fire, ↓reduceIte, le_refl]
  by_cases slot : ActualSlot core pk s index
  swap
  · have eq : potential core pk kappa L index s = (Nat.card core.Y : ℝ≥0∞)⁻¹ := by
      simp only [potential, hs, fired, slot, ↓reduceIte, not_false_eq_true, true_or]
    rw [eq]
    exact potential_after_unassigned_le core pk kappa L hs hy index slot
  obtain ⟨R, M, hc, hp⟩ := slot
  by_cases fresh : s.1.1 (.inr (.inr (kappa pk, M))) = none
  · have live : Live core pk kappa s index := ⟨R, M, hc, hp, fresh⟩
    have nofire : ¬Fired core pk y.2 index := by
      intro post
      exact inactive ⟨R, M, hc, hp, fired, fresh,
        fired_requires_nonce core pk kappa L hs hy index R M hc hp fired good post⟩
    have eq : potential core pk kappa L index s = (Nat.card core.Y : ℝ≥0∞)⁻¹ := by
      simp only [potential, hs, fired, live, ↓reduceIte, or_true]
    rw [eq]
    simp only [potential, after, nofire, ↓reduceIte]
    split_ifs <;> simp
  · have notLive := not_live_of_cached core pk kappa L hs index R M hc hp fresh
    have eq : potential core pk kappa L index s = 0 := by
      have slot : ActualSlot core pk s index := ⟨R, M, hc, hp⟩
      simp only [potential, hs, fired, slot, notLive, ↓reduceIte, not_true_eq_false, or_self]
    rw [eq, potential_after_cached_eq_zero core pk kappa L hs hy index R M hc hp
      fresh fired good]

/-- Distinct actual-key slots sharing a fresh nonce query have disjoint firing outcomes. -/
private theorem shared_fresh_candidate_zero (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j))
    (hs : AnswerTape.HitInv (tapeClass core) L s)
    (first second : Nat) (hne : first ≠ second) (leftR rightR : core.Y) (M : List Byte)
    (leftClass : s.2.1.cls (hmsgPoint core pk leftR M) = some TapeClass.forger)
    (leftPos : s.2.1.pos (hmsgPoint core pk leftR M) = some first)
    (rightClass : s.2.1.cls (hmsgPoint core pk rightR M) = some TapeClass.forger)
    (rightPos : s.2.1.pos (hmsgPoint core pk rightR M) = some second)
    (fresh : s.1.1 (.inr (.inr (kappa pk, M))) = none)
    (leftNotFired : ¬Fired core pk s first) (rightNotFired : ¬Fired core pk s second)
    (z : core.Y × RoleState core)
    (hz : z ∈ support ((roleRunImpl core (nonceQuery core pk kappa M)).run s)) :
    productPotential core pk kappa L first second z.2 = 0 := by
  classical
  have different : leftR ≠ rightR := by
    rintro rfl
    exact hne (Option.some.inj (leftPos.symm.trans rightPos))
  have leftBound := fresh_candidate_pointwise core pk kappa L hs first leftR M
    leftClass leftPos fresh leftNotFired z hz
  have rightBound := fresh_candidate_pointwise core pk kappa L hs second rightR M
    rightClass rightPos fresh rightNotFired z hz
  apply le_zero_iff.mp
  change potential core pk kappa L first z.2 * potential core pk kappa L second z.2 ≤ 0
  have bound := mul_le_mul' leftBound rightBound
  have zero : ({leftR} : Set core.Y).indicator (fun _ => (1 : ℝ≥0∞)) z.1 *
      ({rightR} : Set core.Y).indicator (fun _ => (1 : ℝ≥0∞)) z.1 = 0 := by
    by_cases h : z.1 = leftR
    · simp [h, different]
    · simp [h]
  exact bound.trans_eq zero

/-- A pointwise nonactive factor can be taken outside the other watch's expected step. -/
private theorem product_step_of_not_active (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j)) (hL : L .other = [])
    (first second : Nat) (t : (roleSpec core).Domain) (s : RoleState core)
    (good : GoodQuery core pk kappa t)
    (inactive : ¬ActiveCandidate core pk kappa s first t) :
    ∫⁻ r, r ∂𝒟[(fun z => productPotential core pk kappa L first second z.2) <$>
      ((roleRunImpl core t).run s)] ≤ productPotential core pk kappa L first second s := by
  let _ : MeasurableSpace ((roleSpec core).Range t × RoleState core) := ⊤
  calc
    _ ≤ ∫⁻ r, r ∂𝒟[(fun z => potential core pk kappa L first s *
        potential core pk kappa L second z.2) <$> ((roleRunImpl core t).run s)] :=
      by
        rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map]
        apply lintegral_mono_ae
        exact evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete fun z hz =>
          mul_le_mul' (potential_after_not_active_le core pk kappa L first good inactive hz) le_rfl
    _ = potential core pk kappa L first s *
        (∫⁻ r, r ∂𝒟[(fun z => potential core pk kappa L second z.2) <$>
          ((roleRunImpl core t).run s)]) := by
      rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map,
        lintegral_const_mul _ Measurable.of_discrete]
    _ ≤ productPotential core pk kappa L first second s :=
      mul_le_mul' le_rfl (potential_step core pk kappa L hL second t good s)

/-- The product watch is a native supermartingale at distinct actual-key slots. -/
private theorem product_potential_step (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j)) (hL : L .other = [])
    (first second : Nat) (hne : first ≠ second)
    (t : (roleSpec core).Domain) (good : GoodQuery core pk kappa t) (s : RoleState core) :
    ∫⁻ r, r ∂𝒟[(fun z => productPotential core pk kappa L first second z.2) <$>
      ((roleRunImpl core t).run s)] ≤ productPotential core pk kappa L first second s := by
  classical
  by_cases hs : AnswerTape.HitInv (tapeClass core) L s
  swap
  · have eq : productPotential core pk kappa L first second s = ⊤ := by
      simp only [productPotential, potential, hs, ↓reduceIte, ENNReal.top_mul_top]
    rw [eq]
    exact le_top
  by_cases leftActive : ActiveCandidate core pk kappa s first t
  swap
  · exact product_step_of_not_active core pk kappa L hL first second t s good leftActive
  by_cases rightActive : ActiveCandidate core pk kappa s second t
  swap
  · simpa only [productPotential, mul_comm] using
      product_step_of_not_active core pk kappa L hL second first t s good rightActive
  obtain ⟨leftR, leftM, leftClass, leftPos, leftNotFired, fresh, leftQuery⟩ := leftActive
  obtain ⟨rightR, rightM, rightClass, rightPos, rightNotFired, _, rightQuery⟩ := rightActive
  have sameMessage : leftM = rightM := by
    rcases leftQuery with leftQuery | leftQuery <;>
      rcases rightQuery with rightQuery | rightQuery
    · exact (Prod.mk.inj (Sum.inr.inj (Sum.inr.inj
        (Sum.inl.inj (Sum.inr.inj (leftQuery.symm.trans rightQuery)))))).2
    · cases leftQuery.symm.trans rightQuery
    · cases leftQuery.symm.trans rightQuery
    · exact (Prod.mk.inj (Sum.inr.inj (Sum.inr.inj
        (Sum.inr.inj (Sum.inr.inj (leftQuery.symm.trans rightQuery)))))).2
  subst rightM
  have zeroStep : ∫⁻ r, r ∂𝒟[(fun z => productPotential core pk kappa L first second z.2) <$>
      ((roleRunImpl core (nonceQuery core pk kappa leftM)).run s)] ≤ 0 :=
    lintegral_id_evalDist_map_le_of_le_of_mem_support _ fun z hz =>
      (shared_fresh_candidate_zero core pk kappa L hs first second hne leftR rightR leftM
        leftClass leftPos rightClass rightPos fresh leftNotFired rightNotFired z hz).le
  rcases leftQuery with rfl | rfl
  · rw [nonce_role_copies core pk kappa leftM]
    exact zeroStep.trans zero_le
  · exact zeroStep.trans zero_le

end SLHDSA.Security.Coverage.ActualKeyPotential.Pair

namespace SLHDSA.Security.Coverage.ActualKeyPotential.Pair
open ActualKeyPotential
variable {vp : ValidatedParams} (core : CorePrimitives vp.params)

/-- Terminal credit for both hits and for an unreached first position. -/
noncomputable def pairTerminalValue (pk : PublicKeyCore core) (first second : Nat)
    (s : RoleState core) : ℝ≥0∞ := by
  classical
  exact (if Fired core pk s first ∧ Fired core pk s second then (1 : ℝ≥0∞) else 0) +
    (if ¬first < s.2.1.cnt TapeClass.forger then ((Nat.card core.Y : ℝ≥0∞)⁻¹)^2 else 0)

/-- The product watch pays for simultaneous hits and unused first-position credit. -/
theorem pair_terminal_credit (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j))
    (first second : Nat) (horder : first < second) (s : RoleState core) :
    pairTerminalValue core pk first second s ≤
      productPotential core pk kappa L first second s := by
  classical
  by_cases hs : AnswerTape.HitInv (tapeClass core) L s
  swap
  · simp only [productPotential, potential, hs, ↓reduceIte, ENNReal.top_mul_top, le_top]
  by_cases both : Fired core pk s first ∧ Fired core pk s second
  · have reach := fired_reached core pk L hs both.1
    simp [pairTerminalValue, productPotential, potential, hs, both.1, both.2, reach]
  by_cases reach : first < s.2.1.cnt TapeClass.forger
  · simp only [pairTerminalValue, both, reach, not_true_eq_false, ↓reduceIte, zero_add]
    exact zero_le
  · have noFirst : ¬ActualSlot core pk s first := fun slot =>
      reach (actualSlot_reached core pk L hs slot)
    have noSecond : ¬ActualSlot core pk s second := fun slot =>
      reach (horder.trans (actualSlot_reached core pk L hs slot))
    have notFirstFired : ¬Fired core pk s first := by
      rintro ⟨R, M, hc, hp, _⟩
      exact noFirst ⟨R, M, hc, hp⟩
    have notSecondFired : ¬Fired core pk s second := by
      rintro ⟨R, M, hc, hp, _⟩
      exact noSecond ⟨R, M, hc, hp⟩
    simp [pairTerminalValue, reach, productPotential, potential, hs, notFirstFired,
      notSecondFired, noFirst, noSecond, pow_two]

variable [SampleableType core.Y] [SampleableType (Bytes vp.params.m)] [DecidableEq core.Y]
  [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]

/-- Zero disallowed-query budget composes the product potential through a program. -/
theorem product_potential_run (pk : PublicKeyCore core)
    (kappa : PublicKeyCore core → core.Y)
    (L : (j : TapeClass) → List (tapeClassRange core j)) (hL : L .other = [])
    (first second : Nat) (hne : first ≠ second) {α : Type} (program : OracleComp (roleSpec core) α)
    (allowed : program.AllQueriesSatisfy (GoodQuery core pk kappa))
    (s : RoleState core) :
    ∫⁻ r, r ∂𝒟[(fun y => productPotential core pk kappa L first second y.2) <$>
      ((simulateQ (roleRunImpl core) program).run s)] ≤
        productPotential core pk kappa L first second s := by
  classical
  have bound := (isQueryBoundP_zero_iff program (GoodQuery core pk kappa)).mpr allowed
  let credit : Nat → RoleState core → ℝ≥0∞ :=
    fun n state => if n = 0 then productPotential core pk kappa L first second state else ⊤
  have monotone : ∀ state, Monotone fun n => credit n state := by
    intro state a b hab
    by_cases hb : b = 0
    · have ha : a = 0 := Nat.eq_zero_of_le_zero (hb ▸ hab)
      simp only [credit, ha, hb, ↓reduceIte, le_refl]
    · simp only [credit, hb, ↓reduceIte]
      exact le_top
  have step : ∀ t state n,
      ∫⁻ r, r ∂𝒟[(fun z => credit n z.2) <$> ((roleRunImpl core t).run state)] ≤
        credit (n + if ¬GoodQuery core pk kappa t then 1 else 0) state := by
    intro t state n
    by_cases hn : n = 0
    · subst n
      by_cases hg : GoodQuery core pk kappa t
      · simpa only [credit, hg, not_true_eq_false, ↓reduceIte, Nat.add_zero] using
          product_potential_step core pk kappa L hL first second hne t hg state
      · simp only [credit, hg, not_false_eq_true, ↓reduceIte, Nat.zero_add, Nat.one_ne_zero]
        exact le_top
    · have positive : n + (if ¬GoodQuery core pk kappa t then 1 else 0) ≠ 0 := by omega
      simp only [credit, positive, ↓reduceIte]
      exact le_top
  simpa only [credit, ↓reduceIte] using
    (lintegral_run_le_of_isQueryBoundP (roleRunImpl core)
      (fun t => ¬GoodQuery core pk kappa t) credit monotone step program 0 bound s)

end SLHDSA.Security.Coverage.ActualKeyPotential.Pair
namespace SLHDSA.Security.Coverage.ActualKeyPotential

variable {vp : ValidatedParams} (core : CorePrimitives vp.params)
variable [SampleableType core.Y] [SampleableType (Bytes vp.params.m)]
  [DecidableEq core.Y] [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey]
  [DecidableEq core.SkPrf]

/-- An allowed program's terminal single-slot credit is funded by its starting potential. -/
theorem allowed_program_terminal_credit
    {α : Type} (pk : PublicKeyCore core) (kappa : PublicKeyCore core → core.Y)
    (family : (j : TapeClass) → List (tapeClassRange core j)) (otherEmpty : family .other = [])
    (index : Nat) (program : OracleComp (roleSpec core) α)
    (allowed : program.AllQueriesSatisfy (GoodQuery core pk kappa)) (initial : RoleState core) :
    ∫⁻ value, value ∂𝒟[(fun outcome => terminalValue core pk index outcome.2) <$>
      (simulateQ (roleRunImpl core) program).run initial] ≤
        potential core pk kappa family index initial := by
  exact (lintegral_id_evalDist_map_mono
    ((simulateQ (roleRunImpl core) program).run initial) (fun (outcome : α × RoleState core) =>
      terminal_credit core pk kappa family index outcome.2)).trans
    (potential_run core pk kappa family otherEmpty index program allowed initial)

/-- An allowed program's pair credit retains shared-nonce dependence in one product potential. -/
theorem Pair.allowed_program_pair_terminal_credit
    {α : Type} (pk : PublicKeyCore core) (kappa : PublicKeyCore core → core.Y)
    (family : (j : TapeClass) → List (tapeClassRange core j)) (otherEmpty : family .other = [])
    (first second : Nat) (order : first < second) (program : OracleComp (roleSpec core) α)
    (allowed : program.AllQueriesSatisfy (GoodQuery core pk kappa)) (initial : RoleState core) :
    ∫⁻ value, value ∂𝒟[(fun outcome => Pair.pairTerminalValue core pk first second outcome.2) <$>
      (simulateQ (roleRunImpl core) program).run initial] ≤
        Pair.productPotential core pk kappa family first second initial := by
  exact (lintegral_id_evalDist_map_mono
    ((simulateQ (roleRunImpl core) program).run initial) (fun (outcome : α × RoleState core) =>
      Pair.pair_terminal_credit core pk kappa family first second order outcome.2)).trans
    (Pair.product_potential_run core pk kappa family otherEmpty first second
      (Nat.ne_of_lt order) program allowed initial)

end SLHDSA.Security.Coverage.ActualKeyPotential
