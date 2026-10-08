/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.OracleComp.QueryTracking.RandomOracle.ClassIndexedTape
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# Positions on a class-indexed tape run

`ClassIndexedTape.lean` identifies the shared lazy random oracle with the class-indexed tape
oracle averaged over a bundled tape family. That identification ties no answer to a class. This
file ties them, by instrumenting the tape run, and transports bounds on tape events to the lazy
run.

`classPosAux` instruments a run with the class and position each cache entry was answered at,
the entries consumed from each tape, and the queries made at each class. `ClassPosInv` is the
invariant its run maintains, and `ClassPosInv.exists_pos` is the consequence a caller wants:
under *per-class* query bounds on a set `T` of classes, every cache entry of a class in `T` is
the value of its class's tape at a position of that tape, and distinct entries sit at distinct
class-position pairs. Per-class bounds are what the split forces: the total-cache-size device
of `Tape.lean` does not survive it, since one class exhausting its tape is consistent with the
other classes' entries making up the total. Classes outside `T` need no bound at all.

The invariant also *pins the class*: `ClassPosInv.cls_tau` records that a point's class is the
class of one of its two call sites, so the existence lemma returns `j = τ (.inl t) ∨ j = τ
(.inr t)` alongside the position. Without it `j` is unconstrained, the caller cannot say which
tape an entry came off, and — since the class also determines the answer type — cannot even
convert the tape value to the type of the cache entry. The lemma therefore also returns that
type equality, and states the entry in cast form rather than as a bare `HEq`.

## Runs

* `exists_pos_of_mem_support_run_tapeCachingImplClass` reads `ClassPosInv.exists_pos` off a run
  over the duplicated interface `spec + spec`.
* A program that samples privately runs over `unifSpec + (spec + spec)`, under
  `dupRandomOracleFwd` lazily and under `tapeImplFwd` on tapes. `classPosImplFwd` instruments
  the forwarded tape run with the same bookkeeping, through `classPosAuxFwd`, which records
  nothing at a private query, beside a passive state `Q` of the caller's own.
  `classPosInvAuxFwd_step` is its one-step preservation of `ClassPosInv`, and
  `exists_pos_of_mem_support_run_classPosImplFwd` reads `ClassPosInv.exists_pos` off its runs.
* `cnt_le_of_isQueryBoundP` discharges the per-class bounds: a bound on the queries of class
  `j` the program makes, stated through `classOf`, bounds the class's query counter on every
  instrumented forwarded run.
* `prEvent_run_dupRandomOracleFwd_le_sum` is the transport, in bind form. If every lazy-run
  event `P` is witnessed on the instrumented run by some `w` in a finite set, with a tape event
  `M w` of the family and a run event `H w` of mass at most `β w` on every family, then `P` has
  mass at most `∑ w, Pr_tape[M w] * β w`. A program over `spec + spec` alone enters it through
  `OracleComp.liftComp`, which `QueryImpl.simulateQ_add_liftComp_right` removes on the lazy
  side.

## Hits at fresh draws

`freshHitAux` is a passive state `Q` for `classPosImplFwd`: a hit set of points, written by
`freshHitStep` only at a fresh draw at a point satisfying `trig`, with the points cached before
that draw that its answer relates to under `rel`. A cache hit writes nothing, so a repeated query
cannot record a hit that no fresh answer paid for.

Lemmas suffixed `_classPosImplFwd_run` are about one step, `(classPosImplFwd … t).run s`; lemmas
suffixed `_run_classPosImplFwd` are about a run of a whole program under `simulateQ`.

* `hits_eq_self_of_mem_support_classPosImplFwd_run`: a step that is not such a draw leaves the
  hit set unchanged, and `freshHitStep_of_eq_none` gives the hit set after one that is.
* `ne_none_of_mem_hits_of_mem_support_classPosImplFwd_run`: a step keeps every hit cached, and
  `ne_none_of_mem_hits_of_mem_support_run_classPosImplFwd` carries that along a run.
* `mono_of_mem_support_classPosImplFwd_run`: a step only extends the cache, keeps the class and
  position of every point cached before it, and only grows the hit set, by points cached before
  it. `mono_of_mem_support_run_classPosImplFwd_freshHitAux` carries the first three along a
  run.

## Scope

* Nothing here bounds the mass of any tape event: that is `IndepProductEvents.lean`, reached
  through `evalDist_tapeFamily_setOf_eq` and `evalDist_tapeFamily_setOf_eq₂`.
* The position lemmas start from the empty cache and the empty bookkeeping.
* The transport quantifies over the families the draw can produce, so
  `length_of_mem_support_tapeFamily` identifies the lengths of the family a hypothesis is handed
  with the lengths `m` it was drawn at.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace AnswerTape

variable {ι J : Type} {spec : OracleSpec.{0, 0} ι} [DecidableEq ι]
  [Fintype J] [DecidableEq J] {R : J → Type} [∀ j, SampleableType (R j)]

/-! ## The position instrumentation -/

section Position

/-- The auxiliary state of the instrumented class-indexed tape run: the tape class at which
each point was freshly answered, its position on that tape when the answer came off the tape,
the number of entries consumed from each tape, and the number of queries made at each class. -/
structure ClassPos (D J : Type) where
  /-- The tape class at which the point was freshly answered. -/
  cls : D → Option J
  /-- The position on that class's tape, absent for an answer sampled after it ran out. -/
  pos : D → Option ℕ
  /-- Entries consumed from each class's tape. -/
  next : J → ℕ
  /-- Queries made at each class. -/
  cnt : J → ℕ

/-- The bookkeeping of a run that has made no query: no point has a class or a position, and
every counter is zero. -/
@[expose, simps]
def ClassPos.init {D J : Type} : ClassPos D J :=
  ⟨fun _ => none, fun _ => none, fun _ => 0, fun _ => 0⟩

variable [∀ t : spec.Domain, SampleableType (spec.Range t)]
  {τ : (spec + spec).Domain → J}
  {hR : ∀ t : (spec + spec).Domain, (spec + spec).Range t = R (τ t)}

/-- The bookkeeping of one `tapeStep` at a point `t` of class `j`: a query answered off the
tape records its class and position and advances that tape's counter, a query answered after
the tape ran out records only its class, a cache hit records nothing, and every query
increments its class's query counter. -/
def classPosStep (R : J → Type) (j : J) (t : spec.Domain) :
    (spec.QueryCache × ((k : J) → List (R k))) → spec.Range t →
      (spec.QueryCache × ((k : J) → List (R k))) → ClassPos spec.Domain J →
      ClassPos spec.Domain J :=
  fun s _ _ p =>
    match s.1 t, s.2 j with
    | none, _ :: _ =>
        ⟨Function.update p.cls t (some j), Function.update p.pos t (some (p.next j)),
          Function.update p.next j (p.next j + 1), Function.update p.cnt j (p.cnt j + 1)⟩
    | none, [] =>
        ⟨Function.update p.cls t (some j), p.pos, p.next,
          Function.update p.cnt j (p.cnt j + 1)⟩
    | some _, _ => ⟨p.cls, p.pos, p.next, Function.update p.cnt j (p.cnt j + 1)⟩

/-- The bookkeeping of one step of the class-indexed tape oracle. -/
def classPosAux (R : J → Type) (τ : (spec + spec).Domain → J) :
    (t : (spec + spec).Domain) → (spec.QueryCache × ((k : J) → List (R k))) →
      (spec + spec).Range t → (spec.QueryCache × ((k : J) → List (R k))) →
      ClassPos spec.Domain J → ClassPos spec.Domain J
  | .inl t => classPosStep R (τ (Sum.inl t)) t
  | .inr t => classPosStep R (τ (Sum.inr t)) t

/-- The invariant maintained by the position instrumentation of a class-indexed tape run on
the tape family `Lfam`, relating the answer cache `c`, the unconsumed tapes `l`, and the four
components of the bookkeeping. -/
structure ClassPosInv (τ : (spec + spec).Domain → J) (Lfam : (k : J) → List (R k))
    (c : spec.QueryCache)
    (l : (k : J) → List (R k)) (cls : spec.Domain → Option J) (pos : spec.Domain → Option ℕ)
    (next cnt : J → ℕ) : Prop where
  /-- A recorded position has been consumed on its own class's tape, and the cache entry there
  is that tape's value at that position. -/
  pos_spec : ∀ t j n, cls t = some j → pos t = some n → n < next j ∧ HEq (c t) ((Lfam j)[n]?)
  /-- Distinct cached points record distinct class-position pairs. -/
  pos_inj : ∀ t t' j n, cls t = some j → pos t = some n → cls t' = some j → pos t' = some n →
    t = t'
  /-- The consumed and unconsumed parts exhaust each tape. -/
  length_add : ∀ j, (l j).length + next j = (Lfam j).length
  /-- The unconsumed part of each tape is its tail from that tape's current position. -/
  getElem?_eq : ∀ j i, (l j)[i]? = (Lfam j)[next j + i]?
  /-- No more entries have been consumed from a tape than queries made at its class. -/
  next_le_cnt : ∀ j, next j ≤ cnt j
  /-- Every cached point was freshly answered at some class. -/
  cls_ne_none : ∀ t, c t ≠ none → cls t ≠ none
  /-- Only a cached point carries a class. -/
  cls_none : ∀ t, c t = none → cls t = none
  /-- Only a point with a class carries a position. -/
  pos_none : ∀ t, cls t = none → pos t = none
  /-- A cached point without a position was answered after its class's tape ran out, which
  costs that class a query beyond the ones that consumed the tape. -/
  fallback : ∀ t j, c t ≠ none → cls t = some j → pos t = none → l j = [] ∧ next j < cnt j
  /-- A point's class is the class of one of its two call sites. This is what lets a caller
  identify the tape a cache entry came off, and with it the type of that entry. -/
  cls_tau : ∀ t, cls t ≠ none → cls t = some (τ (Sum.inl t)) ∨ cls t = some (τ (Sum.inr t))

namespace ClassPosInv

omit [DecidableEq ι] [Fintype J] [DecidableEq J] [∀ j, SampleableType (R j)]
  [∀ t : spec.Domain, SampleableType (spec.Range t)] in
/-- The empty cache with every tape unconsumed and no queries made satisfies the invariant. -/
theorem empty (τ : (spec + spec).Domain → J) (Lfam : (k : J) → List (R k)) :
    ClassPosInv τ Lfam (∅ : spec.QueryCache) Lfam (fun _ => none) (fun _ => none)
      (fun _ => 0) (fun _ => 0) where
  pos_spec _ _ _ h := absurd h (by simp)
  pos_inj _ _ _ _ h := absurd h (by simp)
  length_add _ := by simp
  getElem?_eq _ _ := by simp
  next_le_cnt _ := le_rfl
  cls_ne_none t h := absurd (QueryCache.empty_apply t) h
  cls_none _ _ := rfl
  pos_none _ _ := rfl
  fallback t _ h := absurd (QueryCache.empty_apply t) h
  cls_tau _ h := absurd rfl h

end ClassPosInv

omit [DecidableEq ι] [Fintype J] [DecidableEq J] [∀ j, SampleableType (R j)]
  [∀ t : spec.Domain, SampleableType (spec.Range t)] in
private theorem heq_some_cast {A B : Type} (h : A = B) (u : B) :
    HEq (some (cast h.symm u)) (some u) := by
  subst h; rfl

omit [DecidableEq ι] [Fintype J] [DecidableEq J] [∀ j, SampleableType (R j)]
  [∀ t : spec.Domain, SampleableType (spec.Range t)] in
private theorem eq_some_cast_of_heq {A B : Type} (h : A = B) {a : A} {o : Option B}
    (hh : HEq (some a) o) : o = some (cast h a) := by
  subst h
  simpa using (eq_of_heq hh).symm

variable {j : J} {t : spec.Domain} {c : spec.QueryCache} {L : (k : J) → List (R k)}
  {x : spec.Range t} {s' : spec.QueryCache × ((k : J) → List (R k))}
  {p : ClassPos spec.Domain J}

omit [Fintype J] [∀ j, SampleableType (R j)]
  [∀ t : spec.Domain, SampleableType (spec.Range t)] in
/-- A cache hit records only the query at its class. -/
theorem classPosStep_of_some {u₀ : spec.Range t} (hc : c t = some u₀) :
    classPosStep R j t (c, L) x s' p =
      ⟨p.cls, p.pos, p.next, Function.update p.cnt j (p.cnt j + 1)⟩ := by
  simp [classPosStep, hc]

omit [Fintype J] [∀ j, SampleableType (R j)]
  [∀ t : spec.Domain, SampleableType (spec.Range t)] in
/-- An answer sampled after the class's tape ran out records only its class. -/
theorem classPosStep_of_nil (hc : c t = none) (hL : L j = []) :
    classPosStep R j t (c, L) x s' p =
      ⟨Function.update p.cls t (some j), p.pos, p.next,
        Function.update p.cnt j (p.cnt j + 1)⟩ := by
  simp [classPosStep, hc, hL]

omit [Fintype J] [∀ j, SampleableType (R j)]
  [∀ t : spec.Domain, SampleableType (spec.Range t)] in
/-- An answer taken off the tape records its class and position and advances that tape. -/
theorem classPosStep_of_cons {u : R j} {l : List (R j)} (hc : c t = none)
    (hL : L j = u :: l) :
    classPosStep R j t (c, L) x s' p =
      ⟨Function.update p.cls t (some j), Function.update p.pos t (some (p.next j)),
        Function.update p.next j (p.next j + 1), Function.update p.cnt j (p.cnt j + 1)⟩ := by
  simp [classPosStep, hc, hL]

omit [Fintype J] [∀ j, SampleableType (R j)] in
/-- Every step of the instrumented class-indexed tape oracle preserves `ClassPosInv`. -/
private theorem classPosInv_step (Lfam : (k : J) → List (R k)) (h : spec.Range t = R j)
    (hjt : j = τ (Sum.inl t) ∨ j = τ (Sum.inr t))
    (hs : ClassPosInv τ Lfam c L p.cls p.pos p.next p.cnt)
    (y : spec.Range t × (spec.QueryCache × ((k : J) → List (R k))) × ClassPos spec.Domain J)
    (hy : y ∈ support ((tapeStep R j t h).run (c, L) >>= fun w =>
      pure (w.1, (w.2, classPosStep R j t (c, L) w.1 w.2 p)))) :
    ClassPosInv τ Lfam y.2.1.1 y.2.1.2 y.2.2.cls y.2.2.pos y.2.2.next y.2.2.cnt := by
  rw [mem_support_bind_iff] at hy
  obtain ⟨w, hw, hy⟩ := hy
  rw [support_pure, Set.mem_singleton_iff] at hy
  subst hy
  rcases hc : c t with _ | u₀
  · rcases hL : L j with _ | ⟨u, l⟩
    · rw [tapeStep_run_nil hc hL, support_map, support_uniformSample, Set.image_univ] at hw
      obtain ⟨u, hu⟩ := hw
      subst hu
      rw [classPosStep_of_nil hc hL]
      dsimp only
      have hpt : p.cls t = none := hs.cls_none t hc
      have hpp : p.pos t = none := hs.pos_none t hpt
      refine ⟨fun t' j' n hcl hps => ?_, fun t₁ t₂ j' n h₁ h₂ h₃ h₄ => ?_, hs.length_add,
        hs.getElem?_eq, fun j' => ?_, fun t' ht' => ?_, fun t' ht' => ?_, fun t' ht' => ?_,
        fun t' j' ht' hcl hps => ?_, fun t' ht' => ?_⟩
      · rcases eq_or_ne t' t with rfl | hne
        · rw [hpp] at hps; exact absurd hps (by simp)
        · rw [Function.update_of_ne hne] at hcl
          exact ⟨(hs.pos_spec t' j' n hcl hps).1,
            (QueryCache.cacheQuery_of_ne c u hne) ▸ (hs.pos_spec t' j' n hcl hps).2⟩
      · have hne : ∀ t₀, p.pos t₀ = some n → t₀ ≠ t := fun t₀ h₀ h₁ => by
          rw [h₁, hpp] at h₀; exact absurd h₀ (by simp)
        rw [Function.update_of_ne (hne t₁ h₂)] at h₁
        rw [Function.update_of_ne (hne t₂ h₄)] at h₃
        exact hs.pos_inj t₁ t₂ j' n h₁ h₂ h₃ h₄
      · exact le_trans (hs.next_le_cnt j') (by
          rcases eq_or_ne j' j with rfl | hne
          · simp
          · rw [Function.update_of_ne hne])
      · rcases eq_or_ne t' t with rfl | hne
        · rw [Function.update_self]; simp
        · rw [Function.update_of_ne hne]
          exact hs.cls_ne_none t' (by rwa [QueryCache.cacheQuery_of_ne c u hne] at ht')
      · have hne : t' ≠ t := fun hh => by
          rw [hh, QueryCache.cacheQuery_self] at ht'; exact absurd ht' (by simp)
        rw [Function.update_of_ne hne]
        exact hs.cls_none t' (by rwa [QueryCache.cacheQuery_of_ne c u hne] at ht')
      · rcases eq_or_ne t' t with rfl | hne
        · exact hpp
        · rw [Function.update_of_ne hne] at ht'
          exact hs.pos_none t' ht'
      · rcases eq_or_ne t' t with rfl | hne
        · rw [Function.update_self] at hcl
          have hj : j' = j := (Option.some_inj.mp hcl).symm
          subst hj
          exact ⟨hL, lt_of_le_of_lt (hs.next_le_cnt j') (by simp)⟩
        · rw [Function.update_of_ne hne] at hcl
          obtain ⟨h₁, h₂⟩ := hs.fallback t' j'
            (by rwa [QueryCache.cacheQuery_of_ne c u hne] at ht') hcl hps
          refine ⟨h₁, ?_⟩
          rcases eq_or_ne j' j with rfl | hnj
          · simpa using Nat.lt_succ_of_lt h₂
          · rwa [Function.update_of_ne hnj]
      · rcases eq_or_ne t' t with rfl | hne
        · rw [Function.update_self]
          rcases hjt with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        · rw [Function.update_of_ne hne] at ht' ⊢
          exact hs.cls_tau t' ht'
    · rw [tapeStep_run_cons hc hL, support_pure, Set.mem_singleton_iff] at hw
      subst hw
      rw [classPosStep_of_cons hc hL]
      dsimp only
      have hpt : p.cls t = none := hs.cls_none t hc
      have hpp : p.pos t = none := hs.pos_none t hpt
      set v : spec.Range t := cast h.symm u with hv
      have hhead : (Lfam j)[p.next j]? = some u := by
        have h0 := hs.getElem?_eq j 0
        rw [hL] at h0
        simpa using h0.symm
      have hnext : ∀ j', p.next j' ≤ Function.update p.next j (p.next j + 1) j' := by
        intro j'
        rcases eq_or_ne j' j with rfl | hnj
        · simp
        · rw [Function.update_of_ne hnj]
      refine ⟨fun t' j' n hcl hps => ?_, fun t₁ t₂ j' n h₁ h₂ h₃ h₄ => ?_, fun j' => ?_,
        fun j' i => ?_, fun j' => ?_, fun t' ht' => ?_, fun t' ht' => ?_, fun t' ht' => ?_,
        fun t' j' ht' hcl hps => ?_, fun t' ht' => ?_⟩
      · rcases eq_or_ne t' t with rfl | hne
        · rw [Function.update_self] at hcl
          rw [Function.update_self] at hps
          have hj : j' = j := (Option.some_inj.mp hcl).symm
          subst hj
          have hn : n = p.next j' := (Option.some_inj.mp hps).symm
          subst hn
          refine ⟨by simp, ?_⟩
          rw [QueryCache.cacheQuery_self, hhead]
          exact heq_some_cast h u
        · rw [Function.update_of_ne hne] at hcl
          rw [Function.update_of_ne hne] at hps
          exact ⟨lt_of_lt_of_le (hs.pos_spec t' j' n hcl hps).1 (hnext j'),
            (QueryCache.cacheQuery_of_ne c v hne) ▸ (hs.pos_spec t' j' n hcl hps).2⟩
      · rcases eq_or_ne t₁ t with rfl | hne₁
        · rcases eq_or_ne t₂ t₁ with rfl | hne₂
          · rfl
          · rw [Function.update_self] at h₁ h₂
            rw [Function.update_of_ne hne₂] at h₃ h₄
            have hj : j' = j := (Option.some_inj.mp h₁).symm
            subst hj
            have hn : n = p.next j' := (Option.some_inj.mp h₂).symm
            subst hn
            exact absurd (hs.pos_spec t₂ j' _ h₃ h₄).1 (lt_irrefl _)
        · rw [Function.update_of_ne hne₁] at h₁ h₂
          rcases eq_or_ne t₂ t with rfl | hne₂
          · rw [Function.update_self] at h₃ h₄
            have hj : j' = j := (Option.some_inj.mp h₃).symm
            subst hj
            have hn : n = p.next j' := (Option.some_inj.mp h₄).symm
            subst hn
            exact absurd (hs.pos_spec t₁ j' _ h₁ h₂).1 (lt_irrefl _)
          · rw [Function.update_of_ne hne₂] at h₃ h₄
            exact hs.pos_inj t₁ t₂ j' n h₁ h₂ h₃ h₄
      · rcases eq_or_ne j' j with rfl | hnj
        · have hla := hs.length_add j'
          rw [hL, List.length_cons] at hla
          simp only [Function.update_self]
          omega
        · rw [Function.update_of_ne hnj, Function.update_of_ne hnj]
          exact hs.length_add j'
      · rcases eq_or_ne j' j with rfl | hnj
        · have hge := hs.getElem?_eq j' (i + 1)
          rw [hL, List.getElem?_cons_succ] at hge
          simp only [Function.update_self]
          rw [hge, show p.next j' + (i + 1) = p.next j' + 1 + i from by omega]
        · rw [Function.update_of_ne hnj, Function.update_of_ne hnj]
          exact hs.getElem?_eq j' i
      · rcases eq_or_ne j' j with rfl | hnj
        · simp only [Function.update_self]
          exact Nat.succ_le_succ (hs.next_le_cnt j')
        · rw [Function.update_of_ne hnj, Function.update_of_ne hnj]
          exact hs.next_le_cnt j'
      · rcases eq_or_ne t' t with rfl | hne
        · rw [Function.update_self]; simp
        · rw [Function.update_of_ne hne]
          exact hs.cls_ne_none t' (by rwa [QueryCache.cacheQuery_of_ne c v hne] at ht')
      · have hne : t' ≠ t := fun hh => by
          rw [hh, QueryCache.cacheQuery_self] at ht'; exact absurd ht' (by simp)
        rw [Function.update_of_ne hne]
        exact hs.cls_none t' (by rwa [QueryCache.cacheQuery_of_ne c v hne] at ht')
      · have hne : t' ≠ t := fun hh => by
          rw [hh, Function.update_self] at ht'; exact absurd ht' (by simp)
        rw [Function.update_of_ne hne] at ht' ⊢
        exact hs.pos_none t' ht'
      · rcases eq_or_ne t' t with rfl | hne
        · rw [Function.update_self] at hps; exact absurd hps (by simp)
        · rw [Function.update_of_ne hne] at hcl hps
          obtain ⟨h₁, h₂⟩ := hs.fallback t' j'
            (by rwa [QueryCache.cacheQuery_of_ne c v hne] at ht') hcl hps
          have hnj : j' ≠ j := fun hh => by
            rw [hh, hL] at h₁; exact absurd h₁ (by simp)
          rw [Function.update_of_ne hnj, Function.update_of_ne hnj, Function.update_of_ne hnj]
          exact ⟨h₁, h₂⟩
      · rcases eq_or_ne t' t with rfl | hne
        · rw [Function.update_self]
          rcases hjt with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        · rw [Function.update_of_ne hne] at ht' ⊢
          exact hs.cls_tau t' ht'
  · rw [tapeStep_run_some hc, support_pure, Set.mem_singleton_iff] at hw
    subst hw
    rw [classPosStep_of_some hc]
    dsimp only
    refine ⟨hs.pos_spec, hs.pos_inj, hs.length_add, hs.getElem?_eq, fun j' => ?_,
      hs.cls_ne_none, hs.cls_none, hs.pos_none, fun t' j' ht' hcl hps => ?_, hs.cls_tau⟩
    · exact le_trans (hs.next_le_cnt j') (by
        rcases eq_or_ne j' j with rfl | hnj
        · simp
        · rw [Function.update_of_ne hnj])
    · obtain ⟨h₁, h₂⟩ := hs.fallback t' j' ht' hcl hps
      refine ⟨h₁, ?_⟩
      rcases eq_or_ne j' j with rfl | hnj
      · simpa using Nat.lt_succ_of_lt h₂
      · rwa [Function.update_of_ne hnj]

omit [Fintype J] [∀ j, SampleableType (R j)] in
/-- One instrumented step at the left copy: the tape step at the point, followed by the
bookkeeping of that point's tape class. -/
theorem extendState_run_inl (t : spec.Domain)
    (s : (spec.QueryCache × ((k : J) → List (R k))) × ClassPos spec.Domain J) :
    (QueryImpl.extendState (tapeCachingImplClass R τ hR) (classPosAux R τ) (Sum.inl t)).run s =
      ((tapeStep R (τ (Sum.inl t)) t (hR (Sum.inl t))).run s.1 >>= fun w =>
        pure (w.1, (w.2, classPosStep R (τ (Sum.inl t)) t s.1 w.1 w.2 s.2))) := by
  rw [QueryImpl.extendState_apply, tapeCachingImplClass_apply_inl]
  rfl

omit [Fintype J] [∀ j, SampleableType (R j)] in
/-- One instrumented step at the right copy: the tape step at the point, followed by the
bookkeeping of that point's tape class. -/
theorem extendState_run_inr (t : spec.Domain)
    (s : (spec.QueryCache × ((k : J) → List (R k))) × ClassPos spec.Domain J) :
    (QueryImpl.extendState (tapeCachingImplClass R τ hR) (classPosAux R τ) (Sum.inr t)).run s =
      ((tapeStep R (τ (Sum.inr t)) t (hR (Sum.inr t))).run s.1 >>= fun w =>
        pure (w.1, (w.2, classPosStep R (τ (Sum.inr t)) t s.1 w.1 w.2 s.2))) := by
  rw [QueryImpl.extendState_apply, tapeCachingImplClass_apply_inr]
  rfl

omit [Fintype J] [∀ j, SampleableType (R j)] in
/-- Every step of the instrumented class-indexed tape oracle preserves `ClassPosInv`. -/
theorem classPosInvAux_step (Lfam : (k : J) → List (R k)) (t : (spec + spec).Domain)
    (s : (spec.QueryCache × ((k : J) → List (R k))) × ClassPos spec.Domain J)
    (hs : ClassPosInv τ Lfam s.1.1 s.1.2 s.2.cls s.2.pos s.2.next s.2.cnt)
    (y : (spec + spec).Range t ×
      (spec.QueryCache × ((k : J) → List (R k))) × ClassPos spec.Domain J)
    (hy : y ∈ support
      ((QueryImpl.extendState (tapeCachingImplClass R τ hR) (classPosAux R τ) t).run s)) :
    ClassPosInv τ Lfam y.2.1.1 y.2.1.2 y.2.2.cls y.2.2.pos y.2.2.next y.2.2.cnt := by
  obtain ⟨⟨c, L⟩, p⟩ := s
  rcases t with t | t
  · rw [extendState_run_inl] at hy
    exact classPosInv_step (spec := spec) (j := τ (Sum.inl t)) (t := t) (c := c) (L := L)
      (p := p) Lfam (hR (Sum.inl t)) (Or.inl rfl) hs y hy
  · rw [extendState_run_inr] at hy
    exact classPosInv_step (spec := spec) (j := τ (Sum.inr t)) (t := t) (c := c) (L := L)
      (p := p) Lfam (hR (Sum.inr t)) (Or.inr rfl) hs y hy

omit [DecidableEq ι] [Fintype J] [DecidableEq J] [∀ j, SampleableType (R j)]
  [∀ t : spec.Domain, SampleableType (spec.Range t)] in
/-- **The positions of cached points, read off the invariant.** Under `ClassPosInv` with
bookkeeping `p`, every cached point has a class, pinned to one of its two call sites. If every
class in `T` was queried no more often than its tape is long, then a cached point whose class
`j` lies in `T` is the value of that class's tape at a position of that tape, returned in cast
form along the equality of the point's range with `R j`. Distinct cached points sit at distinct
class-position pairs.

The per-class query bounds are what exclude the fallback answers sampled after a tape runs
out: such an answer costs its class one query beyond the ones that consumed its whole tape.
A bound on the *total* size of the cache does not exclude them, because one class running out
of tape is consistent with the others' entries making up the total. Classes outside `T` need
no bound, so a class without a query budget does not obstruct the conclusion for the others. -/
theorem ClassPosInv.exists_pos (hR : ∀ t : (spec + spec).Domain, (spec + spec).Range t = R (τ t))
    {Lfam l : (k : J) → List (R k)} {c : spec.QueryCache} {p : ClassPos spec.Domain J}
    (hinv : ClassPosInv τ Lfam c l p.cls p.pos p.next p.cnt) (T : Set J)
    (hq : ∀ j ∈ T, p.cnt j ≤ (Lfam j).length) :
    (∀ t y, c t = some y → ∃ j, p.cls t = some j ∧ (j = τ (Sum.inl t) ∨ j = τ (Sum.inr t)) ∧
        (j ∈ T → ∃ n, p.pos t = some n ∧ n < (Lfam j).length ∧
          ∃ h : spec.Range t = R j, (Lfam j)[n]? = some (cast h y))) ∧
      (∀ t t' j n, p.cls t = some j → p.pos t = some n → p.cls t' = some j →
        p.pos t' = some n → t = t') := by
  refine ⟨fun t y ht => ?_, hinv.pos_inj⟩
  have htne : c t ≠ none := by rw [ht]; exact Option.some_ne_none y
  obtain ⟨j, hj⟩ : ∃ j, p.cls t = some j := Option.ne_none_iff_exists'.mp (hinv.cls_ne_none t htne)
  have hjt : j = τ (Sum.inl t) ∨ j = τ (Sum.inr t) := by
    rcases hinv.cls_tau t (by rw [hj]; exact Option.some_ne_none j) with hc | hc
    · exact Or.inl (Option.some_inj.mp (hj.symm.trans hc))
    · exact Or.inr (Option.some_inj.mp (hj.symm.trans hc))
  refine ⟨j, hj, hjt, fun hjT => ?_⟩
  obtain ⟨n, hn⟩ : ∃ n, p.pos t = some n := by
    rcases hp : p.pos t with _ | n
    · obtain ⟨hnil, hlt⟩ := hinv.fallback t j htne hj hp
      have hlen := hinv.length_add j
      rw [hnil, List.length_nil, Nat.zero_add] at hlen
      exact absurd (hlen ▸ hlt) (by have := hq j hjT; omega)
    · exact ⟨n, rfl⟩
  obtain ⟨hlt, hval⟩ := hinv.pos_spec t j n hj hn
  have hRj : spec.Range t = R j := by
    rcases hjt with rfl | rfl
    · exact hR (Sum.inl t)
    · exact hR (Sum.inr t)
  rw [ht] at hval
  exact ⟨n, hn, lt_of_lt_of_le hlt (by have := hinv.length_add j; omega), hRj,
    eq_some_cast_of_heq _ hval⟩

omit [Fintype J] [∀ j, SampleableType (R j)] in
/-- **Every cache entry of a class-indexed tape run of a budgeted class sits at its own
position on its class's tape.** `ClassPosInv.exists_pos` at the final state of a run of `oa`
under the instrumented `tapeCachingImplClass` from the empty cache and the empty bookkeeping on
the tape family `Lfam`. -/
theorem exists_pos_of_mem_support_run_tapeCachingImplClass {α : Type}
    (Lfam : (k : J) → List (R k)) (oa : OracleComp (spec + spec) α)
    {z : α × (spec.QueryCache × ((k : J) → List (R k))) × ClassPos spec.Domain J}
    (hz : z ∈ support ((simulateQ
      (QueryImpl.extendState (tapeCachingImplClass R τ hR) (classPosAux R τ)) oa).run
        ((∅, Lfam), ClassPos.init)))
    (T : Set J) (hq : ∀ j ∈ T, z.2.2.cnt j ≤ (Lfam j).length) :
    (∀ t y, z.2.1.1 t = some y → ∃ j, z.2.2.cls t = some j ∧
        (j = τ (Sum.inl t) ∨ j = τ (Sum.inr t)) ∧
        (j ∈ T → ∃ n, z.2.2.pos t = some n ∧ n < (Lfam j).length ∧
          ∃ h : spec.Range t = R j, (Lfam j)[n]? = some (cast h y))) ∧
      (∀ t t' j n, z.2.2.cls t = some j → z.2.2.pos t = some n → z.2.2.cls t' = some j →
        z.2.2.pos t' = some n → t = t') :=
  (simulateQ_run_preserves_inv_of_query
    (QueryImpl.extendState (tapeCachingImplClass R τ hR) (classPosAux R τ))
    (fun s => ClassPosInv τ Lfam s.1.1 s.1.2 s.2.cls s.2.pos s.2.next s.2.cnt)
    (fun t s hs => classPosInvAux_step Lfam t s hs) oa _
    (ClassPosInv.empty τ Lfam) z hz).exists_pos hR T hq

end Position

/-! ## Forwarded private sampling -/

section Forwarded

variable [∀ t : spec.Domain, SampleableType (spec.Range t)]

/-- The tape class of a query of the forwarded interface `unifSpec + (spec + spec)`: a query of
the duplicated interface has its class under `τ`, and a private uniform query has none. -/
@[expose]
def classOf (τ : (spec + spec).Domain → J) : (unifSpec + (spec + spec)).Domain → Option J
  | .inl _ => none
  | .inr t => some (τ t)

/-- The bookkeeping of one step of the forwarded class-indexed tape oracle: a query of the
duplicated interface is recorded by `classPosAux`, and a private uniform query records
nothing. -/
@[expose]
def classPosAuxFwd (R : J → Type) (τ : (spec + spec).Domain → J) :
    (t : (unifSpec + (spec + spec)).Domain) → (spec.QueryCache × ((k : J) → List (R k))) →
      (unifSpec + (spec + spec)).Range t → (spec.QueryCache × ((k : J) → List (R k))) →
      ClassPos spec.Domain J → ClassPos spec.Domain J
  | .inl _ => fun _ _ _ p => p
  | .inr t => classPosAux R τ t

omit [DecidableEq ι] [Fintype J] [DecidableEq J] [∀ j, SampleableType (R j)]
  [∀ t : spec.Domain, SampleableType (spec.Range t)] in
@[simp] theorem classOf_inl (τ : (spec + spec).Domain → J) (n : unifSpec.Domain) :
    classOf τ (Sum.inl n) = none := rfl

omit [DecidableEq ι] [Fintype J] [DecidableEq J] [∀ j, SampleableType (R j)]
  [∀ t : spec.Domain, SampleableType (spec.Range t)] in
@[simp] theorem classOf_inr (τ : (spec + spec).Domain → J) (t : (spec + spec).Domain) :
    classOf τ (Sum.inr t) = some (τ t) := rfl

omit [Fintype J] [∀ j, SampleableType (R j)]
  [∀ t : spec.Domain, SampleableType (spec.Range t)] in
@[simp] theorem classPosAuxFwd_inl (R : J → Type) (τ : (spec + spec).Domain → J)
    (n : unifSpec.Domain) : classPosAuxFwd R τ (Sum.inl n) = fun _ _ _ p => p := rfl

omit [Fintype J] [∀ j, SampleableType (R j)]
  [∀ t : spec.Domain, SampleableType (spec.Range t)] in
@[simp] theorem classPosAuxFwd_inr (R : J → Type) (τ : (spec + spec).Domain → J)
    (t : (spec + spec).Domain) : classPosAuxFwd R τ (Sum.inr t) = classPosAux R τ t := rfl

/-- **The instrumented forwarded class-indexed tape oracle.** `tapeImplFwd`, with the position
bookkeeping of `classPosAuxFwd` beside a passive auxiliary state `Q` that `aux` updates from
each step's states and answer. Neither auxiliary component influences the run. -/
abbrev classPosImplFwd (R : J → Type) (τ : (spec + spec).Domain → J)
    (hR : ∀ t : (spec + spec).Domain, (spec + spec).Range t = R (τ t)) {Q : Type}
    (aux : (t : (unifSpec + (spec + spec)).Domain) →
      (spec.QueryCache × ((k : J) → List (R k))) → (unifSpec + (spec + spec)).Range t →
      (spec.QueryCache × ((k : J) → List (R k))) → Q → Q) :
    QueryImpl (unifSpec + (spec + spec))
      (StateT ((spec.QueryCache × ((k : J) → List (R k))) × (ClassPos spec.Domain J × Q))
        ProbComp) :=
  (tapeImplFwd R τ hR).extendState fun t s u s' pq =>
    (classPosAuxFwd R τ t s u s' pq.1, aux t s u s' pq.2)

variable (τ : (spec + spec).Domain → J)
  (hR : ∀ t : (spec + spec).Domain, (spec + spec).Range t = R (τ t)) {Q : Type}
  (aux : (t : (unifSpec + (spec + spec)).Domain) →
    (spec.QueryCache × ((k : J) → List (R k))) → (unifSpec + (spec + spec)).Range t →
    (spec.QueryCache × ((k : J) → List (R k))) → Q → Q) (q₀ : Q)

omit [Fintype J] [∀ j, SampleableType (R j)] in
/-- Every step of `classPosImplFwd` preserves `ClassPosInv`: a private uniform query changes
neither the cache, the tapes nor the bookkeeping, and a query of the duplicated interface is a
step of the unforwarded instrumentation. -/
theorem classPosInvAuxFwd_step (Lfam : (k : J) → List (R k))
    (t : (unifSpec + (spec + spec)).Domain)
    (s : (spec.QueryCache × ((k : J) → List (R k))) × (ClassPos spec.Domain J × Q))
    (hs : ClassPosInv τ Lfam s.1.1 s.1.2 s.2.1.cls s.2.1.pos s.2.1.next s.2.1.cnt)
    (y : (unifSpec + (spec + spec)).Range t ×
      (spec.QueryCache × ((k : J) → List (R k))) × (ClassPos spec.Domain J × Q))
    (hy : y ∈ support ((classPosImplFwd R τ hR aux t).run s)) :
    ClassPosInv τ Lfam y.2.1.1 y.2.1.2 y.2.2.1.cls y.2.2.1.pos y.2.2.1.next y.2.2.1.cnt := by
  obtain ⟨hv, hq⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ t s y).1 hy
  rcases t with n | t
  · have hv2 : y.2.1 = s.1 := by
      simp only [tapeImplFwd, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
        StateT.run_monadLift, support_bind, support_pure, Set.mem_iUnion] at hv
      obtain ⟨u, -, hu⟩ := hv
      exact (Prod.mk.inj (Set.mem_singleton_iff.mp hu)).2
    simpa only [hq, hv2, classPosAuxFwd] using hs
  · exact classPosInvAux_step Lfam t (s.1, s.2.1) hs (y.1, (y.2.1, y.2.2.1))
      ((QueryImpl.mem_support_extendState_run_iff _ _ t _ _).2 ⟨hv, congrArg Prod.fst hq⟩)

omit [Fintype J] [∀ j, SampleableType (R j)] in
/-- **Every cache entry of a forwarded class-indexed tape run of a budgeted class sits at its
own position on its class's tape.** `ClassPosInv.exists_pos` at the final state of a run of
`oa` under `classPosImplFwd` from the empty cache and the empty bookkeeping on the tape family
`Lfam`. Only the classes in `T` need a query bound. -/
theorem exists_pos_of_mem_support_run_classPosImplFwd {α : Type}
    (Lfam : (k : J) → List (R k)) (oa : OracleComp (unifSpec + (spec + spec)) α)
    {z : α × ((spec.QueryCache × ((k : J) → List (R k))) × (ClassPos spec.Domain J × Q))}
    (hz : z ∈ support ((simulateQ (classPosImplFwd R τ hR aux) oa).run
      ((∅, Lfam), (ClassPos.init, q₀))))
    (T : Set J) (hq : ∀ j ∈ T, z.2.2.1.cnt j ≤ (Lfam j).length) :
    (∀ t y, z.2.1.1 t = some y → ∃ j, z.2.2.1.cls t = some j ∧
        (j = τ (Sum.inl t) ∨ j = τ (Sum.inr t)) ∧
        (j ∈ T → ∃ n, z.2.2.1.pos t = some n ∧ n < (Lfam j).length ∧
          ∃ h : spec.Range t = R j, (Lfam j)[n]? = some (cast h y))) ∧
      (∀ t t' j n, z.2.2.1.cls t = some j → z.2.2.1.pos t = some n → z.2.2.1.cls t' = some j →
        z.2.2.1.pos t' = some n → t = t') :=
  (simulateQ_run_preserves_inv_of_query (classPosImplFwd R τ hR aux)
    (fun s => ClassPosInv τ Lfam s.1.1 s.1.2 s.2.1.cls s.2.1.pos s.2.1.next s.2.1.cnt)
    (classPosInvAuxFwd_step τ hR aux Lfam) oa _ (ClassPosInv.empty τ Lfam) z hz).exists_pos
    hR T hq

omit [Fintype J] [∀ j, SampleableType (R j)] in
/-- **Per-class query budgets bound the class counters.** If `oa` makes at most `n` queries of
tape class `j`, then on every run of `oa` under `classPosImplFwd` from the empty bookkeeping,
the query counter of class `j` is at most `n`. -/
theorem cnt_le_of_isQueryBoundP {α : Type} (Lfam : (k : J) → List (R k))
    (oa : OracleComp (unifSpec + (spec + spec)) α) (j : J) {n : ℕ}
    (hb : IsQueryBoundP oa (fun t => classOf τ t = some j) n)
    {z : α × ((spec.QueryCache × ((k : J) → List (R k))) × (ClassPos spec.Domain J × Q))}
    (hz : z ∈ support ((simulateQ (classPosImplFwd R τ hR aux) oa).run
      ((∅, Lfam), (ClassPos.init, q₀)))) :
    z.2.2.1.cnt j ≤ n := by
  have hcnt : ∀ (t : (unifSpec + (spec + spec)).Domain) s u s' (p : ClassPos spec.Domain J),
      (classPosAuxFwd R τ t s u s' p).cnt j ≤
        p.cnt j + if classOf τ t = some j then 1 else 0 := by
    rintro (n | t) s u s' p
    · simp [classPosAuxFwd, classOf]
    · have hstep : ∀ (k : J) (t₀ : spec.Domain) s u s',
          (classPosStep R k t₀ s u s' p).cnt = Function.update p.cnt k (p.cnt k + 1) := by
        intro k t₀ s u s'
        unfold classPosStep
        split <;> rfl
      have hτ : (classPosAuxFwd R τ (Sum.inr t) s u s' p).cnt =
          Function.update p.cnt (τ t) (p.cnt (τ t) + 1) := by
        rcases t with t | t <;> exact hstep _ _ s u s'
      rw [hτ]
      by_cases hj : τ t = j
      · subst hj; simp [classOf]
      · simp [classOf, hj, Function.update_of_ne (Ne.symm hj)]
  have hsupp : ∀ t
      (st : (spec.QueryCache × ((k : J) → List (R k))) × (ClassPos spec.Domain J × Q)) y,
      y ∈ support ((classPosImplFwd R τ hR aux t).run st) →
        y.2.2.1.cnt j ≤ st.2.1.cnt j + if classOf τ t = some j then 1 else 0 := by
    intro t st y hy
    rw [QueryImpl.extendState_apply, mem_support_bind_iff] at hy
    obtain ⟨v, -, hy⟩ := hy
    rw [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact hcnt t _ _ _ _
  have := hb.cost_le_of_mem_support_run_simulateQ (impl := classPosImplFwd R τ hR aux)
    (fun st => st.2.1.cnt j)
    (fun t ht st y hy => by simpa [ht] using hsupp t st y hy)
    (fun t ht st y hy => by simpa [ht] using hsupp t st y hy) _ z hz
  simpa using this

/-- **Transporting tape-event bounds to a forwarded lazy random-oracle run, in bind form.**
Suppose that on every family `L` the draw `tapeFamily R m` can produce, every outcome `z` of the
instrumented run of `oa` on `L` whose output and final cache satisfy `P` has a witness `w ∈ Ws`
with the tape event `M w L` and the run event `H w z`, and that each run event `H w` has mass
at most `β w` on every such family. Then the lazy run of `oa` under `dupRandomOracleFwd` from
the empty cache satisfies `P` with probability at most `∑ w ∈ Ws, Pr_tape[M w] * β w`. -/
theorem prEvent_run_dupRandomOracleFwd_le_sum {α W : Type}
    (oa : OracleComp (unifSpec + (spec + spec)) α) (m : J → ℕ)
    (P : α × spec.QueryCache → Prop) (Ws : Finset W) (M : W → ((k : J) → List (R k)) → Prop)
    (H : W → α × ((spec.QueryCache × ((k : J) → List (R k))) × (ClassPos spec.Domain J × Q)) →
      Prop)
    (β : W → ℝ≥0∞)
    (hmap : ∀ L ∈ support (tapeFamily R m), ∀ z ∈ support
        ((simulateQ (classPosImplFwd R τ hR aux) oa).run ((∅, L), (ClassPos.init, q₀))),
      P (z.1, z.2.1.1) → ∃ w ∈ Ws, M w L ∧ H w z)
    (hH : ∀ L ∈ support (tapeFamily R m), ∀ w ∈ Ws,
      Pr{let z ← (simulateQ (classPosImplFwd R τ hR aux) oa).run
          ((∅, L), (ClassPos.init, q₀))}[H w z] ≤ β w) :
    Pr{let z ← (simulateQ (dupRandomOracleFwd spec) oa).run ∅}[P z] ≤
      ∑ w ∈ Ws, Pr{let L ← tapeFamily R m}[M w L] * β w := by
  classical
  let _ : MeasurableSpace (α × spec.QueryCache) := ⊤
  have _ : DiscreteMeasurableSpace (α × spec.QueryCache) := ⟨fun _ => trivial⟩
  let _ : MeasurableSpace ((k : J) → List (R k)) := ⊤
  have _ : DiscreteMeasurableSpace ((k : J) → List (R k)) := ⟨fun _ => trivial⟩
  set run := fun L : (k : J) → List (R k) =>
    (simulateQ (classPosImplFwd R τ hR aux) oa).run ((∅, L), (ClassPos.init, q₀)) with hrun
  have hcomp : (tapeFamily R m >>= fun L =>
      (simulateQ (tapeImplFwd R τ hR) oa).run (∅, L) >>= fun z =>
        (pure (z.1, z.2.1) : ProbComp (α × spec.QueryCache))) =
      tapeFamily R m >>= fun L => (fun z => (z.1, z.2.1.1)) <$> run L := by
    refine bind_congr fun L => ?_
    rw [← extendState_run_proj_eq (tapeImplFwd R τ hR)
      (fun t s u s' pq => (classPosAuxFwd R τ t s u s' pq.1, aux t s u s' pq.2)) oa (∅, L)
      (ClassPos.init, q₀)]
    simp only [hrun, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply,
      Prod.map_fst, Prod.map_snd, id_eq]
    rfl
  rw [prEvent_eq_evalDist_of_discrete, evalDist_run_dupRandomOracleFwd_eq_tapeFamily τ hR oa ∅ m,
    hcomp, ← prEvent_eq_evalDist_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  have hs : ∀ᵐ L ∂𝒟[tapeFamily R m], L ∈ support (tapeFamily R m) := by
    rw [ae_iff]
    have := prEvent_eq_zero_of_forall_mem_support (tapeFamily R m)
      (fun L => L ∉ support (tapeFamily R m)) (fun L hL h => h hL)
    rwa [prEvent_eq_evalDist_of_discrete] at this
  calc ∫⁻ L, Pr{let y ← (fun z : α × ((spec.QueryCache × ((k : J) → List (R k))) ×
          (ClassPos spec.Domain J × Q)) => (z.1, z.2.1.1)) <$> run L}[P y] ∂𝒟[tapeFamily R m]
      ≤ ∫⁻ L, ∑ w ∈ Ws, Set.indicator {L | M w L} (fun _ => β w) L ∂𝒟[tapeFamily R m] := by
        refine lintegral_mono_ae ?_
        filter_upwards [hs] with L hL
        rw [prEvent_map]
        refine (prEvent_mono_of_support _ _ (fun z => ∃ w ∈ Ws, M w L ∧ H w z)
          (fun z hz hP => hmap L hL z hz hP)).trans ?_
        refine (prEvent_exists_finset_le Ws _ _).trans (Finset.sum_le_sum fun w hw => ?_)
        by_cases hM : M w L
        · rw [Set.indicator_of_mem (show L ∈ {L | M w L} from hM)]
          simpa only [hM, true_and] using hH L hL w hw
        · rw [Set.indicator_of_notMem (show L ∉ {L | M w L} from hM)]
          exact (prEvent_eq_zero_of_forall_not _ _ fun z h => hM h.1).le
    _ = ∑ w ∈ Ws, Pr{let L ← tapeFamily R m}[M w L] * β w := by
        rw [lintegral_finsetSum _ (fun w _ => Measurable.of_discrete)]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [lintegral_indicator_const MeasurableSet.of_discrete, prEvent_eq_evalDist_of_discrete,
          mul_comm]

end Forwarded

end AnswerTape

/-! ## A hit set written at fresh draws -/

namespace AnswerTape

section FreshHitStep

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} (trig : spec.Domain → Prop) [DecidablePred trig]
  (rel : (x : spec.Domain) → spec.Range x → spec.Domain → Prop)

/-- The hit set after the point `x` is answered `u` on the cache `c`: if `x` is uncached in `c`
and satisfies `trig`, every point `y` cached in `c` with `rel x u y` joins `hs`; otherwise `hs`
is unchanged. -/
@[expose]
def freshHitStep (c : spec.QueryCache) (x : spec.Domain) (u : spec.Range x)
    (hs : Set spec.Domain) : Set spec.Domain :=
  if c x = none ∧ trig x then hs ∪ {y | c y ≠ none ∧ rel x u y} else hs

variable {c : spec.QueryCache} {x : spec.Domain} {u : spec.Range x} {hs : Set spec.Domain}

/-- A step only adds to the hit set. -/
theorem subset_freshHitStep : hs ⊆ freshHitStep trig rel c x u hs := by
  unfold freshHitStep; split_ifs <;> simp

/-- A cache hit writes nothing. -/
theorem freshHitStep_of_ne_none (hc : c x ≠ none) : freshHitStep trig rel c x u hs = hs := by
  simp [freshHitStep, hc]

/-- A point outside `trig` writes nothing. -/
theorem freshHitStep_of_not (hx : ¬ trig x) : freshHitStep trig rel c x u hs = hs := by
  simp [freshHitStep, hx]

/-- A fresh draw at a point in `trig` adds the points cached before it that it relates to. -/
theorem freshHitStep_of_eq_none (hc : c x = none) (hx : trig x) :
    freshHitStep trig rel c x u hs = hs ∪ {y | c y ≠ none ∧ rel x u y} := by
  simp [freshHitStep, hc, hx]

/-- A point of the hit set after a step was in it before, or is cached in `c`. -/
theorem mem_or_ne_none_of_mem_freshHitStep {y : spec.Domain}
    (hy : y ∈ freshHitStep trig rel c x u hs) : y ∈ hs ∨ c y ≠ none := by
  unfold freshHitStep at hy
  split_ifs at hy
  · exact hy.imp_right And.left
  · exact .inl hy

/-- If every point of `hs` is cached in `c`, so is every point of the hit set after a step. -/
theorem ne_none_of_mem_freshHitStep (hhs : ∀ y ∈ hs, c y ≠ none) :
    ∀ y ∈ freshHitStep trig rel c x u hs, c y ≠ none := fun y hy =>
  (mem_or_ne_none_of_mem_freshHitStep trig rel hy).elim (hhs y) id

end FreshHitStep

section FreshHit

variable {ι J : Type} {spec : OracleSpec.{0, 0} ι} [DecidableEq ι] [DecidableEq J]
  {R : J → Type} (trig : spec.Domain → Prop) [DecidablePred trig]
  (rel : (x : spec.Domain) → spec.Range x → spec.Domain → Prop)

/-- The hit-set bookkeeping of one step of the forwarded class-indexed tape oracle: a query of
either copy at a point `x` records `freshHitStep` on the cache before the step, and a private
uniform query records nothing. The hit set therefore grows only at a fresh draw at a point
satisfying `trig`, and only by points cached before that draw. -/
@[expose]
def freshHitAux :
    (t : (unifSpec + (spec + spec)).Domain) → (spec.QueryCache × ((k : J) → List (R k))) →
      (unifSpec + (spec + spec)).Range t → (spec.QueryCache × ((k : J) → List (R k))) →
      Set spec.Domain → Set spec.Domain
  | .inl _ => fun _ _ _ hs => hs
  | .inr (.inl x) => fun s u _ hs => freshHitStep trig rel s.1 x u hs
  | .inr (.inr x) => fun s u _ hs => freshHitStep trig rel s.1 x u hs

variable (τ : (spec + spec).Domain → J)
  (hR : ∀ t : (spec + spec).Domain, (spec + spec).Range t = R (τ t))

/-- The bookkeeping of a step leaves the class and position of a point cached before it. -/
theorem classPosAuxFwd_cls_pos_of_ne_none (t : (unifSpec + (spec + spec)).Domain)
    (s s' : spec.QueryCache × ((k : J) → List (R k))) (u : (unifSpec + (spec + spec)).Range t)
    (p : ClassPos spec.Domain J) {y : spec.Domain} (hy : s.1 y ≠ none) :
    (classPosAuxFwd R τ t s u s' p).cls y = p.cls y ∧
      (classPosAuxFwd R τ t s u s' p).pos y = p.pos y := by
  have key : ∀ (j : J) (x : spec.Domain) (u : spec.Range x),
      (classPosStep R j x s u s' p).cls y = p.cls y ∧
        (classPosStep R j x s u s' p).pos y = p.pos y := by
    intro j x u
    obtain ⟨c, L⟩ := s
    rcases hc : c x with _ | u₀
    · have hne : y ≠ x := fun h => hy (h ▸ hc)
      rcases hL : L j with _ | ⟨v, l⟩
      · simp [classPosStep_of_nil hc hL, Function.update_of_ne hne]
      · simp [classPosStep_of_cons hc hL, Function.update_of_ne hne]
    · simp [classPosStep_of_some hc]
  rcases t with n | (x | x)
  · exact ⟨rfl, rfl⟩
  · exact key _ x u
  · exact key _ x u

variable [∀ t : spec.Domain, SampleableType (spec.Range t)]

/-- A step of `tapeImplFwd` only extends the cache. -/
theorem le_of_mem_support_tapeImplFwd_run (t : (unifSpec + (spec + spec)).Domain)
    (s : spec.QueryCache × ((k : J) → List (R k)))
    (y : (unifSpec + (spec + spec)).Range t × (spec.QueryCache × ((k : J) → List (R k))))
    (hy : y ∈ support ((tapeImplFwd R τ hR t).run s)) : s.1 ≤ y.2.1 := by
  obtain ⟨c, L⟩ := s
  have key : ∀ (j : J) (x : spec.Domain) (h : spec.Range x = R j)
      (y : spec.Range x × (spec.QueryCache × ((k : J) → List (R k)))),
      y ∈ support ((tapeStep R j x h).run (c, L)) → c ≤ y.2.1 := by
    intro j x h y hy
    rcases hc : c x with _ | u₀
    · rcases hL : L j with _ | ⟨u, l⟩
      · rw [tapeStep_run_nil hc hL, support_map] at hy
        obtain ⟨u, -, rfl⟩ := hy
        exact QueryCache.le_cacheQuery c hc
      · rw [tapeStep_run_cons hc hL, support_pure, Set.mem_singleton_iff] at hy
        exact hy ▸ QueryCache.le_cacheQuery c hc
    · rw [tapeStep_run_some hc, support_pure, Set.mem_singleton_iff] at hy
      exact hy ▸ le_rfl
  rcases t with n | (x | x)
  · simp only [tapeImplFwd, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
      StateT.run_monadLift, support_bind, support_pure, Set.mem_iUnion] at hy
    obtain ⟨u, -, hu⟩ := hy
    rw [Set.mem_singleton_iff] at hu
    rw [hu]
  · exact key _ x _ y (by simpa [tapeCachingImplClass_apply_inl] using hy)
  · exact key _ x _ y (by simpa [tapeCachingImplClass_apply_inr] using hy)

/-- **One step of the instrumented run.** A step of `classPosImplFwd` under `freshHitAux` only
extends the cache, keeps the class and position of every point cached before it, and only grows
the hit set, by points cached before it. -/
theorem mono_of_mem_support_classPosImplFwd_run (t : (unifSpec + (spec + spec)).Domain)
    (s : (spec.QueryCache × ((k : J) → List (R k))) × (ClassPos spec.Domain J × Set spec.Domain))
    (y : (unifSpec + (spec + spec)).Range t ×
      (spec.QueryCache × ((k : J) → List (R k))) × (ClassPos spec.Domain J × Set spec.Domain))
    (hy : y ∈ support ((classPosImplFwd R τ hR (freshHitAux trig rel) t).run s)) :
    s.1.1 ≤ y.2.1.1 ∧ (∀ p, s.1.1 p ≠ none → y.2.2.1.cls p = s.2.1.cls p ∧
      y.2.2.1.pos p = s.2.1.pos p) ∧ s.2.2 ⊆ y.2.2.2 ∧
      ∀ p ∈ y.2.2.2, p ∈ s.2.2 ∨ s.1.1 p ≠ none := by
  obtain ⟨hv, hq⟩ := (QueryImpl.mem_support_extendState_run_iff _ _ t s y).1 hy
  rw [hq]
  refine ⟨le_of_mem_support_tapeImplFwd_run τ hR t s.1 _ hv,
    fun p hp => classPosAuxFwd_cls_pos_of_ne_none τ t _ _ _ _ hp, ?_⟩
  rcases t with n | (x | x)
  · exact ⟨subset_rfl, fun p hp => .inl hp⟩
  all_goals exact ⟨subset_freshHitStep trig rel,
    fun p hp => mem_or_ne_none_of_mem_freshHitStep trig rel hp⟩

/-- **The hit set changes only at fresh draws.** A step of `classPosImplFwd` under
`freshHitAux` that is not a query, at either copy, of a point uncached before it and satisfying
`trig` leaves the hit set unchanged. -/
theorem hits_eq_self_of_mem_support_classPosImplFwd_run (t : (unifSpec + (spec + spec)).Domain)
    (s : (spec.QueryCache × ((k : J) → List (R k))) × (ClassPos spec.Domain J × Set spec.Domain))
    (hnot : ∀ x, (t = Sum.inr (Sum.inl x) ∨ t = Sum.inr (Sum.inr x)) → s.1.1 x = none →
      ¬ trig x)
    (y : (unifSpec + (spec + spec)).Range t ×
      (spec.QueryCache × ((k : J) → List (R k))) × (ClassPos spec.Domain J × Set spec.Domain))
    (hy : y ∈ support ((classPosImplFwd R τ hR (freshHitAux trig rel) t).run s)) :
    y.2.2.2 = s.2.2 := by
  rw [((QueryImpl.mem_support_extendState_run_iff _ _ t s y).1 hy).2]
  rcases t with n | (x | x)
  · rfl
  all_goals
    dsimp only [freshHitAux]
    by_cases hc : s.1.1 x = none
    · exact freshHitStep_of_not trig rel (hnot x (by simp) hc)
    · exact freshHitStep_of_ne_none trig rel hc

/-- **Hits stay cached.** If every point of the hit set is cached before a step of
`classPosImplFwd` under `freshHitAux`, every point of the hit set is cached after it: a point
joins the hit set only if it is cached before the step, and a step only extends the cache. -/
theorem ne_none_of_mem_hits_of_mem_support_classPosImplFwd_run
    (t : (unifSpec + (spec + spec)).Domain)
    (s : (spec.QueryCache × ((k : J) → List (R k))) × (ClassPos spec.Domain J × Set spec.Domain))
    (hs : ∀ p ∈ s.2.2, s.1.1 p ≠ none)
    (y : (unifSpec + (spec + spec)).Range t ×
      (spec.QueryCache × ((k : J) → List (R k))) × (ClassPos spec.Domain J × Set spec.Domain))
    (hy : y ∈ support ((classPosImplFwd R τ hR (freshHitAux trig rel) t).run s)) :
    ∀ p ∈ y.2.2.2, y.2.1.1 p ≠ none := by
  obtain ⟨hle, -, -, hnew⟩ := mono_of_mem_support_classPosImplFwd_run trig rel τ hR t s y hy
  intro p hp
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp ((hnew p hp).elim (hs p) id)
  rw [hle hv]
  exact Option.some_ne_none v

/-- **Hits stay cached along a run.** If every point of the hit set is cached in the initial
state, then on every run of `oa` under `classPosImplFwd` with `freshHitAux`, every point of the
final hit set is cached in the final cache. -/
theorem ne_none_of_mem_hits_of_mem_support_run_classPosImplFwd {α : Type}
    (oa : OracleComp (unifSpec + (spec + spec)) α)
    (s : (spec.QueryCache × ((k : J) → List (R k))) × (ClassPos spec.Domain J × Set spec.Domain))
    (hs : ∀ p ∈ s.2.2, s.1.1 p ≠ none)
    {z : α × ((spec.QueryCache × ((k : J) → List (R k))) ×
      (ClassPos spec.Domain J × Set spec.Domain))}
    (hz : z ∈ support ((simulateQ (classPosImplFwd R τ hR (freshHitAux trig rel)) oa).run s)) :
    ∀ p ∈ z.2.2.2, z.2.1.1 p ≠ none :=
  simulateQ_run_preserves_inv_of_query _ (fun s => ∀ p ∈ s.2.2, s.1.1 p ≠ none)
    (ne_none_of_mem_hits_of_mem_support_classPosImplFwd_run trig rel τ hR) oa s hs z hz

/-- **Monotonicity of the instrumented run.** Along every run of `oa` under `classPosImplFwd`
with `freshHitAux`, the cache only grows, a point cached in the initial state keeps its class
and position, and the hit set only grows. -/
theorem mono_of_mem_support_run_classPosImplFwd_freshHitAux {α : Type}
    (oa : OracleComp (unifSpec + (spec + spec)) α)
    (s : (spec.QueryCache × ((k : J) → List (R k))) × (ClassPos spec.Domain J × Set spec.Domain))
    {z : α × ((spec.QueryCache × ((k : J) → List (R k))) ×
      (ClassPos spec.Domain J × Set spec.Domain))}
    (hz : z ∈ support ((simulateQ (classPosImplFwd R τ hR (freshHitAux trig rel)) oa).run s)) :
    s.1.1 ≤ z.2.1.1 ∧ (∀ t, s.1.1 t ≠ none → z.2.2.1.cls t = s.2.1.cls t ∧
      z.2.2.1.pos t = s.2.1.pos t) ∧ s.2.2 ⊆ z.2.2.2 := by
  refine simulateQ_run_preserves_inv_of_query _
    (fun s' => s.1.1 ≤ s'.1.1 ∧ (∀ t, s.1.1 t ≠ none → s'.2.1.cls t = s.2.1.cls t ∧
      s'.2.1.pos t = s.2.1.pos t) ∧ s.2.2 ⊆ s'.2.2)
    (fun t s' ⟨hle, hcp, hsub⟩ y hy => ?_) oa s ⟨le_rfl, fun _ _ => ⟨rfl, rfl⟩, subset_rfl⟩ z hz
  obtain ⟨hle', hcp', hsub', -⟩ :=
    mono_of_mem_support_classPosImplFwd_run trig rel τ hR t s' y hy
  refine ⟨hle.trans hle', fun p hp => ?_, hsub.trans hsub'⟩
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hp
  obtain ⟨h₁, h₂⟩ := hcp' p (by rw [hle hv]; exact Option.some_ne_none v)
  exact ⟨h₁.trans (hcp p hp).1, h₂.trans (hcp p hp).2⟩

end FreshHit

end AnswerTape
