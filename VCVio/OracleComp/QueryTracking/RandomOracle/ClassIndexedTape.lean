/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.EvalDist.Lossless
public import VCVio.OracleComp.QueryTracking.RandomOracle.Tape

/-!
# Answer tapes indexed by a tape class

`Tape.lean` supplies fresh random-oracle answers from one list, of one answer type. This
file supplies them from a *family* of lists, one per tape class, over an arbitrary `spec` whose
ranges may vary from point to point.

Two things vary at once, and they are independent of each other.

* **The interface is duplicated.** `dupRandomOracle` answers `spec + spec` out of one shared
  `spec.QueryCache`, so the two copies are one oracle and the sum tag is a distinction in the
  program's syntax, not in the run (`simulateQ_dupRandomOracle_eq`). A distinction between
  call sites cannot be read off the domain, because the same point may be queried from both;
  it is `τ` that turns the tag into a tape class.
* **The answers are typed by class.** A tape-class map `τ : (spec + spec).Domain → J` sends
  each point of the duplicated interface to a class whose answer type is `R (τ t)`, witnessed
  by `hR`. `tapeCachingImplClass` answers a fresh query off the tape of its class, so a run
  consumes one list per class rather than one list overall.

`tapeFamily` draws the whole family in one step, and
`evalDist_run_dupRandomOracle_eq_tapeFamily` identifies the shared lazy random oracle with the
class-indexed tape oracle averaged over it, jointly in the output and the final cache, from an
arbitrary starting cache, for every assignment of tape lengths to classes. The identification
rests on `evalDist_tapeFamily_bind_of_succ`, which peels one class's next draw out of the
bundled family. That peel and its companion `evalDist_tapeFamily_bind_of_zero` also carry the
laws of the family a caller needs: `evalDist_tapeFamily_bind_eval` reads off one class,
`evalDist_tapeFamily_bind_eval₂` reads off two distinct classes independently, and
`evalDist_tapeFamily_setOf_eq` restates an event of one class's tape as an event of that
class's `answerTape`, which is the shape `IndepProductEvents.lean` bounds, and
`evalDist_tapeFamily_setOf_eq₂` does the same for two distinct classes carrying the same answer
type, landing on a single `answerTape` over the summed index by way of
`evalDist_answerTape_append`.
`length_of_mem_support_tapeFamily` says a drawn family has the lengths it was asked for.

A program that also samples privately runs over `unifSpec + (spec + spec)`.
`dupRandomOracleFwd` and `tapeImplFwd` forward its `unifSpec` queries to `ProbComp`, touching
neither the cache nor any tape, and `evalDist_run_dupRandomOracleFwd_eq_tapeFamily` is the same
identification for them.

The identification is insensitive to `τ`: sending a class to draw from a different class's
tape leaves it true, because the tapes are i.i.d. across classes and it averages over all of
them. Nothing in it ties an answer to a class. What does that is the instrumentation of
`ClassIndexedTape/Position.lean`, which also transports bounds on tape events to the lazy run.

## Scope

* Nothing here bounds the mass of any tape event, and nothing here relates a run event to a
  tape event: both are the business of `ClassIndexedTape/Position.lean`.
* The set-level bridge to `IndepProductEvents.lean` covers one class
  (`evalDist_tapeFamily_setOf_eq`) or two (`evalDist_tapeFamily_setOf_eq₂`). Both require the
  answer types to carry a measurable space on which every set is measurable, and produce the
  `answerTape` law at that space rather than at `⊤`, which is what makes their output the same
  term as the one a bound on an `answerTape` event is stated at. The two-class form also
  requires the two classes to carry the same answer type, since the single `answerTape` it
  lands on has one entry type. An event spanning three or more classes has its joint law
  nowhere here, not even in bind form: `evalDist_tapeFamily_bind_eval₂` reads off exactly
  two.
* No query bound relates the tape lengths to the number of queries a computation makes: the
  identification holds for every assignment `m`, with the tape oracle sampling freshly once a
  tape runs out. Only the position lemmas need per-class bounds, and they take them as
  hypotheses on the instrumented run's own counters, against the lengths of the family it was
  run on; `length_of_mem_support_tapeFamily` is what identifies those lengths with `m`.
* The duplication is into exactly two copies. A run distinguishing more than two call sites is
  not covered, though the tape classes themselves are an arbitrary finite index.
* The class map must send a point to a class whose answer type *equals* the point's range.
  An interface presenting merely equivalent answer types is not covered.
* A consumer's own `R : J → Type`, the `spec` it instantiates and the class map `τ` must each
  be `@[expose]` or an `abbrev`: otherwise the module compiler cannot see through them and the
  instantiation is rejected — for `R` the `SampleableType (R j)` instances fail to synthesise,
  and for a plain `def` spec or class map elaboration reports a differing inferred compilation
  type. A spec that already lives in an `@[expose] public section` file needs nothing further.
* The family is drawn as lists, so a tape's length is a fact about the draw
  (`length_of_mem_support_tapeFamily`) rather than a fact about its type. Drawing it as
  `(j : J) → (Fin (m j) → R j)` and mapping to lists would make the lengths structural and
  would hand `IndepProductEvents.lean` its native shape per class; that is a redesign, not a
  gap this file papers over.
-/

public section

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace AnswerTape

variable {ι J : Type} {spec : OracleSpec.{0, 0} ι} [DecidableEq ι]
  [Fintype J] [DecidableEq J] {R : J → Type} [∀ j, SampleableType (R j)]

/-! ## The bundled tape family -/

/-- The tapes of the classes listed in `js`, drawn independently, the tape of class `j` holding
`m j` uniform values; a class outside `js` gets the empty tape. -/
private noncomputable def tapeOn (R : J → Type) [∀ j, SampleableType (R j)] (m : J → ℕ) :
    List J → ProbComp ((j : J) → List (R j))
  | [] => pure fun _ => []
  | j :: js => do
      let l ← tapeList (R j) (m j)
      let L ← tapeOn R m js
      return Function.update L j l

/-- **The bundled tape family.** One independent tape per class, the tape of class `j` holding
`m j` uniform values of `R j`, all drawn in a single step. -/
noncomputable def tapeFamily (R : J → Type) [∀ j, SampleableType (R j)] (m : J → ℕ) :
    ProbComp ((j : J) → List (R j)) :=
  tapeOn R m Finset.univ.toList

omit [Fintype J] in
private theorem tapeOn_congr {m m' : J → ℕ} :
    ∀ js : List J, (∀ j ∈ js, m j = m' j) → tapeOn R m js = tapeOn R m' js
  | [], _ => rfl
  | j :: js, h => by
      rw [tapeOn, tapeOn, h j (by simp), tapeOn_congr js fun j' hj' => h j' (by simp [hj'])]

omit [Fintype J] in
/-- Peeling one draw of class `j` out of the bundled tape draw. -/
private theorem evalDist_tapeOn_bind_update_succ {β : Type} [MeasurableSpace β] (j : J)
    (m : J → ℕ) (n : ℕ) :
    ∀ js : List J, js.Nodup → j ∈ js →
      ∀ f : ((k : J) → List (R k)) → ProbComp β,
      𝒟[tapeOn R (Function.update m j (n + 1)) js >>= f] =
        𝒟[(do let u ← ($ᵗ R j : ProbComp (R j))
              let L ← tapeOn R (Function.update m j n) js
              f (Function.update L j (u :: L j)))] := by
  let _ : MeasurableSpace ((k : J) → List (R k)) := ⊤
  let _ : DiscreteMeasurableSpace ((k : J) → List (R k)) := ⟨fun _ => trivial⟩
  intro js
  induction js with
  | nil => intro _ hj; exact absurd hj (by simp)
  | cons j' js' ih =>
      intro hnd hj f
      have hnd' : js'.Nodup := (List.nodup_cons.mp hnd).2
      rcases eq_or_ne j' j with rfl | hne
      · have hjs : j' ∉ js' := (List.nodup_cons.mp hnd).1
        have hcong : tapeOn R (Function.update m j' (n + 1)) js'
            = tapeOn R (Function.update m j' n) js' :=
          tapeOn_congr js' fun k hk => by
            have hk' : k ≠ j' := fun h => hjs (by rwa [h] at hk)
            rw [Function.update_of_ne hk', Function.update_of_ne hk']
        simp only [tapeOn, hcong, Function.update_self, tapeList_succ, bind_assoc, pure_bind,
          Function.update_idem]
      · let _ : MeasurableSpace (List (R j')) := ⊤
        let _ : DiscreteMeasurableSpace (List (R j')) := ⟨fun _ => trivial⟩
        let _ : MeasurableSpace (R j) := ⊤
        let _ : DiscreteMeasurableSpace (R j) := ⟨fun _ => trivial⟩
        have hjs' : j ∈ js' := by
          rcases List.mem_cons.mp hj with h | h
          · exact absurd h.symm hne
          · exact h
        have hbody : ∀ (L : (k : J) → List (R k)) (u : R j) (l' : List (R j')),
            Function.update (Function.update L j (u :: L j)) j' l'
              = Function.update (Function.update L j' l') j
                  (u :: (Function.update L j' l') j) := fun L u l' => by
          rw [Function.update_of_ne (Ne.symm hne) l' L]
          exact Function.update_comm (Ne.symm hne) _ _ L
        simp only [tapeOn, Function.update_of_ne hne, bind_assoc, pure_bind]
        have step1 : 𝒟[tapeList (R j') (m j') >>= fun l' =>
              tapeOn R (Function.update m j (n + 1)) js' >>= fun L =>
                f (Function.update L j' l')] =
            𝒟[tapeList (R j') (m j') >>= fun l' =>
              ($ᵗ R j : ProbComp (R j)) >>= fun u =>
                tapeOn R (Function.update m j n) js' >>= fun L =>
                  f (Function.update (Function.update L j (u :: L j)) j' l')] := by
          rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
          refine Measure.bind_congr_right ?_
          filter_upwards [] with l'
          exact ih hnd' hjs' fun L => f (Function.update L j' l')
        rw [step1, evalDist_bind_bind_swap_of_countable]
        simp only [hbody]

omit [Fintype J] in
/-- A class whose tape is empty contributes nothing: inserting the empty tape at that class
after the draw changes no distribution. -/
private theorem evalDist_tapeOn_bind_update_zero {β : Type} [MeasurableSpace β] (j : J)
    (m : J → ℕ) :
    ∀ js : List J, j ∈ js → ∀ f : ((k : J) → List (R k)) → ProbComp β,
      𝒟[tapeOn R (Function.update m j 0) js >>= f] =
        𝒟[tapeOn R (Function.update m j 0) js >>= fun L => f (Function.update L j [])] := by
  let _ : MeasurableSpace ((k : J) → List (R k)) := ⊤
  let _ : DiscreteMeasurableSpace ((k : J) → List (R k)) := ⟨fun _ => trivial⟩
  intro js
  induction js with
  | nil => intro hj; exact absurd hj (by simp)
  | cons j' js' ih =>
      intro hj f
      rcases eq_or_ne j' j with rfl | hne
      · simp only [tapeOn, Function.update_self, tapeList_zero, bind_assoc, pure_bind,
          Function.update_idem]
      · let _ : MeasurableSpace (List (R j')) := ⊤
        let _ : DiscreteMeasurableSpace (List (R j')) := ⟨fun _ => trivial⟩
        have hjs' : j ∈ js' := by
          rcases List.mem_cons.mp hj with h | h
          · exact absurd h.symm hne
          · exact h
        have hbody : ∀ (L : (k : J) → List (R k)) (l' : List (R j')),
            Function.update (Function.update L j' l') j []
              = Function.update (Function.update L j []) j' l' :=
          fun L l' => Function.update_comm hne l' [] L
        simp only [tapeOn, bind_assoc, pure_bind]
        rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
        refine Measure.bind_congr_right ?_
        filter_upwards [] with l'
        simp only [hbody]
        exact ih hjs' fun L => f (Function.update L j' l')

/-- **Peeling one draw of class `j` out of the bundled tape family.** -/
theorem evalDist_tapeFamily_bind_of_succ {β : Type} [MeasurableSpace β] (j : J) (m : J → ℕ)
    (n : ℕ) (hm : m j = n + 1) (f : ((k : J) → List (R k)) → ProbComp β) :
    𝒟[tapeFamily R m >>= f] =
      𝒟[(do let u ← ($ᵗ R j : ProbComp (R j))
            let L ← tapeFamily R (Function.update m j n)
            f (Function.update L j (u :: L j)))] := by
  have hmj : Function.update m j (n + 1) = m := by
    rw [← hm]; exact Function.update_eq_self j m
  have key := evalDist_tapeOn_bind_update_succ (R := R) j m n Finset.univ.toList
    (Finset.nodup_toList _) (Finset.mem_toList.mpr (Finset.mem_univ j)) f
  rw [hmj] at key
  simpa only [tapeFamily] using key

/-- **A class with no tape entries.** Inserting its empty tape after the draw changes no
distribution. -/
theorem evalDist_tapeFamily_bind_of_zero {β : Type} [MeasurableSpace β] (j : J) (m : J → ℕ)
    (hm : m j = 0) (f : ((k : J) → List (R k)) → ProbComp β) :
    𝒟[tapeFamily R m >>= f] =
      𝒟[tapeFamily R m >>= fun L => f (Function.update L j [])] := by
  have hmj : Function.update m j 0 = m := by
    rw [← hm]; exact Function.update_eq_self j m
  have key := evalDist_tapeOn_bind_update_zero (R := R) j m Finset.univ.toList
    (Finset.mem_toList.mpr (Finset.mem_univ j)) f
  rw [hmj] at key
  simpa only [tapeFamily] using key

omit [Fintype J] [DecidableEq J] [∀ j, SampleableType (R j)] in
/-- Uniform sampling transported across an equality of types, before a common continuation. -/
private theorem evalDist_uniformSample_bind_cast {A B γ : Type} [hA : SampleableType A]
    [hB : SampleableType B] (h : A = B) [MeasurableSpace γ] (g : A → ProbComp γ) :
    𝒟[($ᵗ A : ProbComp A) >>= g] = 𝒟[($ᵗ B : ProbComp B) >>= fun u => g (cast h.symm u)] := by
  subst h
  let _ : MeasurableSpace A := ⊤
  let _ : DiscreteMeasurableSpace A := ⟨fun _ => trivial⟩
  let _ : MeasurableSingletonClass A := ⟨fun _ => trivial⟩
  have hu : 𝒟[(@uniformSample A hA : ProbComp A)] = 𝒟[(@uniformSample A hB : ProbComp A)] := by
    rw [@SampleableType.evalDist_uniformSample A hA _ _,
      @SampleableType.evalDist_uniformSample A hB _ _]
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete, hu]
  simp

omit [DecidableEq ι] [Fintype J] [DecidableEq J] [∀ j, SampleableType (R j)] in
private theorem length_of_mem_support_tapeList (A : Type) [SampleableType A] (n : ℕ)
    (l : List A) (hl : l ∈ support (tapeList A n)) : l.length = n := by
  rw [tapeList_eq_map_answerTape A n, support_map] at hl
  obtain ⟨v, -, rfl⟩ := hl
  exact List.length_ofFn

omit [Fintype J] in
private theorem length_of_mem_support_tapeOn (m : J → ℕ) :
    ∀ (js : List J), js.Nodup → ∀ L ∈ support (tapeOn R m js), ∀ j ∈ js, (L j).length = m j
  | [], _, _, _, _, hj => absurd hj (by simp)
  | j' :: js', hnd, L, hL, j, hj => by
      rw [tapeOn, mem_support_bind_iff] at hL
      obtain ⟨l, hl, hL⟩ := hL
      rw [mem_support_bind_iff] at hL
      obtain ⟨L', hL', hL⟩ := hL
      rw [support_pure, Set.mem_singleton_iff] at hL
      subst hL
      rcases List.mem_cons.mp hj with rfl | hj'
      · rw [Function.update_self]
        exact length_of_mem_support_tapeList (R j) (m j) l hl
      · have hne : j ≠ j' := fun hh => (List.nodup_cons.mp hnd).1 (hh ▸ hj')
        rw [Function.update_of_ne hne]
        exact length_of_mem_support_tapeOn m js' (List.nodup_cons.mp hnd).2 L' hL' j hj'

/-- **A drawn tape family has the lengths it was asked for.** This is what lets a caller
discharge the per-class query bounds of the position lemmas of `ClassIndexedTape/Position.lean`
against an event of `tapeFamily`, and so compose them with the transports there. -/
theorem length_of_mem_support_tapeFamily (m : J → ℕ) {L : (j : J) → List (R j)}
    (hL : L ∈ support (tapeFamily R m)) (j : J) : (L j).length = m j :=
  length_of_mem_support_tapeOn m Finset.univ.toList (Finset.nodup_toList _) L hL j
    (Finset.mem_toList.mpr (Finset.mem_univ j))

/-! ## Marginal and joint laws -/

omit [DecidableEq ι] in
/-- **The marginal law of one class's tape.** Reading off class `j` from the bundled family is
drawing that class's tape on its own. -/
theorem evalDist_tapeFamily_bind_eval {β : Type} [MeasurableSpace β] (j : J) :
    ∀ (m : J → ℕ) (f : List (R j) → ProbComp β),
      letI : MeasurableSpace ((k : J) → List (R k)) := ⊤
      𝒟[tapeFamily R m >>= fun L => f (L j)] = 𝒟[tapeList (R j) (m j) >>= f] := by
  let _ : MeasurableSpace ((k : J) → List (R k)) := ⊤
  let _ : DiscreteMeasurableSpace ((k : J) → List (R k)) := ⟨fun _ => trivial⟩
  let _ : MeasurableSpace (List (R j)) := ⊤
  let _ : DiscreteMeasurableSpace (List (R j)) := ⟨fun _ => trivial⟩
  let _ : MeasurableSpace (R j) := ⊤
  let _ : DiscreteMeasurableSpace (R j) := ⟨fun _ => trivial⟩
  suffices h : ∀ k (m : J → ℕ), m j = k → ∀ f : List (R j) → ProbComp β,
      𝒟[tapeFamily R m >>= fun L => f (L j)] = 𝒟[tapeList (R j) k >>= f] from
    fun m f => h (m j) m rfl f
  intro k
  induction k with
  | zero =>
      intro m hk f
      rw [evalDist_tapeFamily_bind_of_zero j m hk (fun L => f (L j))]
      simp only [Function.update_self, tapeList_zero, pure_bind]
      rw [_root_.evalDist_bind_const]
      rw [measure_univ, one_smul]
  | succ n ih =>
      intro m hk f
      rw [evalDist_tapeFamily_bind_of_succ j m n hk (fun L => f (L j))]
      simp only [Function.update_self, tapeList_succ, bind_assoc]
      rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
      refine Measure.bind_congr_right ?_
      filter_upwards [] with u
      exact ih (Function.update m j n) (by simp) (fun l => f (u :: l))

omit [DecidableEq ι] in
/-- **The joint law of two distinct classes' tapes.** They are independent, so reading off both
is drawing the two tapes one after the other. -/
theorem evalDist_tapeFamily_bind_eval₂ {β : Type} [MeasurableSpace β] {j j' : J} (hne : j ≠ j') :
    ∀ (m : J → ℕ) (f : List (R j) → List (R j') → ProbComp β),
      letI : MeasurableSpace ((k : J) → List (R k)) := ⊤
      𝒟[tapeFamily R m >>= fun L => f (L j) (L j')] =
        𝒟[tapeList (R j) (m j) >>= fun l => tapeList (R j') (m j') >>= fun l' => f l l'] := by
  let _ : MeasurableSpace ((k : J) → List (R k)) := ⊤
  let _ : DiscreteMeasurableSpace ((k : J) → List (R k)) := ⟨fun _ => trivial⟩
  let _ : MeasurableSpace (List (R j)) := ⊤
  let _ : DiscreteMeasurableSpace (List (R j)) := ⟨fun _ => trivial⟩
  let _ : MeasurableSpace (R j) := ⊤
  let _ : DiscreteMeasurableSpace (R j) := ⟨fun _ => trivial⟩
  suffices h : ∀ k (m : J → ℕ), m j = k → ∀ f : List (R j) → List (R j') → ProbComp β,
      𝒟[tapeFamily R m >>= fun L => f (L j) (L j')] =
        𝒟[tapeList (R j) k >>= fun l => tapeList (R j') (m j') >>= fun l' => f l l'] from
    fun m f => h (m j) m rfl f
  intro k
  induction k with
  | zero =>
      intro m hk f
      rw [evalDist_tapeFamily_bind_of_zero j m hk (fun L => f (L j) (L j'))]
      simp only [Function.update_self, Function.update_of_ne (Ne.symm hne), tapeList_zero,
        pure_bind]
      exact evalDist_tapeFamily_bind_eval j' m (fun l' => f [] l')
  | succ n ih =>
      intro m hk f
      rw [evalDist_tapeFamily_bind_of_succ j m n hk (fun L => f (L j) (L j'))]
      simp only [Function.update_self, Function.update_of_ne (Ne.symm hne), tapeList_succ,
        bind_assoc]
      rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
      refine Measure.bind_congr_right ?_
      filter_upwards [] with u
      have := ih (Function.update m j n) (by simp) (fun l l' => f (u :: l) l')
      rwa [Function.update_of_ne (Ne.symm hne)] at this

omit [DecidableEq ι] in
/-- **An event of one class's tape is an event of that class's `answerTape`.** This is the
shape the product bounds of `IndepProductEvents.lean` are stated for. -/
theorem evalDist_tapeFamily_setOf_eq [∀ j, MeasurableSpace (R j)]
    [∀ j, DiscreteMeasurableSpace (R j)] (j : J) (m : J → ℕ) (S : Set (List (R j))) :
    letI : MeasurableSpace ((k : J) → List (R k)) := ⊤
    𝒟[tapeFamily R m] {L | L j ∈ S} = 𝒟[answerTape (R j) (m j)] {v | List.ofFn v ∈ S} := by
  let _ : MeasurableSpace ((k : J) → List (R k)) := ⊤
  let _ : DiscreteMeasurableSpace ((k : J) → List (R k)) := ⟨fun _ => trivial⟩
  let _ : MeasurableSpace (List (R j)) := ⊤
  let _ : DiscreteMeasurableSpace (List (R j)) := ⟨fun _ => trivial⟩
  have h1 : 𝒟[(fun L => L j) <$> tapeFamily R m] = 𝒟[List.ofFn <$> answerTape (R j) (m j)] := by
    rw [map_eq_bind_pure_comp, Function.comp_def, ← tapeList_eq_map_answerTape]
    simpa using evalDist_tapeFamily_bind_eval (R := R) (β := List (R j)) j m pure
  rw [evalDist_map_of_discrete, evalDist_map_of_discrete] at h1
  have h2 := congrArg (fun μ : Measure (List (R j)) => μ S) h1
  simpa only [Measure.map_apply (f := fun L : (k : J) → List (R k) => L j)
      Measurable.of_discrete MeasurableSet.of_discrete,
    Measure.map_apply (f := fun v : Fin (m j) → R j => List.ofFn v)
      Measurable.of_discrete MeasurableSet.of_discrete, Set.preimage] using h2

omit [DecidableEq ι] [Fintype J] [DecidableEq J] [∀ j, SampleableType (R j)] in
/-- A tuple transported across an equality of its entry type, read as a list. -/
private theorem cast_list_ofFn {A B : Type} (h : A = B) {n : ℕ} (v : Fin n → A) :
    cast (congrArg List h) (List.ofFn v) = List.ofFn fun i => cast h (v i) := by
  subst h; simp

omit [DecidableEq ι] [Fintype J] [DecidableEq J] [∀ j, SampleableType (R j)] in
/-- The law of a tape does not depend on which uniform sampler its entry type carries. -/
private theorem evalDist_answerTape_congr_instance (A : Type) (h₁ h₂ : SampleableType A)
    (n : ℕ) [MeasurableSpace A] [MeasurableSingletonClass A] :
    𝒟[(@answerTape A h₁ n)] = 𝒟[(@answerTape A h₂ n)] := by
  rw [@evalDist_answerTape A h₁ n _, @evalDist_answerTape A h₂ n _]
  congr 1
  funext _
  rw [@SampleableType.evalDist_uniformSample A h₁ _ _,
    @SampleableType.evalDist_uniformSample A h₂ _ _]

omit [DecidableEq ι] [Fintype J] [DecidableEq J] [∀ j, SampleableType (R j)] in
/-- A tape drawn at one entry type, transported across an equality of entry types, before a
common continuation. -/
private theorem evalDist_answerTape_bind_cast {A B γ : Type} [h₁ : SampleableType A]
    [h₂ : SampleableType B] (hAB : A = B) [MeasurableSpace γ] (n : ℕ)
    (g : (Fin n → B) → ProbComp γ) :
    𝒟[answerTape A n >>= fun v => g fun i => cast hAB (v i)] = 𝒟[answerTape B n >>= g] := by
  subst hAB
  let _ : MeasurableSpace A := ⊤
  let _ : MeasurableSingletonClass A := ⟨fun _ => trivial⟩
  simp only [cast_eq]
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete,
    evalDist_answerTape_congr_instance A h₁ h₂ n]

omit [DecidableEq ι] in
/-- **An event of two distinct classes' tapes is an event of a single `answerTape` over the
summed index.** The tape of class `j` occupies the first `m j` coordinates and the tape of
class `j'` the last `m j'`, so a caller reaches them through `Fin.castAdd` and `Fin.natAdd` —
the shape the two-family bounds of `IndepProductEvents.lean` and of the covering files are
stated for.

The two classes must carry the *same* answer type, because a single `answerTape` has one entry
type; `hR` is that identification, and the tape of class `j'` enters the left-hand event
transported along it. -/
theorem evalDist_tapeFamily_setOf_eq₂ [∀ j, MeasurableSpace (R j)]
    [∀ j, DiscreteMeasurableSpace (R j)] {j j' : J} (hne : j ≠ j') (hR : R j' = R j)
    (m : J → ℕ) (P : List (R j) → List (R j) → Prop) :
    letI : MeasurableSpace ((k : J) → List (R k)) := ⊤
    𝒟[tapeFamily R m] {L | P (L j) (cast (congrArg List hR) (L j'))} =
      𝒟[answerTape (R j) (m j + m j')]
        {w | P (List.ofFn fun i => w (Fin.castAdd (m j') i))
            (List.ofFn fun i => w (Fin.natAdd (m j) i))} := by
  let _ : MeasurableSpace ((k : J) → List (R k)) := ⊤
  let _ : DiscreteMeasurableSpace ((k : J) → List (R k)) := ⟨fun _ => trivial⟩
  let _ : MeasurableSpace (List (R j) × List (R j)) := ⊤
  let _ : DiscreteMeasurableSpace (List (R j) × List (R j)) := ⟨fun _ => trivial⟩
  set obs : (Fin (m j + m j') → R j) → List (R j) × List (R j) := fun w =>
    (List.ofFn fun i => w (Fin.castAdd (m j') i), List.ofFn fun i => w (Fin.natAdd (m j) i))
    with hobs
  have key : 𝒟[tapeFamily R m >>= fun L =>
        (pure (L j, cast (congrArg List hR) (L j')) : ProbComp (List (R j) × List (R j)))] =
      𝒟[obs <$> answerTape (R j) (m j + m j')] :=
    calc 𝒟[tapeFamily R m >>= fun L =>
          (pure (L j, cast (congrArg List hR) (L j')) : ProbComp (List (R j) × List (R j)))]
        = 𝒟[tapeList (R j) (m j) >>= fun l => tapeList (R j') (m j') >>= fun l' =>
              (pure (l, cast (congrArg List hR) l') : ProbComp (List (R j) × List (R j)))] :=
          evalDist_tapeFamily_bind_eval₂ (R := R) hne m
            (fun l l' => pure (l, cast (congrArg List hR) l'))
      _ = 𝒟[answerTape (R j) (m j) >>= fun u => answerTape (R j') (m j') >>= fun v =>
              (pure (List.ofFn u, List.ofFn fun i => cast hR (v i)) :
                ProbComp (List (R j) × List (R j)))] := by
          simp only [tapeList_eq_map_answerTape, map_eq_bind_pure_comp, Function.comp_def,
            bind_assoc, pure_bind]
          simp only [cast_list_ofFn hR]
      _ = 𝒟[answerTape (R j) (m j) >>= fun u => answerTape (R j) (m j') >>= fun v =>
              (pure (List.ofFn u, List.ofFn v) : ProbComp (List (R j) × List (R j)))] := by
          rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
          refine Measure.bind_congr_right ?_
          filter_upwards [] with u
          exact evalDist_answerTape_bind_cast hR (m j') fun v => pure (List.ofFn u, List.ofFn v)
      _ = 𝒟[obs <$> (do let u ← answerTape (R j) (m j)
                        let v ← answerTape (R j) (m j')
                        (pure (Fin.append u v) : ProbComp (Fin (m j + m j') → R j)))] := by
          simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind, hobs,
            Fin.append_left, Fin.append_right]
      _ = 𝒟[obs <$> answerTape (R j) (m j + m j')] := by
          rw [evalDist_map_of_discrete, evalDist_map_of_discrete,
            evalDist_answerTape_append (m j) (m j')]
  have hmap1 : 𝒟[tapeFamily R m >>= fun L =>
        (pure (L j, cast (congrArg List hR) (L j')) : ProbComp (List (R j) × List (R j)))] =
      (𝒟[tapeFamily R m]).map (fun L => (L j, cast (congrArg List hR) (L j'))) := by
    rw [← evalDist_map_of_discrete (tapeFamily R m)
      (fun L => (L j, cast (congrArg List hR) (L j')))]
    simp only [map_eq_bind_pure_comp, Function.comp_def]
  rw [hmap1, evalDist_map_of_discrete] at key
  have h2 : ((𝒟[tapeFamily R m]).map fun L => (L j, cast (congrArg List hR) (L j')))
        {z | P z.1 z.2} = ((𝒟[answerTape (R j) (m j + m j')]).map obs) {z | P z.1 z.2} := by
    rw [key]
  rwa [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
    Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete] at h2

/-! ## The duplicated interface on one shared cache -/

section Duplicated

/-- Collapsing the duplication: either copy of a query is the same query of `spec`. -/
def dupCollapse (spec : OracleSpec.{0, 0} ι) : QueryImpl (spec + spec) (OracleComp spec) :=
  QueryImpl.id' spec + QueryImpl.id' spec

variable [∀ t : spec.Domain, SampleableType (spec.Range t)]

variable (spec) in
/-- The lazy random oracle answering both copies of the duplicated interface `spec + spec` out
of **one** shared cache. The two copies see and extend the same answer table, and the handler
keeps no trace of which copy a query came through: the call site is a distinction in the
program's syntax, not in the run (`simulateQ_dupRandomOracle_eq`). What consumes it is the
tape-class map `τ`, which may send the two copies of a point to different classes. -/
def dupRandomOracle : QueryImpl (spec + spec) (StateT spec.QueryCache ProbComp) :=
  spec.randomOracle + spec.randomOracle

theorem dupRandomOracle_apply_inl (t : spec.Domain) :
    dupRandomOracle spec (Sum.inl t) = spec.randomOracle t := by
  unfold dupRandomOracle; rfl

theorem dupRandomOracle_apply_inr (t : spec.Domain) :
    dupRandomOracle spec (Sum.inr t) = spec.randomOracle t := by
  unfold dupRandomOracle; rfl

/-- **The duplication changes no distribution.** Running a computation over the duplicated
interface under the shared lazy random oracle is running its collapse under the lazy random
oracle: the two copies are one oracle, and only the call site is recorded. -/
theorem simulateQ_dupRandomOracle_eq {α : Type} (oa : OracleComp (spec + spec) α) :
    simulateQ (dupRandomOracle spec) oa
      = simulateQ spec.randomOracle (simulateQ (dupCollapse spec) oa) := by
  have hc : spec.randomOracle ∘ₛ dupCollapse spec = dupRandomOracle spec := by
    funext t
    cases t <;> simp [dupCollapse, dupRandomOracle_apply_inl, dupRandomOracle_apply_inr]
  rw [← hc, QueryImpl.simulateQ_compose]

end Duplicated

/-! ## The class-indexed tape oracle -/

section TapeImpl

variable [∀ t : spec.Domain, SampleableType (spec.Range t)]

/-- One step of the class-indexed tape oracle at the point `t`, whose tape class is `j` and
whose answer type is therefore `R j`. A cached point is answered from the cache, a fresh point
takes the head of the tape of class `j`, and once that tape is exhausted the answer is sampled
uniformly. -/
def tapeStep (R : J → Type) (j : J) (t : spec.Domain) (h : spec.Range t = R j) :
    StateT (spec.QueryCache × ((k : J) → List (R k))) ProbComp (spec.Range t) :=
  StateT.mk fun s =>
    match s.1 t with
    | some u => pure (u, s)
    | none => match s.2 j with
        | u :: l => pure (cast h.symm u,
            (s.1.cacheQuery t (cast h.symm u), Function.update s.2 j l))
        | [] => (fun u => (u, (s.1.cacheQuery t u, s.2))) <$> ($ᵗ spec.Range t : ProbComp _)

/-- **The class-indexed tape oracle.** Over the duplicated interface `spec + spec` it answers
out of one shared cache, taking each fresh answer off the tape of the query's class. -/
def tapeCachingImplClass (R : J → Type) (τ : (spec + spec).Domain → J)
    (hR : ∀ t : (spec + spec).Domain, (spec + spec).Range t = R (τ t)) :
    QueryImpl (spec + spec) (StateT (spec.QueryCache × ((k : J) → List (R k))) ProbComp)
  | .inl t => tapeStep R (τ (Sum.inl t)) t (hR (Sum.inl t))
  | .inr t => tapeStep R (τ (Sum.inr t)) t (hR (Sum.inr t))

variable {τ : (spec + spec).Domain → J}
  {hR : ∀ t : (spec + spec).Domain, (spec + spec).Range t = R (τ t)}

omit [Fintype J] [∀ j, SampleableType (R j)] in
theorem tapeCachingImplClass_apply_inl (t : spec.Domain) :
    tapeCachingImplClass R τ hR (Sum.inl t) = tapeStep R (τ (Sum.inl t)) t (hR (Sum.inl t)) := by
  unfold tapeCachingImplClass; rfl

omit [Fintype J] [∀ j, SampleableType (R j)] in
theorem tapeCachingImplClass_apply_inr (t : spec.Domain) :
    tapeCachingImplClass R τ hR (Sum.inr t) = tapeStep R (τ (Sum.inr t)) t (hR (Sum.inr t)) := by
  unfold tapeCachingImplClass; rfl

variable {j : J} {t : spec.Domain} {h : spec.Range t = R j} {c : spec.QueryCache}
  {L : (k : J) → List (R k)}

omit [Fintype J] [∀ j, SampleableType (R j)] in
theorem tapeStep_run_some {u : spec.Range t} (hc : c t = some u) :
    (tapeStep R j t h).run (c, L) = pure (u, (c, L)) := by
  simp [tapeStep, hc]

omit [Fintype J] [∀ j, SampleableType (R j)] in
theorem tapeStep_run_cons {u : R j} {l : List (R j)} (hc : c t = none) (hL : L j = u :: l) :
    (tapeStep R j t h).run (c, L) =
      pure (cast h.symm u, (c.cacheQuery t (cast h.symm u), Function.update L j l)) := by
  simp [tapeStep, hc, hL]

omit [Fintype J] [∀ j, SampleableType (R j)] in
theorem tapeStep_run_nil (hc : c t = none) (hL : L j = []) :
    (tapeStep R j t h).run (c, L) =
      (fun u => (u, (c.cacheQuery t u, L))) <$> ($ᵗ spec.Range t : ProbComp _) := by
  simp [tapeStep, hc, hL]

omit [Fintype J] [∀ j, SampleableType (R j)] in
private theorem tapeStep_run_update_nil (hc : c t = none) (L : (k : J) → List (R k)) :
    (tapeStep R j t h).run (c, Function.update L j []) =
      (fun u => (u, (c.cacheQuery t u, Function.update L j []))) <$>
        ($ᵗ spec.Range t : ProbComp _) :=
  tapeStep_run_nil hc (Function.update_self j [] L)

omit [Fintype J] [∀ j, SampleableType (R j)] in
private theorem tapeStep_run_update_cons (hc : c t = none) (L : (k : J) → List (R k)) (u : R j) :
    (tapeStep R j t h).run (c, Function.update L j (u :: L j)) =
      pure (cast h.symm u, (c.cacheQuery t (cast h.symm u), L)) := by
  rw [tapeStep_run_cons hc (Function.update_self j (u :: L j) L), Function.update_idem,
    Function.update_eq_self]

end TapeImpl

/-! ## Forwarding private sampling -/

section Forwarded

variable [∀ t : spec.Domain, SampleableType (spec.Range t)]

variable (spec) in
/-- The shared lazy random oracle of `dupRandomOracle` beside a forwarded private uniform
oracle: a query of the `unifSpec` summand is passed to `ProbComp` and leaves the cache as it
is. -/
abbrev dupRandomOracleFwd :
    QueryImpl (unifSpec + (spec + spec)) (StateT spec.QueryCache ProbComp) :=
  unifFwdImpl spec + dupRandomOracle spec

/-- The class-indexed tape oracle of `tapeCachingImplClass` beside a forwarded private uniform
oracle: a query of the `unifSpec` summand is passed to `ProbComp` and leaves the cache and every
tape as they are. -/
abbrev tapeImplFwd (R : J → Type) (τ : (spec + spec).Domain → J)
    (hR : ∀ t : (spec + spec).Domain, (spec + spec).Range t = R (τ t)) :
    QueryImpl (unifSpec + (spec + spec))
      (StateT (spec.QueryCache × ((k : J) → List (R k))) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (spec.QueryCache × ((k : J) → List (R k))) ProbComp) +
    tapeCachingImplClass R τ hR

end Forwarded

/-! ## The identification -/

section Identification

variable [∀ t : spec.Domain, SampleableType (spec.Range t)]
  {τ : (spec + spec).Domain → J}
  {hR : ∀ t : (spec + spec).Domain, (spec + spec).Range t = R (τ t)}

/-- One query step of the identification, at a point `t` of tape class `j`: a lazy query
followed by a continuation `F` matches a tape step followed by a continuation `G`, once `F` and
`G` agree averaged over a tape family of every length assignment. -/
private theorem evalDist_run_query_step {β : Type} [MeasurableSpace β] (j : J)
    (t : spec.Domain) (h : spec.Range t = R j) (F : spec.Range t → spec.QueryCache → ProbComp β)
    (G : spec.Range t → spec.QueryCache × ((k : J) → List (R k)) → ProbComp β)
    (c : spec.QueryCache) (m : J → ℕ)
    (ih : ∀ (u : spec.Range t) (c' : spec.QueryCache) (m' : J → ℕ),
      𝒟[F u c'] = 𝒟[tapeFamily R m' >>= fun L => G u (c', L)]) :
    𝒟[(spec.randomOracle t).run c >>= fun p => F p.1 p.2] =
      𝒟[tapeFamily R m >>= fun L => (tapeStep R j t h).run (c, L) >>= fun p => G p.1 p.2] := by
  let _ : MeasurableSpace (spec.Range t) := ⊤
  let _ : DiscreteMeasurableSpace (spec.Range t) := ⟨fun _ => trivial⟩
  let _ : MeasurableSpace (R j) := ⊤
  let _ : DiscreteMeasurableSpace (R j) := ⟨fun _ => trivial⟩
  let _ : MeasurableSpace ((k : J) → List (R k)) := ⊤
  let _ : DiscreteMeasurableSpace ((k : J) → List (R k)) := ⟨fun _ => trivial⟩
  rcases hc : c t with _ | u₀
  · rw [randomOracle.run_eq, hc]
    rcases hm : m j with _ | n
    · rw [evalDist_tapeFamily_bind_of_zero j m hm]
      simp only [tapeStep_run_update_nil hc, map_eq_bind_pure_comp,
        Function.comp_def, bind_assoc, pure_bind]
      rw [evalDist_bind_bind_swap_of_countable]
      rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
      refine Measure.bind_congr_right ?_
      filter_upwards [] with u
      rw [← evalDist_tapeFamily_bind_of_zero j m hm (fun L => G u (c.cacheQuery t u, L))]
      exact ih u (c.cacheQuery t u) m
    · rw [evalDist_tapeFamily_bind_of_succ j m n hm]
      simp only [tapeStep_run_update_cons hc, bind_assoc, pure_bind]
      rw [evalDist_uniformSample_bind_cast (γ := β) h]
      rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
      refine Measure.bind_congr_right ?_
      filter_upwards [] with u
      exact ih (cast h.symm u) (c.cacheQuery t (cast h.symm u)) (Function.update m j n)
  · rw [randomOracle.run_eq, hc, pure_bind]
    simp only [tapeStep_run_some hc, pure_bind]
    exact ih u₀ c m

/-- **The duplicated lazy random oracle is the class-indexed tape oracle averaged over a
bundled iid tape family.** For every assignment `m` of tape lengths to classes, running `oa`
under the shared lazy random oracle from cache `c` has the same joint distribution of output
and final cache as drawing one independent uniform tape per class, running `oa` under
`tapeCachingImplClass` from `c` with those tapes, and forgetting the unconsumed tapes. -/
theorem evalDist_run_dupRandomOracle_eq_tapeFamily {α : Type}
    (oa : OracleComp (spec + spec) α) (c : spec.QueryCache) (m : J → ℕ) :
    letI : MeasurableSpace (α × spec.QueryCache) := ⊤
    𝒟[(simulateQ (dupRandomOracle spec) oa).run c] =
      𝒟[(do let L ← tapeFamily R m
            let z ← (simulateQ (tapeCachingImplClass R τ hR) oa).run (c, L)
            return (z.1, z.2.1))] := by
  let _ : MeasurableSpace (α × spec.QueryCache) := ⊤
  let _ : MeasurableSpace ((k : J) → List (R k)) := ⊤
  induction oa using OracleComp.inductionOn generalizing c m with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    rw [_root_.evalDist_bind_const]
    rw [measure_univ, one_smul]
  | query_bind t k ih =>
    have hredL : (simulateQ (dupRandomOracle spec)
          (liftM ((spec + spec).query t) >>= k)).run c =
        ((dupRandomOracle spec t).run c) >>= fun p =>
          (simulateQ (dupRandomOracle spec) (k p.1)).run p.2 := by
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have hredR : ∀ L : (k : J) → List (R k),
        (simulateQ (tapeCachingImplClass R τ hR)
            (liftM ((spec + spec).query t) >>= k)).run (c, L) =
          ((tapeCachingImplClass R τ hR t).run (c, L)) >>= fun p =>
            (simulateQ (tapeCachingImplClass R τ hR) (k p.1)).run p.2 := fun L => by
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [hredL]
    simp only [hredR, bind_assoc]
    rcases t with t | t
    · rw [dupRandomOracle_apply_inl, tapeCachingImplClass_apply_inl]
      exact evalDist_run_query_step _ t (hR (Sum.inl t))
        (fun u c' => (simulateQ (dupRandomOracle spec) (k u)).run c')
        (fun u s => (simulateQ (tapeCachingImplClass R τ hR) (k u)).run s >>= fun z =>
          pure (z.1, z.2.1)) c m ih
    · rw [dupRandomOracle_apply_inr, tapeCachingImplClass_apply_inr]
      exact evalDist_run_query_step _ t (hR (Sum.inr t))
        (fun u c' => (simulateQ (dupRandomOracle spec) (k u)).run c')
        (fun u s => (simulateQ (tapeCachingImplClass R τ hR) (k u)).run s >>= fun z =>
          pure (z.1, z.2.1)) c m ih

variable (τ hR) in
/-- **The duplicated lazy random oracle with private sampling forwarded is the class-indexed
tape oracle with private sampling forwarded, averaged over a bundled iid tape family.** For every
assignment `m` of tape lengths to classes, running `oa` under `dupRandomOracleFwd` from cache `c`
has the same joint distribution of output and final cache as drawing one independent uniform
tape per class, running `oa` under `tapeImplFwd` from `c` with those tapes, and forgetting the
unconsumed tapes. A private uniform query touches neither the cache nor any tape. -/
theorem evalDist_run_dupRandomOracleFwd_eq_tapeFamily {α : Type}
    (oa : OracleComp (unifSpec + (spec + spec)) α) (c : spec.QueryCache) (m : J → ℕ) :
    letI : MeasurableSpace (α × spec.QueryCache) := ⊤
    𝒟[(simulateQ (dupRandomOracleFwd spec) oa).run c] =
      𝒟[(do let L ← tapeFamily R m
            let z ← (simulateQ (tapeImplFwd R τ hR) oa).run (c, L)
            return (z.1, z.2.1))] := by
  let _ : MeasurableSpace (α × spec.QueryCache) := ⊤
  let _ : MeasurableSpace ((k : J) → List (R k)) := ⊤
  let _ : DiscreteMeasurableSpace ((k : J) → List (R k)) := ⟨fun _ => trivial⟩
  induction oa using OracleComp.inductionOn generalizing c m with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, pure_bind]
    rw [_root_.evalDist_bind_const]
    rw [measure_univ, one_smul]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
    rcases t with n | t | t
    · simp only [dupRandomOracleFwd, tapeImplFwd, QueryImpl.add_apply_inl, unifFwdImpl,
        QueryImpl.liftTarget_apply, StateT.run_monadLift, bind_assoc, pure_bind]
      let _ : MeasurableSpace (unifSpec.Range n) := ⊤
      let _ : DiscreteMeasurableSpace (unifSpec.Range n) := ⟨fun _ => trivial⟩
      rw [evalDist_bind_bind_swap_of_countable, evalDist_bind_of_discrete,
        evalDist_bind_of_discrete]
      refine Measure.bind_congr_right ?_
      filter_upwards [] with u
      exact ih u c m
    · exact evalDist_run_query_step _ t (hR (Sum.inl t))
        (fun u c' => (simulateQ (dupRandomOracleFwd spec) (k u)).run c')
        (fun u s => (simulateQ (tapeImplFwd R τ hR) (k u)).run s >>= fun z =>
          pure (z.1, z.2.1)) c m ih
    · exact evalDist_run_query_step _ t (hR (Sum.inr t))
        (fun u c' => (simulateQ (dupRandomOracleFwd spec) (k u)).run c')
        (fun u s => (simulateQ (tapeImplFwd R τ hR) (k u)).run s >>= fun z =>
          pure (z.1, z.2.1)) c m ih

end Identification

end AnswerTape
