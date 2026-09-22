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
class's `answerTape`, which is the shape `IndepProductEvents.lean` bounds.
`length_of_mem_support_tapeFamily` says a drawn family has the lengths it was asked for.

The identification is insensitive to `τ`: sending a class to draw from a different class's
tape leaves it true, because the tapes are i.i.d. across classes and it averages over all of
them. Nothing in it ties an answer to a class. What does that is the instrumentation below.

`classPosAux` instruments a run with the class and position each cache entry was answered at,
the entries consumed from each tape, and the queries made at each class. `ClassPosInv` is the
invariant its run maintains, and `exists_pos_of_mem_support_run_tapeCachingImplClass` is the
consequence a caller wants: under *per-class* query bounds, every cache entry is the value of
its class's tape at a position of that tape, and distinct entries sit at distinct
class-position pairs. Per-class bounds are what the split forces: the total-cache-size device
of `Tape.lean` does not survive it, since one class exhausting its tape is consistent with the
other classes' entries making up the total.

The invariant also *pins the class*: `ClassPosInv.cls_tau` records that a point's class is the
class of one of its two call sites, so the existence lemma returns `j = τ (.inl t) ∨ j = τ
(.inr t)` alongside the position. Without it `j` is unconstrained, the caller cannot say which
tape an entry came off, and — since the class also determines the answer type — cannot even
convert the tape value to the type of the cache entry. The lemma therefore also returns that
type equality, and states the entry in cast form rather than as a bare `HEq`.

## Scope

* Nothing here bounds the mass of any tape event.
  `evalDist_run_dupRandomOracle_setOf_le_of_transport` takes that bound as a hypothesis on an
  event of the whole family.
* The bridge to `IndepProductEvents.lean` is built for **one** class at a time
  (`evalDist_tapeFamily_setOf_eq`). An event spanning two classes has its joint law only in
  the bind form `evalDist_tapeFamily_bind_eval₂`; there is no set-level form for a pair, and
  no identification of two `answerTape`s with the single `answerTape` over a summed index
  that the product bounds would then apply to.
* No query bound relates the tape lengths to the number of queries a computation makes: the
  identification holds for every assignment `m`, with the tape oracle sampling freshly once a
  tape runs out. Only the position lemma needs the per-class bounds, and it takes them as
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

private theorem isProbabilityMeasure_uniformSample (A : Type) [SampleableType A] :
    letI : MeasurableSpace A := ⊤
    IsProbabilityMeasure 𝒟[($ᵗ A : ProbComp A)] := by
  let _ : MeasurableSpace A := ⊤
  let _ : MeasurableSingletonClass A := ⟨fun _ => trivial⟩
  rw [SampleableType.evalDist_uniformSample]
  infer_instance

private theorem isProbabilityMeasure_tapeList (A : Type) [SampleableType A] (n : ℕ) :
    letI : MeasurableSpace (List A) := ⊤
    IsProbabilityMeasure 𝒟[tapeList A n] := by
  let _ : MeasurableSpace A := ⊤
  let _ : DiscreteMeasurableSpace A := ⟨fun _ => trivial⟩
  let _ : MeasurableSpace (List A) := ⊤
  induction n with
  | zero => rw [tapeList_zero]; infer_instance
  | succ n ih =>
      rw [tapeList_succ]
      have := isProbabilityMeasure_uniformSample A
      exact evalDist.isProbabilityMeasure_bind _ _ fun _ =>
        evalDist.isProbabilityMeasure_bind _ _ fun _ => inferInstance

omit [Fintype J] in
private theorem isProbabilityMeasure_tapeOn (m : J → ℕ) :
    letI : MeasurableSpace ((j : J) → List (R j)) := ⊤
    ∀ js : List J, IsProbabilityMeasure 𝒟[tapeOn R m js] := by
  let _ : MeasurableSpace ((j : J) → List (R j)) := ⊤
  let _ : DiscreteMeasurableSpace ((j : J) → List (R j)) := ⟨fun _ => trivial⟩
  intro js
  induction js with
  | nil => rw [tapeOn]; infer_instance
  | cons j js ih =>
      let _ : MeasurableSpace (List (R j)) := ⊤
      let _ : DiscreteMeasurableSpace (List (R j)) := ⟨fun _ => trivial⟩
      have := isProbabilityMeasure_tapeList (R j) (m j)
      rw [tapeOn]
      exact evalDist.isProbabilityMeasure_bind _ _ fun _ =>
        evalDist.isProbabilityMeasure_bind _ _ fun _ => inferInstance

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
discharge the per-class query bounds of
`exists_pos_of_mem_support_run_tapeCachingImplClass` against an event of `tapeFamily`, and so
compose the position lemma with `evalDist_run_dupRandomOracle_setOf_le_of_transport`. -/
theorem length_of_mem_support_tapeFamily (m : J → ℕ) {L : (j : J) → List (R j)}
    (hL : L ∈ support (tapeFamily R m)) (j : J) : (L j).length = m j :=
  length_of_mem_support_tapeOn m Finset.univ.toList (Finset.nodup_toList _) L hL j
    (Finset.mem_toList.mpr (Finset.mem_univ j))

/-- The bundled tape family is lossless. -/
theorem isProbabilityMeasure_tapeFamily (m : J → ℕ) :
    letI : MeasurableSpace ((j : J) → List (R j)) := ⊤
    IsProbabilityMeasure 𝒟[tapeFamily R m] :=
  isProbabilityMeasure_tapeOn m _

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
      have := isProbabilityMeasure_tapeFamily (R := R) m
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
theorem evalDist_tapeFamily_setOf_eq (j : J) (m : J → ℕ) (S : Set (List (R j))) :
    letI : MeasurableSpace ((k : J) → List (R k)) := ⊤
    letI : MeasurableSpace (Fin (m j) → R j) := ⊤
    𝒟[tapeFamily R m] {L | L j ∈ S} = 𝒟[answerTape (R j) (m j)] {v | List.ofFn v ∈ S} := by
  let _ : MeasurableSpace ((k : J) → List (R k)) := ⊤
  let _ : DiscreteMeasurableSpace ((k : J) → List (R k)) := ⟨fun _ => trivial⟩
  let _ : MeasurableSpace (Fin (m j) → R j) := ⊤
  let _ : DiscreteMeasurableSpace (Fin (m j) → R j) := ⟨fun _ => trivial⟩
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

/-! ## The identification -/

section Identification

variable [∀ t : spec.Domain, SampleableType (spec.Range t)]
  {τ : (spec + spec).Domain → J}
  {hR : ∀ t : (spec + spec).Domain, (spec + spec).Range t = R (τ t)}

/-- One query step of the identification, at a point `t` of tape class `j`. -/
private theorem evalDist_run_query_step {α : Type} (j : J) (t : spec.Domain)
    (h : spec.Range t = R j) (k : spec.Range t → OracleComp (spec + spec) α)
    (c : spec.QueryCache) (m : J → ℕ)
    (ih : ∀ (u : spec.Range t) (c' : spec.QueryCache) (m' : J → ℕ),
      letI : MeasurableSpace (α × spec.QueryCache) := ⊤
      𝒟[(simulateQ (dupRandomOracle spec) (k u)).run c'] =
        𝒟[(do let L ← tapeFamily R m'
              let z ← (simulateQ (tapeCachingImplClass R τ hR) (k u)).run (c', L)
              return (z.1, z.2.1))]) :
    letI : MeasurableSpace (α × spec.QueryCache) := ⊤
    𝒟[(spec.randomOracle t).run c >>= fun p =>
        (simulateQ (dupRandomOracle spec) (k p.1)).run p.2] =
      𝒟[(do let L ← tapeFamily R m
            let p ← (tapeStep R j t h).run (c, L)
            let z ← (simulateQ (tapeCachingImplClass R τ hR) (k p.1)).run p.2
            return (z.1, z.2.1))] := by
  let _ : MeasurableSpace (α × spec.QueryCache) := ⊤
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
      rw [← evalDist_tapeFamily_bind_of_zero j m hm
        (fun L => (simulateQ (tapeCachingImplClass R τ hR) (k u)).run (c.cacheQuery t u, L) >>=
          fun z => pure (z.1, z.2.1))]
      exact ih u (c.cacheQuery t u) m
    · rw [evalDist_tapeFamily_bind_of_succ j m n hm]
      simp only [tapeStep_run_update_cons hc, bind_assoc, pure_bind]
      rw [evalDist_uniformSample_bind_cast (γ := α × spec.QueryCache) h]
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
    have hprob := isProbabilityMeasure_tapeFamily (R := R) m
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
      exact evalDist_run_query_step _ t (hR (Sum.inl t)) k c m ih
    · rw [dupRandomOracle_apply_inr, tapeCachingImplClass_apply_inr]
      exact evalDist_run_query_step _ t (hR (Sum.inr t)) k c m ih

end Identification

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
/-- A point's class determines the type of its answers. -/
private theorem range_eq_of_cls
    (hRt : ∀ t : (spec + spec).Domain, (spec + spec).Range t = R (τ t))
    {t : spec.Domain} {j : J} (hjt : j = τ (Sum.inl t) ∨ j = τ (Sum.inr t)) :
    spec.Range t = R j := by
  rcases hjt with rfl | rfl
  · exact hRt (Sum.inl t)
  · exact hRt (Sum.inr t)

omit [Fintype J] [∀ j, SampleableType (R j)] in
/-- **Every cache entry of a class-indexed tape run sits at its own position on its own
class's tape.** In a run of `oa` under the instrumented `tapeCachingImplClass` from the empty
cache on the tape family `Lfam`, if every class was queried no more often than its tape is
long, then each cache entry is the value of its class's tape at a position of that tape, and
distinct cached points sit at distinct class-position pairs.

The class is pinned to one of the point's two call sites, which is what lets a caller say
*which* tape an entry came off; with it comes the equality of the point's range with that
class's answer type, so the entry is returned in cast form and needs no further transport.

The per-class query bounds are what exclude the fallback answers sampled after a tape runs
out: such an answer costs its class one query beyond the ones that consumed its whole tape.
A bound on the *total* size of the cache does not exclude them, because one class running out
of tape is consistent with the others' entries making up the total. -/
theorem exists_pos_of_mem_support_run_tapeCachingImplClass {α : Type}
    (Lfam : (k : J) → List (R k)) (oa : OracleComp (spec + spec) α)
    {z : α × (spec.QueryCache × ((k : J) → List (R k))) × ClassPos spec.Domain J}
    (hz : z ∈ support ((simulateQ
      (QueryImpl.extendState (tapeCachingImplClass R τ hR) (classPosAux R τ)) oa).run
        ((∅, Lfam), ⟨fun _ => none, fun _ => none, fun _ => 0, fun _ => 0⟩)))
    (hq : ∀ j, z.2.2.cnt j ≤ (Lfam j).length) :
    (∀ t y, z.2.1.1 t = some y → ∃ j n, z.2.2.cls t = some j ∧ z.2.2.pos t = some n ∧
        n < (Lfam j).length ∧ (j = τ (Sum.inl t) ∨ j = τ (Sum.inr t)) ∧
        ∃ h : spec.Range t = R j, (Lfam j)[n]? = some (cast h y)) ∧
      (∀ t t' j n, z.2.2.cls t = some j → z.2.2.pos t = some n → z.2.2.cls t' = some j →
        z.2.2.pos t' = some n → t = t') := by
  have hinv := simulateQ_run_preserves_inv_of_query
    (QueryImpl.extendState (tapeCachingImplClass R τ hR) (classPosAux R τ))
    (fun s => ClassPosInv τ Lfam s.1.1 s.1.2 s.2.cls s.2.pos s.2.next s.2.cnt)
    (fun t s hs => classPosInvAux_step Lfam t s hs) oa _
    (ClassPosInv.empty τ Lfam) z hz
  refine ⟨fun t y ht => ?_, hinv.pos_inj⟩
  have htne : z.2.1.1 t ≠ none := by rw [ht]; exact Option.some_ne_none y
  obtain ⟨j, hj⟩ : ∃ j, z.2.2.cls t = some j :=
    Option.ne_none_iff_exists'.mp (hinv.cls_ne_none t htne)
  obtain ⟨n, hn⟩ : ∃ n, z.2.2.pos t = some n := by
    rcases hp : z.2.2.pos t with _ | n
    · obtain ⟨hnil, hlt⟩ := hinv.fallback t j htne hj hp
      have hlen := hinv.length_add j
      rw [hnil, List.length_nil, Nat.zero_add] at hlen
      exact absurd (hlen ▸ hlt) (by have := hq j; omega)
    · exact ⟨n, rfl⟩
  obtain ⟨hlt, hval⟩ := hinv.pos_spec t j n hj hn
  have hjt : j = τ (Sum.inl t) ∨ j = τ (Sum.inr t) := by
    rcases hinv.cls_tau t (by rw [hj]; exact Option.some_ne_none j) with hc | hc
    · exact Or.inl (Option.some_inj.mp (hj.symm.trans hc))
    · exact Or.inr (Option.some_inj.mp (hj.symm.trans hc))
  rw [ht] at hval
  exact ⟨j, n, hj, hn, lt_of_lt_of_le hlt (by have := hinv.length_add j; omega), hjt,
    range_eq_of_cls hR hjt, eq_some_cast_of_heq _ hval⟩

/-! ## Transporting a tape-family bound -/

/-- **Transporting a tape-family bound to a duplicated lazy random-oracle run.** If the event
`E` of the tape family has mass at most `b`, and off `E` no instrumented run of `oa` on that
family can leave a final cache satisfying `P`, then the shared lazy random-oracle run leaves a
cache satisfying `P` with mass at most `b`.

The mass of `E` is the caller's obligation. For an event of a single class's tape,
`evalDist_tapeFamily_setOf_eq` restates it over that class's `answerTape`, where the product
bounds of `IndepProductEvents.lean` apply; for an event spanning two classes only the bind-form
joint law `evalDist_tapeFamily_bind_eval₂` is available.

`htransport` is given only the families the draw can actually produce, so
`length_of_mem_support_tapeFamily` applies to the `Lfam` it is handed. That is what lets it
discharge the per-class query bounds of
`exists_pos_of_mem_support_run_tapeCachingImplClass`, which are stated against the lengths of
that family rather than against `m`. -/
theorem evalDist_run_dupRandomOracle_setOf_le_of_transport {α : Type}
    (oa : OracleComp (spec + spec) α) (P : spec.QueryCache → Prop) (m : J → ℕ)
    (b : ℝ≥0∞) (E : Set ((k : J) → List (R k)))
    (hE : letI : MeasurableSpace ((k : J) → List (R k)) := ⊤; 𝒟[tapeFamily R m] E ≤ b)
    (htransport : ∀ Lfam ∈ support (tapeFamily R m), Lfam ∉ E → ∀ z ∈ support ((simulateQ
        (QueryImpl.extendState (tapeCachingImplClass R τ hR) (classPosAux R τ)) oa).run
        ((∅, Lfam), ⟨fun _ => none, fun _ => none, fun _ => 0, fun _ => 0⟩)),
      ¬ P z.2.1.1) :
    letI : MeasurableSpace (α × spec.QueryCache) := ⊤
    𝒟[(simulateQ (dupRandomOracle spec) oa).run ∅] {z | P z.2} ≤ b := by
  classical
  let _ : MeasurableSpace (α × spec.QueryCache) := ⊤
  let _ : MeasurableSpace ((k : J) → List (R k)) := ⊤
  let _ : DiscreteMeasurableSpace ((k : J) → List (R k)) := ⟨fun _ => trivial⟩
  rw [evalDist_run_dupRandomOracle_eq_tapeFamily (R := R) (τ := τ) (hR := hR) oa ∅ m]
  refine le_trans ?_ hE
  refine evalDist_bind_apply_le_of_forall_mem_support_notMem_eq_zero _ _
    MeasurableSet.of_discrete MeasurableSet.of_discrete fun Lfam hLs hL => ?_
  refine evalDist.apply_eq_zero_of_disjoint_support _ MeasurableSet.of_discrete fun z hz => ?_
  rw [mem_support_bind_iff] at hz
  obtain ⟨w, hw, hz⟩ := hz
  rw [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  rw [← extendState_run_proj_eq (tapeCachingImplClass R τ hR) (classPosAux R τ) oa
    (∅, Lfam) ⟨fun _ => none, fun _ => none, fun _ => 0, fun _ => 0⟩, support_map] at hw
  obtain ⟨y, hy, hyw⟩ := hw
  have hyy : y.2.1.1 = w.2.1 := by rw [← hyw]; rfl
  simp only [Set.mem_ofPred_eq, ← hyy]
  exact htransport Lfam hLs hL y hy

end Position

end AnswerTape
