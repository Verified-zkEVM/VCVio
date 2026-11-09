/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/

module

public import VCVio.EvalDist.EvalDistEq
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.Constructions.UniformPreimage

/-!
# Uniform permutations extending a finite trace

The extension subtype records all forward constraints in a finite trace, including repetitions.
Nonemptiness of this subtype is the compatibility assumption. For a fresh input, the answer lies
among the unused outputs. Swapping two unused outputs preserves every recorded constraint and
gives a bijection between the corresponding answer fibers.

The sampling lemmas identify the eager uniform-extension distribution with first sampling a
uniform unused answer and then a uniform extension in that answer's fiber. Inverse queries are
handled by reversing all trace edges and inverting the permutation.

For a fixed program with distinct fresh sources and distinct fresh targets, the left-to-right
swap algorithm `install` sends uniform old-trace extensions to uniform extensions of
the combined trace. Sources and targets need not be disjoint from each other.

Samplers are `ProbComp`s; equalities of laws are stated for `𝒟[·]` under the discrete
σ-algebra on the sampled type.
-/

public section

noncomputable section

open OracleComp MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OracleComp.PermutationConditioning

variable {α : Type}

/-- All permutations satisfying the recorded forward edges. -/
abbrev Extensions (trace : List (α × α)) :=
  {p : Equiv.Perm α // ∀ edge ∈ trace, p edge.1 = edge.2}

/-- Inputs not already constrained by the trace. -/
abbrev UnusedInputs (trace : List (α × α)) :=
  {x : α // ∀ edge ∈ trace, x ≠ edge.1}

/-- Outputs not already occupied by a recorded edge. -/
abbrev UnusedOutputs (trace : List (α × α)) :=
  {y : α // ∀ edge ∈ trace, y ≠ edge.2}

/-- A fresh forward query can only return an unused output. -/
@[expose] def answer (trace : List (α × α)) (x : UnusedInputs trace) (p : Extensions trace) :
    UnusedOutputs trace :=
  ⟨p.1 x.1, by
    intro edge hedge heq
    exact x.2 edge hedge (p.1.injective (heq.trans (p.2 edge hedge).symm))⟩

section Swap

variable [DecidableEq α]

/-- Swapping unused outputs preserves the trace constraints. -/
@[expose] def swapOutputs (trace : List (α × α)) (y z : UnusedOutputs trace)
    (p : Extensions trace) : Extensions trace :=
  ⟨p.1.trans (Equiv.swap y.1 z.1), by
    intro edge hedge
    change Equiv.swap y.1 z.1 (p.1 edge.1) = edge.2
    rw [p.2 edge hedge]
    exact Equiv.swap_apply_of_ne_of_ne (y.2 edge hedge).symm (z.2 edge hedge).symm⟩

/-- Swapping the same two unused outputs twice restores the extension. -/
theorem swapOutputs_involutive (trace : List (α × α)) (y z : UnusedOutputs trace) :
    Function.Involutive (swapOutputs trace y z) := by
  intro p
  apply Subtype.ext
  apply Equiv.ext
  intro a
  exact Equiv.swap_apply_self y.1 z.1 (p.1 a)

end Swap

/-- Every unused output occurs as the answer to a fresh query under some extension. -/
theorem answer_surjective (trace : List (α × α)) (x : UnusedInputs trace)
    (htrace : Nonempty (Extensions trace)) : Function.Surjective (answer trace x) := by
  classical
  obtain ⟨p⟩ := htrace
  intro y
  refine ⟨swapOutputs trace (answer trace x p) y p, ?_⟩
  apply Subtype.ext
  exact Equiv.swap_apply_left (p.1 x.1) y.1

/-- The fiber of extensions giving one particular unused answer. -/
abbrev AnswerFiber (trace : List (α × α)) (x : UnusedInputs trace)
    (y : UnusedOutputs trace) := {p : Extensions trace // answer trace x p = y}

/-- Equal-size answer fibers are related by swapping the two unused outputs. -/
@[expose] def answerFiberEquiv [DecidableEq α] (trace : List (α × α)) (x : UnusedInputs trace)
    (y z : UnusedOutputs trace) : AnswerFiber trace x y ≃ AnswerFiber trace x z where
  toFun p := ⟨swapOutputs trace y z p.1, by
    apply Subtype.ext
    change Equiv.swap y.1 z.1 (p.1.1 x.1) = z.1
    rw [show p.1.1 x.1 = y.1 from congrArg Subtype.val p.2]
    exact Equiv.swap_apply_left y.1 z.1⟩
  invFun p := ⟨swapOutputs trace y z p.1, by
    apply Subtype.ext
    change Equiv.swap y.1 z.1 (p.1.1 x.1) = y.1
    rw [show p.1.1 x.1 = z.1 from congrArg Subtype.val p.2]
    exact Equiv.swap_apply_right y.1 z.1⟩
  left_inv p := Subtype.ext (swapOutputs_involutive trace y z p.1)
  right_inv p := Subtype.ext (swapOutputs_involutive trace y z p.1)

/-- Conditioning on an answer is exactly adding that forward edge to the trace. -/
@[expose] def answerFiberEquivExtended (trace : List (α × α)) (x : UnusedInputs trace)
    (y : UnusedOutputs trace) :
    AnswerFiber trace x y ≃ Extensions ((x.1, y.1) :: trace) where
  toFun p := ⟨p.1.1, by
    intro edge hedge
    rcases List.mem_cons.mp hedge with rfl | hedge
    · exact congrArg Subtype.val p.2
    · exact p.1.2 edge hedge⟩
  invFun p := ⟨⟨p.1, fun edge hedge => p.2 edge (List.mem_cons_of_mem _ hedge)⟩, by
    apply Subtype.ext
    exact p.2 (x.1, y.1) (List.mem_cons_self ..)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Nonemptiness of the remaining output space follows from an extension and a fresh input. -/
theorem unusedOutputs_nonempty (trace : List (α × α)) (x : UnusedInputs trace)
    (htrace : Nonempty (Extensions trace)) : Nonempty (UnusedOutputs trace) :=
  htrace.map (answer trace x)

/-! ## Programming a fixed fresh edge -/

/-- Install a fixed fresh edge by the output swap of one step of `install`. -/
@[expose] def programExtension [DecidableEq α] (trace : List (α × α)) (x : UnusedInputs trace)
    (y : UnusedOutputs trace) (p : Extensions trace) : Extensions ((x.1, y.1) :: trace) :=
  answerFiberEquivExtended trace x y
    ⟨swapOutputs trace (answer trace x p) y p, by
      apply Subtype.ext
      exact Equiv.swap_apply_left (p.1 x.1) y.1⟩

/-- A fresh edge can always be appended to a satisfiable trace. -/
theorem extensions_cons_nonempty (trace : List (α × α)) (x : UnusedInputs trace)
    (y : UnusedOutputs trace) (htrace : Nonempty (Extensions trace)) :
    Nonempty (Extensions ((x.1, y.1) :: trace)) := by
  classical
  exact htrace.map (programExtension trace x y)

/-! ## Fixed fresh programs -/

/-- Sources and targets are each distinct and avoid the corresponding side of the old trace.
Sources may equal targets, including targets of other programmed edges. -/
structure FreshProgram (trace program : List (α × α)) : Prop where
  /-- The programmed sources are pairwise distinct. -/
  sourcesNodup : (program.map Prod.fst).Nodup
  /-- The programmed targets are pairwise distinct. -/
  targetsNodup : (program.map Prod.snd).Nodup
  /-- No programmed source already occurs as a source of the old trace. -/
  inputsFresh : ∀ edge ∈ program, ∀ old ∈ trace, edge.1 ≠ old.1
  /-- No programmed target already occurs as a target of the old trace. -/
  outputsFresh : ∀ edge ∈ program, ∀ old ∈ trace, edge.2 ≠ old.2

/-- After programming the first edge, the remaining edges are fresh for the enlarged trace. -/
theorem FreshProgram.tail {trace rest : List (α × α)} {edge : α × α}
    (h : FreshProgram trace (edge :: rest)) : FreshProgram (edge :: trace) rest := by
  have hs : edge.1 ∉ rest.map Prod.fst ∧ (rest.map Prod.fst).Nodup := by
    simpa using h.sourcesNodup
  have ht : edge.2 ∉ rest.map Prod.snd ∧ (rest.map Prod.snd).Nodup := by
    simpa using h.targetsNodup
  refine ⟨hs.2, ht.2, ?_, ?_⟩
  · intro a ha b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact fun hab => hs.1 (List.mem_map.mpr ⟨a, ha, hab⟩)
    · exact h.inputsFresh a (List.mem_cons_of_mem _ ha) b hb
  · intro a ha b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact fun hab => ht.1 (List.mem_map.mpr ⟨a, ha, hab⟩)
    · exact h.outputsFresh a (List.mem_cons_of_mem _ ha) b hb

/-- Reordering or repeating identical trace constraints does not change the extension space. -/
@[expose] def extensionsEquivOfMemIff (trace other : List (α × α))
    (h : ∀ edge, edge ∈ trace ↔ edge ∈ other) : Extensions trace ≃ Extensions other where
  toFun p := ⟨p.1, fun edge hedge => p.2 edge ((h edge).mpr hedge)⟩
  invFun p := ⟨p.1, fun edge hedge => p.2 edge ((h edge).mp hedge)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every fixed fresh program extends a satisfiable trace. -/
theorem extensions_append_nonempty (trace program : List (α × α))
    (h : FreshProgram trace program) (htrace : Nonempty (Extensions trace)) :
    Nonempty (Extensions (trace ++ program)) := by
  classical
  induction program generalizing trace with
  | nil => simpa using htrace
  | cons edge rest ih =>
    let x : UnusedInputs trace := ⟨edge.1, h.inputsFresh edge (List.mem_cons_self ..)⟩
    let y : UnusedOutputs trace := ⟨edge.2, h.outputsFresh edge (List.mem_cons_self ..)⟩
    have hcons := extensions_cons_nonempty trace x y htrace
    have hrest := ih (edge :: trace) h.tail hcons
    exact hrest.map (extensionsEquivOfMemIff _ _ (by
      intro a
      simp only [List.mem_append, List.mem_cons]
      tauto))

/-! ## Uniform extensions -/

section Uniform

variable [DecidableEq α] [Fintype α]

/-- Uniform sampling among permutations extending the recorded edges. -/
@[expose] def uniformExtensions (trace : List (α × α)) (htrace : Nonempty (Extensions trace)) :
    ProbComp (Extensions trace) :=
  letI := htrace
  letI := SampleableType.ofFintype (Extensions trace)
  $ᵗ (Extensions trace)

/-- Uniform sampling among the outputs still available to a fresh input. -/
@[expose] def uniformUnusedOutputs (trace : List (α × α)) (x : UnusedInputs trace)
    (htrace : Nonempty (Extensions trace)) : ProbComp (UnusedOutputs trace) :=
  letI := unusedOutputs_nonempty trace x htrace
  letI := SampleableType.ofFintype (UnusedOutputs trace)
  $ᵗ (UnusedOutputs trace)

/-- Uniform sampling in the extension fiber specified by the new answer. -/
@[expose] def uniformAnswerFiber (trace : List (α × α)) (x : UnusedInputs trace)
    (htrace : Nonempty (Extensions trace)) (y : UnusedOutputs trace) :
    ProbComp (Extensions trace) :=
  OracleComp.UniformPreimage.sampleUniformPreimage (answer trace x) y
    (OracleComp.UniformPreimage.preimage_nonempty (answer trace x)
      (answer_surjective trace x htrace) y)

/-- Every unused answer has the same number of compatible extensions. -/
theorem card_answerFiber_eq (trace : List (α × α)) (x : UnusedInputs trace)
    (y z : UnusedOutputs trace) :
    Fintype.card (AnswerFiber trace x y) = Fintype.card (AnswerFiber trace x z) :=
  Fintype.card_congr (answerFiberEquiv trace x y z)

/-- The probability of an answer is the size of its fiber divided by all extensions. -/
theorem uniformExtensions_answer_apply (trace : List (α × α)) (x : UnusedInputs trace)
    (htrace : Nonempty (Extensions trace)) (y : UnusedOutputs trace) :
    Pr{let p ← uniformExtensions trace htrace}[answer trace x p = y] =
      (Fintype.card (AnswerFiber trace x y) : ℝ≥0∞) *
        (Fintype.card (Extensions trace) : ℝ≥0∞)⁻¹ := by
  classical
  let _ := htrace
  let _ := SampleableType.ofFintype (Extensions trace)
  change Pr{let p ← $ᵗ (Extensions trace)}[answer trace x p = y] = _
  rw [SampleableType.prEvent_uniformSample, div_eq_mul_inv]
  simp only [AnswerFiber, Fintype.card_subtype]

/-- Every unused answer has positively many compatible extensions. -/
theorem card_answerFiber_pos (trace : List (α × α)) (x : UnusedInputs trace)
    (htrace : Nonempty (Extensions trace)) (y : UnusedOutputs trace) :
    0 < Fintype.card (AnswerFiber trace x y) := by
  obtain ⟨p, hp⟩ := answer_surjective trace x htrace y
  exact Fintype.card_pos_iff.mpr ⟨⟨p, hp⟩⟩

/-- All extensions split into equal answer fibers over the unused outputs. -/
theorem card_extensions_eq_mul (trace : List (α × α)) (x : UnusedInputs trace)
    (y : UnusedOutputs trace) :
    Fintype.card (Extensions trace) =
      Fintype.card (UnusedOutputs trace) * Fintype.card (AnswerFiber trace x y) := by
  classical
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := answer trace x)
    (t := Finset.univ) fun _ _ => Finset.mem_univ _]
  have hfiber (z : UnusedOutputs trace) :
      (Finset.univ.filter fun p => answer trace x p = z).card =
        Fintype.card (AnswerFiber trace x y) := by
    rw [← card_answerFiber_eq trace x z y]
    exact (Fintype.card_subtype _).symm
  simp only [hfiber, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- A fresh query to a uniform extension returns a uniform unused output. -/
theorem map_answer_uniformExtensions (trace : List (α × α)) (x : UnusedInputs trace)
    (htrace : Nonempty (Extensions trace)) :
    (letI : MeasurableSpace (UnusedOutputs trace) := ⊤
    𝒟[answer trace x <$> uniformExtensions trace htrace] =
      𝒟[uniformUnusedOutputs trace x htrace]) := by
  classical
  let : MeasurableSpace (UnusedOutputs trace) := ⊤
  let _ := unusedOutputs_nonempty trace x htrace
  let _ := SampleableType.ofFintype (UnusedOutputs trace)
  apply Measure.ext_of_singleton
  intro y
  rw [← prEvent_eq_evalDist_singleton (answer trace x <$> uniformExtensions trace htrace),
    ← prEvent_eq_evalDist_singleton (uniformUnusedOutputs trace x htrace), prEvent_map,
    uniformExtensions_answer_apply]
  change _ = Pr{let z ← $ᵗ (UnusedOutputs trace)}[z = y]
  rw [SampleableType.prEvent_uniformSample, card_extensions_eq_mul trace x y]
  have hpos := card_answerFiber_pos trace x htrace y
  have hfilter : (Finset.univ.filter fun z : UnusedOutputs trace => z = y).card = 1 := by
    rw [Finset.filter_eq' Finset.univ y]
    simp
  rw [hfilter, Nat.cast_mul, ENNReal.mul_inv (by simp) (by simp), mul_comm, mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hpos.ne') (by simp), mul_one, Nat.cast_one, one_div]

/-- Sampling an unused answer and then a uniform extension in its fiber exactly reconstructs
the eager uniform-extension distribution. -/
theorem uniformExtensions_eq_bind_fibers (trace : List (α × α)) (x : UnusedInputs trace)
    (htrace : Nonempty (Extensions trace)) :
    (letI : MeasurableSpace (Extensions trace) := ⊤
    𝒟[uniformExtensions trace htrace] =
      𝒟[uniformUnusedOutputs trace x htrace >>= uniformAnswerFiber trace x htrace]) := by
  let : MeasurableSpace (Extensions trace) := ⊤
  let _ := htrace
  let _ := SampleableType.ofFintype (Extensions trace)
  rw [← ((evalDistEq_iff_evalDist_eq.mpr (map_answer_uniformExtensions trace x htrace)).bind_left
      (uniformAnswerFiber trace x htrace)).evalDist_eq,
    bind_map_left]
  exact (OracleComp.UniformPreimage.bind_sampleUniformPreimage_eq_uniform
    (answer trace x)).symm

/-- Inversion turns extensions of a forward trace into extensions of its reversed edges. -/
@[expose] def inverseExtensionsEquiv (trace : List (α × α)) :
    Extensions trace ≃ Extensions (trace.map Prod.swap) where
  toFun p := ⟨p.1.symm, by
    intro edge hedge
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hedge
    exact p.1.symm_apply_eq.mpr (p.2 original horiginal).symm⟩
  invFun p := ⟨p.1.symm, by
    intro edge hedge
    exact p.1.symm_apply_eq.mpr (p.2 edge.swap (List.mem_map.mpr ⟨edge, hedge, rfl⟩)).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Uniform trace extensions are preserved by inversion and reversal of all recorded edges. -/
theorem map_inverse_uniformExtensions (trace : List (α × α))
    (htrace : Nonempty (Extensions trace)) :
    (letI : MeasurableSpace (Extensions (trace.map Prod.swap)) := ⊤
    𝒟[inverseExtensionsEquiv trace <$> uniformExtensions trace htrace] =
      𝒟[uniformExtensions (trace.map Prod.swap)
        (htrace.map (inverseExtensionsEquiv trace))]) := by
  let : MeasurableSpace (Extensions (trace.map Prod.swap)) := ⊤
  let _ := htrace
  let _ := SampleableType.ofFintype (Extensions trace)
  let _ := htrace.map (inverseExtensionsEquiv trace)
  let _ := SampleableType.ofFintype (Extensions (trace.map Prod.swap))
  exact (SampleableType.map_uniformSample_evalDistEq_of_bijective
    (inverseExtensionsEquiv trace).bijective).evalDist_eq

/-- Programming a fixed fresh target sends the uniform distribution in any old-answer fiber
to the uniform distribution of extensions with that fixed new edge. -/
theorem map_programExtension_uniformAnswerFiber (trace : List (α × α))
    (x : UnusedInputs trace) (htrace : Nonempty (Extensions trace))
    (y z : UnusedOutputs trace) :
    (letI : MeasurableSpace (Extensions ((x.1, z.1) :: trace)) := ⊤
    𝒟[programExtension trace x z <$> uniformAnswerFiber trace x htrace y] =
      𝒟[uniformExtensions ((x.1, z.1) :: trace)
        (extensions_cons_nonempty trace x z htrace)]) := by
  classical
  let : MeasurableSpace (Extensions ((x.1, z.1) :: trace)) := ⊤
  let _ := OracleComp.UniformPreimage.preimage_nonempty (answer trace x)
    (answer_surjective trace x htrace) y
  let _ : SampleableType (AnswerFiber trace x y) := SampleableType.ofFintype _
  let _ := extensions_cons_nonempty trace x z htrace
  let _ := SampleableType.ofFintype (Extensions ((x.1, z.1) :: trace))
  let e := (answerFiberEquiv trace x y z).trans (answerFiberEquivExtended trace x z)
  have he : (fun p : AnswerFiber trace x y => programExtension trace x z p.1) = e := by
    funext p
    apply Subtype.ext
    change p.1.1.trans (Equiv.swap (p.1.1 x.1) z.1) =
      p.1.1.trans (Equiv.swap y.1 z.1)
    rw [show p.1.1 x.1 = y.1 from congrArg Subtype.val p.2]
  change 𝒟[programExtension trace x z <$> (Subtype.val <$>
    ($ᵗ (AnswerFiber trace x y)))] = 𝒟[$ᵗ (Extensions ((x.1, z.1) :: trace))]
  rw [Functor.map_map, he]
  exact (SampleableType.map_uniformSample_evalDistEq_of_bijective e.bijective).evalDist_eq

/-- A fixed fresh swap sends uniform old-trace extensions to uniform new-trace extensions. -/
theorem map_programExtension_uniformExtensions (trace : List (α × α))
    (x : UnusedInputs trace) (y : UnusedOutputs trace)
    (htrace : Nonempty (Extensions trace)) :
    (letI : MeasurableSpace (Extensions ((x.1, y.1) :: trace)) := ⊤
    𝒟[programExtension trace x y <$> uniformExtensions trace htrace] =
      𝒟[uniformExtensions ((x.1, y.1) :: trace)
        (extensions_cons_nonempty trace x y htrace)]) := by
  let : MeasurableSpace (Extensions ((x.1, y.1) :: trace)) := ⊤
  let : MeasurableSpace (UnusedOutputs trace) := ⊤
  rw [map_eq_bind_pure_comp,
    ((evalDistEq_iff_evalDist_eq.mpr
      (uniformExtensions_eq_bind_fibers trace x htrace)).bind_left _).evalDist_eq,
    bind_assoc, evalDist_bind_congr _ _ (fun _ => uniformExtensions ((x.1, y.1) :: trace)
      (extensions_cons_nonempty trace x y htrace)) fun z => by
        rw [← map_eq_bind_pure_comp]
        exact map_programExtension_uniformAnswerFiber trace x htrace z y,
    _root_.evalDist_bind_const, measure_univ, one_smul]

/-- Uniform trace extensions viewed as a distribution on the underlying permutations. -/
@[expose] def uniformPermutations (trace : List (α × α)) (htrace : Nonempty (Extensions trace)) :
    ProbComp (Equiv.Perm α) := Subtype.val <$> uniformExtensions trace htrace

/-- Uniform extension distributions depend on the constraints, not their order in the trace. -/
theorem uniformPermutations_congr (trace other : List (α × α))
    (htrace : Nonempty (Extensions trace)) (hother : Nonempty (Extensions other))
    (h : ∀ edge, edge ∈ trace ↔ edge ∈ other) :
    (letI : MeasurableSpace (Equiv.Perm α) := ⊤
    𝒟[uniformPermutations trace htrace] = 𝒟[uniformPermutations other hother]) := by
  let : MeasurableSpace (Equiv.Perm α) := ⊤
  let _ := htrace
  let _ := SampleableType.ofFintype (Extensions trace)
  let _ := hother
  let _ := SampleableType.ofFintype (Extensions other)
  let e := extensionsEquivOfMemIff trace other h
  let : MeasurableSpace (Extensions other) := ⊤
  have hmap := ((SampleableType.map_uniformSample_evalDistEq_of_bijective e.bijective).map
    (Subtype.val : Extensions other → Equiv.Perm α)).evalDist_eq
  rw [Functor.map_map] at hmap
  exact hmap

/-- The single-edge programming law on underlying permutations. -/
theorem map_swap_uniformPermutations (trace : List (α × α))
    (x : UnusedInputs trace) (y : UnusedOutputs trace)
    (htrace : Nonempty (Extensions trace)) :
    (letI : MeasurableSpace (Equiv.Perm α) := ⊤
    𝒟[(fun p => p.trans (Equiv.swap (p x.1) y.1)) <$> uniformPermutations trace htrace] =
      𝒟[uniformPermutations ((x.1, y.1) :: trace)
        (extensions_cons_nonempty trace x y htrace)]) := by
  let : MeasurableSpace (Equiv.Perm α) := ⊤
  have h := ((evalDistEq_iff_evalDist_eq.mpr
    (map_programExtension_uniformExtensions trace x y htrace)).map Subtype.val).evalDist_eq
  simp only [uniformPermutations, Functor.map_map] at h ⊢
  exact h

end Uniform

/-! ## Sequential programming of a fixed fresh program -/

/-- Install a list of edges by left-to-right output swaps. -/
@[expose] def install [DecidableEq α] : Equiv.Perm α → List (α × α) → Equiv.Perm α
  | p, [] => p
  | p, edge :: rest => install (p.trans (Equiv.swap (p edge.1) edge.2)) rest

/-- Sequential swaps map uniform extensions of the original trace to uniform extensions of
the trace with the complete fixed program appended. No source-target disjointness is required. -/
theorem map_install_uniformPermutations [DecidableEq α] [Fintype α] (trace program : List (α × α))
    (h : FreshProgram trace program) (htrace : Nonempty (Extensions trace)) :
    (letI : MeasurableSpace (Equiv.Perm α) := ⊤
    𝒟[(fun p => install p program) <$> uniformPermutations trace htrace] =
      𝒟[uniformPermutations (trace ++ program)
        (extensions_append_nonempty trace program h htrace)]) := by
  let : MeasurableSpace (Equiv.Perm α) := ⊤
  induction program generalizing trace with
  | nil =>
    simp only [List.append_nil, install, id_map']
  | cons edge rest ih =>
    let x : UnusedInputs trace := ⟨edge.1, h.inputsFresh edge (List.mem_cons_self ..)⟩
    let y : UnusedOutputs trace := ⟨edge.2, h.outputsFresh edge (List.mem_cons_self ..)⟩
    let hcons := extensions_cons_nonempty trace x y htrace
    calc
      𝒟[(fun p => install p (edge :: rest)) <$> uniformPermutations trace htrace] =
          𝒟[(fun p => install p rest) <$> ((fun p => p.trans (Equiv.swap (p x.1) y.1)) <$>
            uniformPermutations trace htrace)] := by
        rw [Functor.map_map]
        rfl
      _ = 𝒟[(fun p => install p rest) <$> uniformPermutations (edge :: trace) hcons] := by
        exact ((evalDistEq_iff_evalDist_eq.mpr
          (map_swap_uniformPermutations trace x y htrace)).map _).evalDist_eq
      _ = 𝒟[uniformPermutations ((edge :: trace) ++ rest)
          (extensions_append_nonempty (edge :: trace) rest h.tail hcons)] :=
        ih (edge :: trace) h.tail hcons
      _ = 𝒟[uniformPermutations (trace ++ edge :: rest)
          (extensions_append_nonempty trace (edge :: rest) h htrace)] := by
        apply uniformPermutations_congr
        intro a
        simp only [List.mem_append, List.mem_cons]
        tauto

end OracleComp.PermutationConditioning
