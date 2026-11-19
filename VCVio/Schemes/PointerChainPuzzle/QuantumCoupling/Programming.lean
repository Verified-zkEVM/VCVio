/-
Copyright (c) 2026 Quang Dao, Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import VCVio.Schemes.PointerChainPuzzle.QuantumEncoding
public import VCVio.Schemes.PointerChainPuzzle.RankFrontier
public import ToMathlib.MeasureTheory.Measure.UniformTable.Adaptive

/-!
# Rank-ordered raw oracle programming for the pointer-chain puzzle

Each path value has an independent full raw response word. Projecting masks to their link
prefixes gives the typed path labels, while retaining every raw tail. A path input depends
only on strictly earlier labels. Adaptive table exchanges therefore realize reverse-order
programming as a permutation of a complete raw table and its auxiliary words.

Distinct programmed inputs force the honest path traversal to recover the projected labels.
The full raw table stays available for arbitrary quantum continuations; no query is routed
through a classical cache and no preprocessing resource bound is needed for the coupling.
-/

public section

open OracleSpec OracleComp Quantum MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PointerChainPuzzle.LeanSeal

variable {b n m B : ℕ}

/-- The portion of a raw path response outside its typed value. -/
@[expose]
def PathTail {n m : ℕ} (b : ℕ) : PathValue n m → Type
  | .mask .. => Bytes (32 - b)
  | _ => Unit

/-- A complete raw path response split into its typed value and complementary tail. -/
@[expose]
def splitPath {b n m : ℕ} (hb : b ≤ 32) :
    (v : PathValue n m) → Bytes 32 ≃ v.Val (Bytes 32) (Bytes b) × PathTail b v
  | .state .. => (Equiv.prodPUnit (Bytes 32)).symm
  | .mask .. => splitMask hb
  | .acc .. => (Equiv.prodPUnit (Bytes 32)).symm
  | .key => (Equiv.prodPUnit (Bytes 32)).symm
  | .commit => (Equiv.prodPUnit (Bytes 32)).symm

/-- Project full raw path responses to the corresponding typed labels. -/
@[expose]
def pathLabels (hb : b ≤ 32) (W : PathValue n m → Bytes 32) :
    Labels n m (Bytes 32) (Bytes b) := fun v ↦ (splitPath hb v (W v)).1

/-- Updating one raw response changes only the corresponding typed label. -/
theorem pathLabels_update (hb : b ≤ 32) (W : PathValue n m → Bytes 32)
    (w : PathValue n m) (a : Bytes 32) :
    pathLabels hb (Function.update W w a) =
      Function.update (pathLabels hb W) w ((splitPath hb w a).1) := by
  funext v
  by_cases hv : v = w
  · subst v
    simp [pathLabels]
  · simp [pathLabels, Function.update_of_ne hv]

noncomputable instance instFintypePathTail : (v : PathValue n m) → Fintype (PathTail b v)
  | .state .. => inferInstanceAs (Fintype Unit)
  | .mask .. => inferInstanceAs (Fintype (Bytes (32 - b)))
  | .acc .. => inferInstanceAs (Fintype Unit)
  | .key => inferInstanceAs (Fintype Unit)
  | .commit => inferInstanceAs (Fintype Unit)

instance instInhabitedPathTail : (v : PathValue n m) → Inhabited (PathTail b v)
  | .state .. => inferInstanceAs (Inhabited Unit)
  | .mask .. => inferInstanceAs (Inhabited (Bytes (32 - b)))
  | .acc .. => inferInstanceAs (Inhabited Unit)
  | .key => inferInstanceAs (Inhabited Unit)
  | .commit => inferInstanceAs (Inhabited Unit)

/-- Full raw path responses are equivalent to typed labels and all complementary tails. -/
@[expose]
def pathLabelEquiv (hb : b ≤ 32) :
    (PathValue n m → Bytes 32) ≃
      Labels n m (Bytes 32) (Bytes b) × ((v : PathValue n m) → PathTail b v) :=
  (Equiv.piCongrRight (splitPath hb)).trans
    (Equiv.arrowProdEquivProdArrow (PathValue n m) _ _)

/-- Projecting independent uniform full path words gives independent uniform typed labels.
The complementary raw tails remain in the underlying sample space. -/
theorem uniformOn_univ_map_pathLabels (hb : b ≤ 32)
    [MeasurableSpace (PathValue n m → Bytes 32)]
    [MeasurableSingletonClass (PathValue n m → Bytes 32)]
    [MeasurableSpace (Labels n m (Bytes 32) (Bytes b))]
    [MeasurableSingletonClass (Labels n m (Bytes 32) (Bytes b))] :
    (uniformOn Set.univ : Measure (PathValue n m → Bytes 32)).map (pathLabels hb) =
      (uniformOn Set.univ : Measure (Labels n m (Bytes 32) (Bytes b))) := by
  let : MeasurableSpace ((v : PathValue n m) → PathTail b v) := ⊤
  have he := uniformOn_univ_map_equiv (pathLabelEquiv (n := n) (m := m) hb)
  calc
    _ = ((uniformOn Set.univ : Measure (PathValue n m → Bytes 32)).map
        (pathLabelEquiv hb)).map Prod.fst := by
      rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete]
      rfl
    _ = _ := by
      rw [he, uniformOn_univ_prod, Measure.map_fst_prod, measure_univ, one_smul]


variable [NeZero n]

/-- The encoded oracle input of a path value, in the complete finite byte window. -/
@[expose]
def pathWindowInput (hB : hashInputBound b ≤ B) (salt : Bytes 16) (x : Bytes b)
    (z : Fin (n - 1) → Bytes b) (v : PathValue n m)
    (ℓ : Labels n m (Bytes 32) (Bytes b)) : ByteArray.Bounded B :=
  hashInputWindow hB (pathInput m (ctx b n m) id (labelPuzzle salt x z ℓ) ℓ v)

/-- Changing a non-predecessor label leaves a path input unchanged. -/
theorem pathWindowInput_update_of_not_mem_preds (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (v w : PathValue n m) (hw : w ∉ v.preds)
    (ℓ : Labels n m (Bytes 32) (Bytes b)) (a : w.Val (Bytes 32) (Bytes b)) :
    pathWindowInput hB salt x z v (Function.update ℓ w a) =
      pathWindowInput hB salt x z v ℓ := by
  unfold pathWindowInput
  congr 1
  rw [pathInput_labelPuzzle m (ctx b n m) id salt x z (Function.update ℓ w a) ℓ]
  apply pathInput_congr
  intro u hu
  have huw : u ≠ w := by
    intro he
    subst u
    exact hw hu
  exact Function.update_of_ne huw a ℓ

/-- A path input is independent of the output label being programmed there. -/
theorem pathWindowInput_update_self (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (v : PathValue n m) (ℓ : Labels n m (Bytes 32) (Bytes b))
    (a : v.Val (Bytes 32) (Bytes b)) :
    pathWindowInput hB salt x z v (Function.update ℓ v a) =
      pathWindowInput hB salt x z v ℓ := by
  apply pathWindowInput_update_of_not_mem_preds
  intro hv
  exact lt_irrefl _ (PathValue.rho_lt_of_mem_preds hv)

/-- A path input is independent of labels with equal or later honest receipt rank. -/
theorem pathWindowInput_update_of_rho_le (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (v w : PathValue n m) (hw : v.rho ≤ w.rho)
    (ℓ : Labels n m (Bytes 32) (Bytes b)) (a : w.Val (Bytes 32) (Bytes b)) :
    pathWindowInput hB salt x z v (Function.update ℓ w a) =
      pathWindowInput hB salt x z v ℓ := by
  apply pathWindowInput_update_of_not_mem_preds
  intro hm
  exact (not_lt_of_ge hw) (PathValue.rho_lt_of_mem_preds hm)

/-- The typed projection of a raw path response is the source encoding's truncation. -/
theorem splitPath_fst_eq_truncate (hb : b ≤ 32)
    (P : PointerChainPuzzle.Puzzle n (Bytes 32) (Bytes b) (Bytes 16))
    (ℓ : Labels n m (Bytes 32) (Bytes b)) (v : PathValue n m) (y : Bytes 32) :
    (splitPath hb v y).1 = cast (range_pathInput m (ctx b n m) id P ℓ v)
      (truncate (pathInput m (ctx b n m) id P ℓ v) y) := by
  rcases v with ⟨⟨_ | i, hi⟩, ⟨_ | k, hk⟩⟩ | i | ⟨_ | i, hi⟩ | _ | _ <;> rfl


/-- The encoded path input determined by full raw response words. -/
@[expose]
def rawPathInput (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (v : PathValue n m) (W : PathValue n m → Bytes 32) : ByteArray.Bounded B :=
  pathWindowInput hB salt x z v (pathLabels hb W)

/-- A raw path input is independent of its own auxiliary raw response word. -/
theorem rawPathInput_update_self (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (v : PathValue n m) (W : PathValue n m → Bytes 32) (a : Bytes 32) :
    rawPathInput hb hB salt x z v (Function.update W v a) =
      rawPathInput hb hB salt x z v W := by
  unfold rawPathInput
  rw [pathLabels_update]
  exact pathWindowInput_update_self hB salt x z v _ _

/-- Updating an equal-rank or later raw response leaves an earlier input unchanged. -/
theorem rawPathInput_update_of_rho_le (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (v w : PathValue n m) (hw : v.rho ≤ w.rho)
    (W : PathValue n m → Bytes 32) (a : Bytes 32) :
    rawPathInput hb hB salt x z v (Function.update W w a) =
      rawPathInput hb hB salt x z v W := by
  unfold rawPathInput
  rw [pathLabels_update]
  exact pathWindowInput_update_of_rho_le hB salt x z v w hw _ _


/-- Rank-ordered exchanges between a complete raw oracle and independent full path responses. -/
@[expose]
def pathProgrammingEquiv (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b) :
    ((ByteArray.Bounded B → Bytes 32) × (PathValue n m → Bytes 32)) ≃
      ((ByteArray.Bounded B → Bytes 32) × (PathValue n m → Bytes 32)) :=
  Equiv.tableLabelExchangeList (rawPathInput hb hB salt x z)
    (fun _ ↦ (Equiv.prodPUnit (Bytes 32) : Bytes 32 × Unit ≃ Bytes 32).symm)
    (fun v W a ↦ rawPathInput_update_self hb hB salt x z v W a) (PathValue.order n m)

/-- Program the full raw response of every path input, giving earlier ranks priority on
repeated inputs. The raw responses include the mask tails. -/
@[expose]
def programPath (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32) (W : PathValue n m → Bytes 32) :
    ByteArray.Bounded B → Bytes 32 :=
  Equiv.tableLabelProgram (rawPathInput hb hB salt x z)
    (fun _ ↦ (Equiv.prodPUnit (Bytes 32) : Bytes 32 × Unit ≃ Bytes 32).symm)
    (PathValue.order n m) H W

/-- Reversing the ranked exchanges realizes raw programming for every path labelling,
including labellings whose inputs collide. -/
theorem pathProgrammingEquiv_symm_fst (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32) (W : PathValue n m → Bytes 32) :
    ((pathProgrammingEquiv hb hB salt x z).symm (H, W)).1 =
      programPath hb hB salt x z H W := by
  apply Equiv.tableLabelExchangeList_symm_fst _ _ _ _ PathValue.nodup_order
  exact PathValue.pairwise_order.imp fun {v w} h W a ↦
    rawPathInput_update_of_rho_le hb hB salt x z v w h W a

/-- With distinct path inputs, each programmed cell contains its prescribed full raw response. -/
theorem programPath_apply_of_injective (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32) (W : PathValue n m → Bytes 32)
    (hinj : Function.Injective (fun v ↦ rawPathInput hb hB salt x z v W))
    (v : PathValue n m) :
    programPath hb hB salt x z H W (rawPathInput hb hB salt x z v W) = W v :=
  Equiv.tableLabelProgram_apply_of_injective _ _ _ _ _ PathValue.nodup_order hinj
    (PathValue.mem_order v)

/-- Inputs outside the programmed path retain their raw oracle values. -/
theorem programPath_apply_of_avoids (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32) (W : PathValue n m → Bytes 32)
    (d : ByteArray.Bounded B)
    (havoid : ∀ v, rawPathInput hb hB salt x z v W ≠ d) :
    programPath hb hB salt x z H W d = H d :=
  Equiv.tableLabelProgram_apply_of_avoids _ _ _ _ _ d (fun v _ ↦ havoid v)

/-- A complete oracle answering all path inputs with the prescribed raw responses
forces the honest ranked path traversal to recover their typed projections. -/
theorem fixedPath_eq_pathLabels_of_answers (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32) (W : PathValue n m → Bytes 32)
    (hread : ∀ v, H (rawPathInput hb hB salt x z v W) = W v)
    (π ν : Labels n m (Bytes 32) (Bytes b)) :
    fixedPath m (ctx b n m) id (oracles (extendWindowOracle H))
      (labelPuzzle salt x z π) (PathValue.order n m) ν = pathLabels hb W := by
  let P := labelPuzzle salt x z π
  let O := oracles (b := b) (n := n) (extendWindowOracle H)
  apply fixedPath_eq O P (pathLabels hb W) _ PathValue.pairwise_order PathValue.nodup_order
    (fun w hw ↦ absurd (PathValue.mem_order w) hw)
  intro v μ hμ
  have he := pathInput_congr m (ctx b n m) id P v hμ
  have hh : cast (range_pathInput m (ctx b n m) id P (pathLabels hb W) v)
      (O.toImpl (pathInput m (ctx b n m) id P (pathLabels hb W) v)).run =
        pathLabels hb W v := by
    dsimp only [O]
    rw [toImpl_oracles_apply]
    rw [← toByteArray_hashInputWindow hB
      (pathInput m (ctx b n m) id P (pathLabels hb W) v), extendWindowOracle_apply]
    have hl : H (hashInputWindow hB
        (pathInput m (ctx b n m) id P (pathLabels hb W) v)) = W v := by
      dsimp only [P]
      rw [pathInput_labelPuzzle m (ctx b n m) id salt x z π (pathLabels hb W)]
      exact hread v
    rw [hl]
    exact (splitPath_fst_eq_truncate hb P (pathLabels hb W) v (W v)).symm
  exact (O.cast_toImpl_run_congr he _ _).trans hh

/-- Prescribed raw path answers determine the masked-link generator's public puzzle and key. -/
theorem simulateQ_genMaskedWith_of_answers (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32) (W : PathValue n m → Bytes 32)
    (hread : ∀ v, H (rawPathInput hb hB salt x z v W) = W v) :
    simulateQ (impl (extendWindowOracle H) b n)
      (genMaskedWith m (ctx b n m) id salt x z) =
      pure (labelPuzzle salt x z (pathLabels hb W), (pathLabels hb W) .key) := by
  simp only [genMaskedWith, simulateQ_bind, simulateQ_pure]
  rw [simulateQ_queryPath, pure_bind]
  rw [fixedPath_eq_pathLabels_of_answers hb hB salt x z H W hread]

/-- Distinct programmed inputs make the source masked-link generator recover the prescribed
public puzzle and key. The table is the named complete raw programmer. -/
theorem simulateQ_genMaskedWith_programPath_of_injective
    (hb : b ≤ 32) (hB : hashInputBound b ≤ B)
    (salt : Bytes 16) (x : Bytes b) (z : Fin (n - 1) → Bytes b)
    (H : ByteArray.Bounded B → Bytes 32) (W : PathValue n m → Bytes 32)
    (hinj : Function.Injective (fun v ↦ rawPathInput hb hB salt x z v W)) :
    simulateQ (impl (extendWindowOracle (programPath hb hB salt x z H W)) b n)
      (genMaskedWith m (ctx b n m) id salt x z) =
      pure (labelPuzzle salt x z (pathLabels hb W), (pathLabels hb W) .key) :=
  simulateQ_genMaskedWith_of_answers hb hB salt x z _ W
    (programPath_apply_of_injective hb hB salt x z H W hinj)

end PointerChainPuzzle.LeanSeal
