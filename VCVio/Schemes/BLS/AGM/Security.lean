/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.BLS.AGM.Reductions
import all VCVio.Schemes.BLS.AGM.Reductions
import VCVio.CryptoFoundations.GroupModel.LinearFunctional.TraceExtraction
import VCVio.CryptoFoundations.GroupModel.LinearFunctional.LazyCover

/-! # Tight algebraic security of BLS

This follows Gurkan's linear-functional proof of BLS security in the algebraic group model
of Fuchsbauer, Kiltz and Loss (CRYPTO 2018). A finite cover exists for every adaptive execution
family but is used only in the proof. Both reductions execute the original chronological
adversary with a lazy cache over arbitrary messages.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace BLS.AGM

private abbrev Trace (F M G₁ G₂ : Type) := Explained F M (Group G₁ G₂) × Transcript M

private def table {F M : Type} [Zero F] [DecidableEq M]
    (S : Finset M) (ρ : S → F) : M → F := GroupModel.LinearFunctional.extendTable S 0 ρ

private def goodRep {F M G₁ G₂ : Type} [Semiring F]
    (ρ : M → F) (z : Trace F M G₁ G₂) : F × F :=
  evaluate (BLS.coefficients z.1) ([(1, 0), (0, 1)] ++
    z.2.map (fun q => if q.1 then (0, ρ q.2) else (ρ q.2, 0)))

private def functional {F M G₁ G₂ : Type} [Semiring F] [DecidableEq M]
    (S : Finset M) (z : Trace F M G₁ G₂) : F × (S → F) :=
  traceFunctional (labelWeight S) (BLS.coefficients z.1) z.2

private def gap {F M G₁ G₂ : Type} [Ring F] [DecidableEq M]
    (S : Finset M) (z : Trace F M G₁ G₂) (i : S) : F :=
  labelWeight S z.1.value.data i - (functional S z).2 i

private theorem gap_eq {F M G₁ G₂ : Type} [CommRing F] [DecidableEq M]
    (S : Finset M) (ρ : S → F) (z : Trace F M G₁ G₂) :
    table S ρ z.1.value.data - (goodRep (table S ρ) z).2 =
      (∑ i, gap S z i * ρ i) - (functional S z).1 := by
  have h := traceFunctional_good (labelWeight S) (BLS.coefficients z.1) z.2 ρ
  simp only [sum_labelWeight_mul] at h
  change (goodRep (table S ρ) z).2 =
    (functional S z).1 + ∑ i, (functional S z).2 i * ρ i at h
  rw [h]
  simp only [gap, sub_mul, Finset.sum_sub_distrib, sum_labelWeight_mul, table]
  ring

private theorem gap_target {F M G₁ G₂ : Type} [Ring F] [DecidableEq M]
    (S : Finset M) (z : Trace F M G₁ G₂) (hm : z.1.value.data ∈ S)
    (hfresh : z.1.value.data ∉ signedMessages z.2) :
    gap S z ⟨z.1.value.data, hm⟩ = 1 := by
  have h := traceFunctional_apply_eq_zero (labelWeight S) (BLS.coefficients z.1) z.2
    (⟨z.1.value.data, hm⟩ : S) (by
      intro q hq hb
      have hn : q.2 ≠ z.1.value.data := by
        intro he
        apply hfresh
        exact List.mem_filterMap.mpr ⟨q, hq, by simp [hb, he]⟩
      simp [labelWeight, hn])
  simpa [gap, functional, labelWeight] using congrArg (fun x : F => 1 - x) h

private def view {F M G₁ G₂ Gₜ : Type} [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F M G₁ G₂ e g₁ g₂) (ρ : M → F) (κ : F) :=
  fixedRun (fun m => ρ m • g₁) (fun m => κ • (ρ m • g₁))
    (rawMain A (κ • g₁, κ • g₂))

private theorem goodReduction_table {F M G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq M]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F M G₁ G₂ e g₁ g₂) (κ : F)
    (S : Finset M) (hS : InterfaceCovered S (fun out => out.value.data)
      (rawMain A (κ • g₁, κ • g₂))) :
    BLS.goodReduction A g₁ (κ • g₁) g₂ (κ • g₂) =ᵈ
      (do let ρ ← $ᵗ (S → F)
          let z ← view A (table S ρ) κ
          return (goodRep (table S ρ) z).1 /
            (table S ρ z.1.value.data - (goodRep (table S ρ) z).2)) := by
  have h := (reductionRun_eq_table A (κ • g₁, κ • g₂)
    (fun ρ : F => ρ • g₁) (fun ρ => ρ • (κ • g₁))
    (fun ρ => (ρ, (0 : F))) (fun ρ => ((0 : F), ρ)) [(1, 0), (0, 1)] S hS 0).map
      (fun z => (evaluate (BLS.coefficients z.1) z.2.1).1 /
        (z.2.2 - (evaluate (BLS.coefficients z.1) z.2.1).2))
  simpa only [BLS.goodReduction, bind_pure_comp, map_bind, map_pure, Functor.map_map, view, table,
    goodRep, Function.comp_def, smul_smul, mul_comm] using h

private theorem pair_tables {F ι : Type} [SampleableType F] [Fintype ι] [DecidableEq ι] :
    (do let a ← $ᵗ (ι → F); let b ← $ᵗ (ι → F); return fun i => (a i, b i)) =ᵈ
      ($ᵗ (ι → F × F) : ProbComp _) := by
  apply SampleableType.evalDistEq_uniformSample_pair_of_bijective
  constructor
  · intro ⟨a, b⟩ ⟨c, d⟩ h
    exact Prod.ext (funext fun i => congrArg Prod.fst (congrFun h i))
      (funext fun i => congrArg Prod.snd (congrFun h i))
  · intro ρ
    exact ⟨(fun i => (ρ i).1, fun i => (ρ i).2), rfl⟩

private theorem table_pair {F M : Type} [Zero F] [DecidableEq M]
    (S : Finset M) (a b : S → F) (m : M) :
    GroupModel.LinearFunctional.extendTable S (0, 0) (fun i => (a i, b i)) m =
      (table S a m, table S b m) := by
  simp only [GroupModel.LinearFunctional.extendTable, table]
  split <;> rfl

private theorem table_affine {F M : Type} [Ring F] [DecidableEq M]
    (S : Finset M) (a b : S → F) (α : F) (m : M) :
    table S (fun i => a i * α + b i) m = table S a m * α + table S b m := by
  simp only [table, GroupModel.LinearFunctional.extendTable]
  split <;> simp

private theorem badReduction_table {F M G₁ G₂ Gₜ : Type}
    [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ] [DecidableEq M]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F M G₁ G₂ e g₁ g₂) (α : F)
    (S : Finset M) (hS : ∀ κ : F, InterfaceCovered S (fun out => out.value.data)
      (rawMain A (κ • g₁, κ • g₂))) :
    BLS.badReduction A g₁ (α • g₁) g₂ (α • g₂) =ᵈ
      (do let κ ← $ᵗ F
          let a ← $ᵗ (S → F); let b ← $ᵗ (S → F)
          let z ← view A (table S (fun i => a i * α + b i)) κ
          return ((functional S z).1 - ∑ i, gap S z i * b i) /
            (∑ i, gap S z i * a i)) := by
  unfold BLS.badReduction
  apply _root_.EvalDistEq.bind_right
  intro κ
  have h := (reductionRun_eq_table A (κ • g₁, κ • g₂)
    (fun r : F × F => r.1 • (α • g₁) + r.2 • g₁)
    (fun r => κ • (r.1 • (α • g₁) + r.2 • g₁))
    (fun _ => ((0 : F), (0 : F))) id [(0, 0), (0, 1)] S (hS κ) (0, 0)).map
      (fun z => ((evaluate (BLS.coefficients z.1) z.2.1).2 - z.2.2.2) /
        (z.2.2.1 - (evaluate (BLS.coefficients z.1) z.2.1).1))
  simp only [bind_pure_comp]
  refine _root_.EvalDistEq.trans (m'' := ProbComp) h ?_
  have ht := (pair_tables (F := F) (ι := S)).bind_left (fun ρ => do
    let z ← fixedRun
      (fun m => (GroupModel.LinearFunctional.extendTable S (0, 0) ρ m).1 • (α • g₁) +
        (GroupModel.LinearFunctional.extendTable S (0, 0) ρ m).2 • g₁)
      (fun m => κ • ((GroupModel.LinearFunctional.extendTable S (0, 0) ρ m).1 • (α • g₁) +
        (GroupModel.LinearFunctional.extendTable S (0, 0) ρ m).2 • g₁))
      (rawMain A (κ • g₁, κ • g₂))
    let repr := evaluate (BLS.coefficients z.1) ([(0, 0), (0, 1)] ++
      z.2.map (fun q => if q.1 then
        GroupModel.LinearFunctional.extendTable S (0, 0) ρ q.2 else (0, 0)))
    return (repr.2 - (GroupModel.LinearFunctional.extendTable S (0, 0) ρ z.1.value.data).2) /
      ((GroupModel.LinearFunctional.extendTable S (0, 0) ρ z.1.value.data).1 - repr.1))
  simp only [map_bind, map_pure, bind_assoc, pure_bind,
    Function.comp_def, id_eq] at ht ⊢
  refine ht.symm.trans ?_
  apply _root_.EvalDistEq.bind_right
  intro a
  apply _root_.EvalDistEq.bind_right
  intro b
  simp only [table_pair, view, table_affine, add_smul, mul_smul, bind_pure_comp]
  convert _root_.EvalDistEq.refl _ using 1
  congr 1
  funext z
  have hr := traceFunctional_bad (labelWeight S) (BLS.coefficients z.1) z.2 a b
  simp only [sum_labelWeight_mul] at hr
  simp only [table]
  rw [hr]
  simp only [functional, gap, sub_mul, Finset.sum_sub_distrib, sum_labelWeight_mul]
  congr 1
  ring

end BLS.AGM

namespace BLS

/-- BLS is tightly EUF-CMA secure against the shared algebraic adversary in the random-oracle
model under the two explicit (1,1)-discrete-logarithm reductions. The single field-sized loss
is the collision probability of a hidden affine slope. Messages and query counts are unrestricted.
-/
theorem unforgeableAdvantage_le_of_algebraic {F M G₁ G₂ Gₜ : Type}
    [Field F] [Fintype F] [SampleableType F] [DecidableEq F]
    [AddCommGroup G₁] [Module F G₁] [SampleableType G₁]
    [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
    [DecidableEq Gₜ] [DecidableEq M]
    {e : G₁ →ₗ[F] G₂ →ₗ[F] Gₜ} {g₁ : G₁} {g₂ : G₂}
    (A : AlgebraicAdversary F M G₁ G₂ e g₁ g₂)
    (hg₁ : Function.Bijective (· • g₁ : F → G₁)) (he : e g₁ g₂ ≠ 0) :
    SignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (M →ₒ G₁))
      A.toUnforgeableAdversary ≤
      Pr{let b ← DLog11.experiment g₁ g₂ (goodReduction A)}[b = true] +
      Pr{let b ← DLog11.experiment g₁ g₂ (badReduction A)}[b = true] +
      1 / Fintype.card F := by
  classical
  obtain ⟨S, hS⟩ := exists_interface_cover (fun out => out.value.data)
    (fun κ : F => AGM.rawMain A (κ • g₁, κ • g₂))
  let pub := fun ρ : S → F => do
    let κ ← ($ᵗ F : ProbComp F)
    let z ← AGM.view A (AGM.table S ρ) κ
    return (κ, z)
  let game := do
    let ρ ← ($ᵗ (S → F) : ProbComp _)
    let z ← pub ρ
    return (ρ, z)
  let win := fun z : (S → F) × F × AGM.Trace F M G₁ G₂ =>
    z.2.2.1.value.data ∉ AGM.signedMessages z.2.2.2 ∧
      (AGM.forgery z.2.2.1).2 = z.2.1 • (AGM.table S z.1 z.2.2.1.value.data • g₁)
  let good := fun z : (S → F) × F × AGM.Trace F M G₁ G₂ =>
    (AGM.goodRep (AGM.table S z.1) z.2.2).1 /
      (AGM.table S z.1 z.2.2.1.value.data - (AGM.goodRep (AGM.table S z.1) z.2.2).2) = z.2.1
  let bad := fun z : (S → F) × F × AGM.Trace F M G₁ G₂ =>
    z.2.2.1.value.data ∉ AGM.signedMessages z.2.2.2 ∧
      ∑ i, AGM.gap S z.2.2 i * z.1 i = (AGM.functional S z.2.2).1
  have horder : (do
      let κ ← ($ᵗ F : ProbComp F); let ρ ← $ᵗ (S → F)
      let z ← AGM.view A (AGM.table S ρ) κ
      return (ρ, κ, z)) =ᵈ game := by
    simpa only [game, pub, bind_assoc, pure_bind] using
      OracleComp.EvalDistEq.bind_bind_swap ($ᵗ F) ($ᵗ (S → F))
        (fun κ ρ => do let z ← AGM.view A (AGM.table S ρ) κ; return (ρ, κ, z))
  have hgame : SignatureAlg.unforgeableAdvantage (ProbCompRuntime.rom (M →ₒ G₁))
      A.toUnforgeableAdversary = Pr{let z ← game}[win z] := by
    rw [AGM.unforgeableAdvantage_eq_table A hg₁ he S hS]
    simpa only [prEvent_norm, win, AGM.view, AGM.table] using horder.prEvent_eq win
  have hgood : Pr{let b ← DLog11.experiment g₁ g₂ (goodReduction A)}[b = true] =
      Pr{let z ← game}[good z] := by
    rw [← horder.prEvent_eq good]
    simp only [DLog11.experiment, prEvent_norm, decide_eq_true_eq]
    let : MeasurableSpace F := ⊤
    rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
    apply MeasureTheory.lintegral_congr
    intro κ
    simpa only [good, prEvent_norm] using
      (AGM.goodReduction_table A κ S (hS κ)).prEvent_eq (· = κ)
  have hsplit : Pr{let z ← game}[win z] ≤
      Pr{let z ← game}[good z] + Pr{let z ← game}[bad z] := by
    apply (prEvent_mono_of_support game win (fun z => good z ∨ bad z) ?_).trans
      (prEvent_or_le game good bad)
    intro z hz hw
    obtain ⟨ρ, _, v, hv, rfl⟩ := by
      simpa only [game, support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff] using hz
    obtain ⟨κ, _, t, ht, rfl⟩ := by
      simpa only [pub, support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff] using hv
    change _ ∧ _ at hw
    have hs := AGM.fixedRun_good_sound A κ (AGM.table S ρ) t ht
    change (AGM.forgery t.1).2 =
      ((AGM.goodRep (AGM.table S ρ) t).1 + (AGM.goodRep (AGM.table S ρ) t).2 * κ) • g₁ at hs
    have hverify := hw.2
    simp only [smul_smul] at hverify
    have heq := hg₁.1 (hs.symm.trans hverify)
    by_cases hgap : AGM.table S ρ t.1.value.data - (AGM.goodRep (AGM.table S ρ) t).2 = 0
    · apply Or.inr
      refine ⟨hw.1, ?_⟩
      exact sub_eq_zero.mp ((AGM.gap_eq S ρ t).symm.trans hgap)
    · apply Or.inl
      change _ / _ = κ
      apply (div_eq_iff hgap).2
      linear_combination heq
  obtain ⟨z₀, hz₀⟩ := support_nonempty (AGM.view A (fun _ => 0) (0 : F))
  have hm₀ := (fixedRun_mem_cover S (fun out => out.value.data) _ _ _ (hS 0) z₀ hz₀).1
  let j := fun z : F × AGM.Trace F M G₁ G₂ =>
    if hm : z.2.1.value.data ∈ S then (⟨z.2.1.value.data, hm⟩ : S) else ⟨z₀.1.value.data, hm₀⟩
  have hL : ∀ ρ z, z ∈ support (pub ρ) →
      z.2.1.value.data ∉ AGM.signedMessages z.2.2 → AGM.gap S z.2 (j z) ≠ 0 := by
    intro ρ z hz hfresh
    obtain ⟨κ, _, t, ht, rfl⟩ := by
      simpa only [pub, support_bind, Set.mem_iUnion, support_pure,
        Set.mem_singleton_iff] using hz
    have hm := (fixedRun_mem_cover S (fun out => out.value.data) _ _ _ (hS κ) t ht).1
    simpa only [j, dite_eq_left hm, AGM.gap_target S t hm hfresh] using (one_ne_zero : (1 : F) ≠ 0)
  have hb := prEvent_zero_gap_le_uniform_affine_extract_add pub
    (fun z => AGM.gap S z.2) (fun z => (AGM.functional S z.2).1)
    (fun z => z.2.1.value.data ∉ AGM.signedMessages z.2.2) j hL
  have hbad : Pr{let b ← DLog11.experiment g₁ g₂ (badReduction A)}[b = true] =
      Pr{let α ← ($ᵗ F : ProbComp F)
         let a ← $ᵗ (S → F); let b ← $ᵗ (S → F)
         let z ← pub (fun i => a i * α + b i)}[
        ((AGM.functional S z.2).1 - ∑ i, AGM.gap S z.2 i * b i) /
          (∑ i, AGM.gap S z.2 i * a i) = α] := by
    simp only [DLog11.experiment, prEvent_norm, decide_eq_true_eq]
    let : MeasurableSpace F := ⊤
    rw [prEvent_bind_of_discrete, prEvent_bind_of_discrete]
    apply MeasureTheory.lintegral_congr
    intro α
    rw [(AGM.badReduction_table A α S hS).prEvent_eq (· = α)]
    have hswap := OracleComp.EvalDistEq.bind_bind_swap ($ᵗ F)
      (do let a ← ($ᵗ (S → F) : ProbComp _); let b ← $ᵗ (S → F); return (a, b))
      (fun κ ab => do
        let z ← AGM.view A (AGM.table S (fun i => ab.1 i * α + ab.2 i)) κ
        return ((AGM.functional S z).1 - ∑ i, AGM.gap S z i * ab.2 i) /
          (∑ i, AGM.gap S z i * ab.1 i))
    simpa only [pub, prEvent_norm] using hswap.prEvent_eq (· = α)
  have hb' : Pr{let z ← game}[bad z] ≤
      Pr{let b ← DLog11.experiment g₁ g₂ (badReduction A)}[b = true] +
        1 / Fintype.card F := by
    rw [hbad]
    simpa only [game, bad, prEvent_norm] using hb
  rw [hgame, hgood]
  exact hsplit.trans (by simpa only [add_assoc] using add_le_add (le_refl _) hb')

end BLS
