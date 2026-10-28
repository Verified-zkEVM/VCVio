/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.MasterBound
public import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.List.GetD

/-! # Accessible polynomial spans

The accessible span is the least family of submodules containing the initial tables and
closed under the signature's structure maps. Every symbolic run stays in this family.
-/

public section

open OracleComp OracleSpec

namespace GroupModel

variable {F S ι : Type}

/-- Closure of polynomial submodules under the symbolic linear and bilinear maps. -/
@[expose] def Sig.SpanClosed [CommSemiring F] (σ : Sig S)
    (V : S → Submodule F (MvPolynomial ι F)) : Prop :=
  (∀ o, V (σ.lsrc o) ≤ V (σ.ltgt o)) ∧
    (∀ o p q, p ∈ V (σ.src₁ o) → q ∈ V (σ.src₂ o) → p * q ∈ V (σ.tgt o))

/-- The intersection of all closed families containing the initial polynomial tables. -/
@[expose] noncomputable def accessibleSpan [CommSemiring F] (σ : Sig S)
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (s : S) : Submodule F (MvPolynomial ι F) :=
  ⨅ (V : {V : S → Submodule F (MvPolynomial ι F) //
    σ.SpanClosed V ∧ ∀ t p, p ∈ tbl t → p ∈ V t}), V.val s

/-- Every initial table entry belongs to the accessible span of its sort. -/
theorem mem_accessibleSpan [CommSemiring F] (σ : Sig S)
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (s : S) {p : MvPolynomial ι F}
    (hp : p ∈ tbl s) : p ∈ accessibleSpan σ tbl s := by
  exact (Submodule.mem_iInf _).mpr (fun V => V.property.2 s p hp)

/-- The accessible span is contained in every closed family containing the tables. -/
theorem accessibleSpan_le [CommSemiring F] (σ : Sig S)
    (tbl : Tbl (fun _ : S => MvPolynomial ι F))
    (V : S → Submodule F (MvPolynomial ι F)) (hV : σ.SpanClosed V)
    (htbl : ∀ s p, p ∈ tbl s → p ∈ V s) (s : S) : accessibleSpan σ tbl s ≤ V s :=
  iInf_le_of_le ⟨V, hV, htbl⟩ le_rfl

/-- The accessible span is closed under all structure maps of the signature. -/
theorem accessibleSpan_spanClosed [CommSemiring F] (σ : Sig S)
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) : σ.SpanClosed (accessibleSpan σ tbl) := by
  constructor
  · intro o p hp
    exact (Submodule.mem_iInf _).mpr (fun V => V.property.1.1 o ((Submodule.mem_iInf _).mp hp V))
  · intro o p q hp hq
    exact (Submodule.mem_iInf _).mpr (fun V =>
      V.property.1.2 o p q ((Submodule.mem_iInf _).mp hp V) ((Submodule.mem_iInf _).mp hq V))

/-- Lookup stays in a submodule containing the table, including the zero default. -/
theorem lookup_mem_submodule [CommSemiring F]
    {V : S → Submodule F (MvPolynomial ι F)}
    {tbl : Tbl (fun _ : S => MvPolynomial ι F)}
    (h : ∀ s p, p ∈ tbl s → p ∈ V s) (s : S) (a : Handle) : lookup tbl s a ∈ V s := by
  by_cases ha : a < (tbl s).length
  · exact h s _ (by simpa only [lookup, List.getD_eq_getElem _ _ ha] using List.getElem_mem ha)
  · simpa only [lookup, List.getD_eq_default _ _ (Nat.le_of_not_gt ha)] using (V s).zero_mem

private theorem append_mem_submodule [CommSemiring F] [DecidableEq S]
    {V : S → Submodule F (MvPolynomial ι F)}
    {tbl : Tbl (fun _ : S => MvPolynomial ι F)}
    (h : ∀ s p, p ∈ tbl s → p ∈ V s) (s : S) (p : MvPolynomial ι F) (hp : p ∈ V s) :
    ∀ t q, q ∈ append tbl s p t → q ∈ V t := by
  intro t q hq
  by_cases ht : t = s
  · subst t
    simp only [append, Function.update_self, List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact h s q hq
    · exact hp
  · exact h t q (by simpa [append, ht] using hq)

private theorem impl_mem_submodule [CommSemiring F] [DecidableEq S]
    {σ : Sig S} {V : S → Submodule F (MvPolynomial ι F)} (hV : σ.SpanClosed V)
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (obs : (s : S) → MvPolynomial ι F → U s) (t : Query F σ)
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (htbl : ∀ s p, p ∈ tbl s → p ∈ V s)
    (z : spec F σ t × Tbl (fun _ : S => MvPolynomial ι F))
    (hz : z ∈ support ((impl (symbolic F σ ι) obs ProbComp t).run tbl)) :
    ∀ s p, p ∈ z.2 s → p ∈ V s := by
  cases t with
  | eq s a b =>
    have he : z.2 = tbl := impl_table_step (symbolic F σ ι) obs (.eq s a b) tbl z hz
    simpa only [he] using htbl
  | add s a b | smul s c a | lin o a | bil o a b =>
    simp only [impl, push, StateT.run, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet] at hz
    replace hz := (mem_support_pure_iff _ _).mp hz
    subst z
    apply append_mem_submodule htbl
    try simp only [symbolic_lin_apply, symbolic_bil_apply]
    first
    | exact (V s).add_mem (lookup_mem_submodule htbl s a) (lookup_mem_submodule htbl s b)
    | exact (V s).smul_mem c (lookup_mem_submodule htbl s a)
    | exact hV.1 o (lookup_mem_submodule htbl (σ.lsrc o) a)
    | exact hV.2 o _ _ (lookup_mem_submodule htbl (σ.src₁ o) a)
        (lookup_mem_submodule htbl (σ.src₂ o) b)

private theorem runGen_mem_submodule [CommSemiring F] [DecidableEq S]
    {σ : Sig S} {V : S → Submodule F (MvPolynomial ι F)} (hV : σ.SpanClosed V)
    {U : S → Type} [∀ s, DecidableEq (U s)]
    (obs : (s : S) → MvPolynomial ι F → U s) {α : Type}
    (oa : OracleComp (genSpec F σ) α)
    (tbl : Tbl (fun _ : S => MvPolynomial ι F)) (htbl : ∀ s p, p ∈ tbl s → p ∈ V s)
    (z : α × Tbl (fun _ : S => MvPolynomial ι F))
    (hz : z ∈ support (runGen (symbolic F σ ι) obs oa tbl)) :
    ∀ s p, p ∈ z.2 s → p ∈ V s := by
  induction oa using OracleComp.inductionOn generalizing tbl with
  | pure a =>
    simp only [runGen, run, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst z
    exact htbl
  | query_bind t k ih =>
    simp only [runGen, run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    apply ih w.1 w.2 _ hz
    cases t with
    | inl t => exact impl_mem_submodule hV obs t tbl htbl w hw
    | inr t => simpa only [preservesTbl_coins t tbl w hw] using htbl

/-- Every entry reached by a symbolic run belongs to the initial accessible span. -/
theorem runGen_mem_accessibleSpan [CommSemiring F] [DecidableEq S]
    {σ : Sig S} {U : S → Type} [∀ s, DecidableEq (U s)]
    (obs : (s : S) → MvPolynomial ι F → U s) {α : Type}
    (oa : OracleComp (genSpec F σ) α) (tbl : Tbl (fun _ : S => MvPolynomial ι F))
    (z : α × Tbl (fun _ : S => MvPolynomial ι F))
    (hz : z ∈ support (runGen (symbolic F σ ι) obs oa tbl)) :
    ∀ s p, p ∈ z.2 s → p ∈ accessibleSpan σ tbl s :=
  runGen_mem_submodule (accessibleSpan_spanClosed σ tbl) obs oa tbl
    (fun s _ hp => mem_accessibleSpan σ tbl s hp) z hz

/-- The explicit Type 3 spans: source entries, and target entries together with source products. -/
@[expose] noncomputable def pairingSpan [CommSemiring F]
    (tbl : Tbl (fun _ : PSort => MvPolynomial ι F)) : PSort → Submodule F (MvPolynomial ι F)
  | .g₁ => Submodule.span F {p | p ∈ tbl .g₁}
  | .g₂ => Submodule.span F {p | p ∈ tbl .g₂}
  | .gₜ => Submodule.span F ({p | p ∈ tbl .gₜ} ∪
      {r | ∃ p ∈ tbl .g₁, ∃ q ∈ tbl .g₂, r = p * q})

private theorem pairingSpan_closed [CommSemiring F]
    (tbl : Tbl (fun _ : PSort => MvPolynomial ι F)) : pairingSig.SpanClosed (pairingSpan tbl) := by
  refine ⟨fun o => o.elim, ?_⟩
  intro o p q hp hq
  change p * q ∈ pairingSpan tbl .gₜ
  change p ∈ Submodule.span F {p | p ∈ tbl .g₁} at hp
  change q ∈ Submodule.span F {q | q ∈ tbl .g₂} at hq
  induction hp using Submodule.span_induction with
  | mem p hp =>
    induction hq using Submodule.span_induction with
    | mem q hq => exact Submodule.subset_span (Or.inr ⟨p, hp, q, hq, rfl⟩)
    | zero => simp
    | add q r _ _ hq hr => simpa only [mul_add] using (pairingSpan tbl .gₜ).add_mem hq hr
    | smul c q _ hq => simpa only [mul_smul_comm] using (pairingSpan tbl .gₜ).smul_mem c hq
  | zero => simp
  | add p r _ _ hp hr => simpa only [add_mul] using (pairingSpan tbl .gₜ).add_mem hp hr
  | smul c p _ hp => simpa only [smul_mul_assoc] using (pairingSpan tbl .gₜ).smul_mem c hp

/-- At Type 3 the accessible spans are exactly the source spans and target/product span. -/
theorem accessibleSpan_pairingSig [CommSemiring F]
    (tbl : Tbl (fun _ : PSort => MvPolynomial ι F)) (s : PSort) :
    accessibleSpan pairingSig tbl s = pairingSpan tbl s := by
  apply le_antisymm
  · apply accessibleSpan_le pairingSig tbl _ (pairingSpan_closed tbl)
    intro t p hp
    cases t with
    | g₁ | g₂ => exact Submodule.subset_span hp
    | gₜ => exact Submodule.subset_span (Or.inl hp)
  · cases s with
    | g₁ | g₂ => exact Submodule.span_le.mpr (fun _ hp => mem_accessibleSpan _ _ _ hp)
    | gₜ =>
      apply Submodule.span_le.mpr
      intro r hr
      rcases hr with hr | ⟨p, hp, q, hq, rfl⟩
      · exact mem_accessibleSpan _ _ _ hr
      · exact (accessibleSpan_spanClosed pairingSig tbl).2 () p q
          (mem_accessibleSpan _ _ _ hp) (mem_accessibleSpan _ _ _ hq)

end GroupModel
