/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.ByteLinkedBound
public import VCVio.OracleComp.QueryTracking.RandomOracle.ProjectedHazards
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# The virtual hit and the honest input at a linked point, charged

At `n = 32`, `HashSig.SLHDSA.Security.ByteLinkedBound` bounds the strong advantage against SLH-DSA
over one SHAKE256 oracle, at a public seed, by the events of the verifying run plus the cost `κ` of
a further charge (`DeferredCharge`) to which the virtual hit (`VirtualHit`) and the honest input at
a linked point (`LinkedHonestInput`) are charged. This module supplies that charge, `linkedCharge`,
at every public seed, with `κ = (qs + 1) / |Y|`. It is a classical random-oracle statement; nothing
here is quantum.

## The charge

* **The virtual hit is a projected hit** (`projHazard_of_virtualHit_fill`). Its honest entry is
  the point of a node `κ` at its drawn children, so its cached value is the label of `κ`, and the
  linked point at its key reads an `H_msg` point `H_msg(PK.seed, PK.seed, ·, ·)` whose first `n`
  bytes are that label. The projected keys of the linked points (`linkedProjKeys`) read such an
  answer, through its first `n` bytes (uniform, `prEvent_uniformSample_prefixBytes_eq`), at the node
  at the key with the bytes of `PK.seed`, so each such entry is charged `1 / |Y|` once
  (`CanonicalGraph.ProjKeys.isCharged`).
* **The honest input at a linked point is a root event** (`rootCharge_of_linkedHonestInput_fill`).
  The root cell holds `PK.root` (`cell_rootNode_of_mem_support_deferredImpl_labExperiment`), the
  first input of a linked point. If the key with the bytes of `PK.seed` is the key of a node `κ₀`,
  the first child cell of `κ₀` holds the value of the root cell, a distinct cell
  (`inr_rootNode_not_mem_ch`), so the two are drawn equal (`CanonicalGraph.isCharged_pairHazard`);
  otherwise the honest input is a secret queried at a linked point, and the first secret seed is
  the value of the root cell. Either costs `1 / |Y|`, and exactly one case is charged per seed.

## The budget

Every projected entry is a cached `H_msg` point. With `a` the public entries at node keys, `b`
the cached derivable public points and `h` the cached `H_msg` points of a lab run of an adversary
with budget `(qh, qs)`, `a + b ≤ qh + V` and `a + b + h ≤ qh + qs + V`. So at the verifying
adversary, of budget `(qh + V, qs)`, the joint budget with the linked charge exceeds the joint
budget of `HashSig.SLHDSA.Security.ByteLinkedBound` by `(qs + 1) / |Y|`, with the charge of the
message-`PRF` key and with the fixed-key charge alike.

## Main statements

- `shakeStrongAdvantage_pure_le_securityBound_add_of_n_eq_32`: at `n = 32`, at every public seed and
  every `opt_rand` distribution, the strong advantage is at most
  `securityBound vp.params |Y| 2 1 (qh + V) qs + (qs + 1) / |Y| + (qs + 1) / |Y|`.
- `shakeStrongAdvantage_pure_le_securityBound_add_of_n_eq_32_hedged`: the hedged form, with
  `(qs + 1) / |Y|` added to the hedged bound of `HashSig.SLHDSA.Security.ByteLinkedBound`.
-/

public section

open OracleComp OracleSpec SignatureAlg
open scoped ENNReal

namespace SLHDSA.Security

open Concrete

/-! ## The projected keys at `n = 32` -/

section Shake

variable {vp : ValidatedParams}

variable (vp) in
open Classical in
/-- The node at whose key an `H_msg` point `H_msg(PK.seed, PK.seed, ·, ·)` is read at public seed
`pkSeed`: the node at the key with the bytes of `PK.seed`, if there is one. No other point is
read at a node. -/
noncomputable def linkedNode (pkSeed : (shakeCore vp).PkSeed) :
    (hashSpec (shakeCore vp)).Domain → Option (NodeKey (shakeCore vp))
  | .inl (.hmsg R s _ _) =>
      if h : R = pkSeed ∧ s = pkSeed ∧ ∃ a ∈ constructionAddresses vp,
          (shakeCore vp).adrsToKey a = adrsKeyOfList vp (Vector.toList (pkSeed : Bytes vp.params.n))
        then some ⟨_, h.2.2⟩ else none
  | _ => none

variable (vp) in
/-- An answer read as a label: the first `n` bytes of an `H_msg` answer, any other answer as is. -/
def linkedProj : (t : (hashSpec (shakeCore vp)).Domain) → (hashSpec (shakeCore vp)).Range t →
    (shakeCore vp).Y
  | .inl (.thash _ _ _) => id
  | .inl (.hmsg _ _ _ _) => prefixBytes vp.params.n
  | .inr _ => id

/-- **The projected keys of the linked points** at public seed `pkSeed`: an `H_msg` point
`H_msg(PK.seed, PK.seed, ·, ·)` is read, through its first `n` bytes, at the node at the key with
the bytes of `PK.seed`. -/
noncomputable def linkedProjKeys (hnm : vp.params.n ≤ vp.params.m)
    (pkSeed : (shakeCore vp).PkSeed) : (slhGraph (shakeCore vp) pkSeed).ProjKeys where
  node := linkedNode vp pkSeed
  proj := linkedProj vp
  prEvent_proj_le t k h ℓ := by
    rcases t with (_ | ⟨R, s, r, msg⟩) | _
    · simp [linkedNode] at h
    · rw [SampleableType.prEvent_uniformSample_inst_irrel _ (inferInstanceAs (SampleableType
        (Bytes vp.params.m)))]
      exact (prEvent_uniformSample_prefixBytes_eq hnm ℓ).le
    · simp [linkedNode] at h

/-- Every public entry at a projected key is a cached `H_msg` point. -/
theorem encard_keyEntries_linkedProjKeys_le (hnm : vp.params.n ≤ vp.params.m)
    (pkSeed : (shakeCore vp).PkSeed) (C : (hashSpec (shakeCore vp)).QueryCache) :
    ((linkedProjKeys hnm pkSeed).keyEntries C).encard ≤
      {t | (C t).isSome ∧ IsHmsgPoint (core := shakeCore vp) t}.encard := by
  refine Set.encard_le_encard fun t ⟨hC, hk⟩ ↦ ⟨hC, ?_⟩
  rcases t with (_ | _) | _
  · simp [linkedProjKeys, linkedNode] at hk
  · trivial
  · simp [linkedProjKeys, linkedNode] at hk

variable {pkSeed : (shakeCore vp).PkSeed} {s : (shakeCore vp).SkSeed × (shakeCore vp).SkPrf}
  {st : LabState (shakeCore vp)} {o : DeriveOutcome (shakeCore vp)}

/-- An address key with the bytes of `PK.seed` is the key read off `PK.seed`. -/
private theorem eq_adrsKeyOfList {k : (shakeCore vp).AdrsKey}
    (hks : Vector.toList (k : Bytes 32) = Vector.toList (pkSeed : Bytes vp.params.n)) :
    k = adrsKeyOfList vp (Vector.toList (pkSeed : Bytes vp.params.n)) := by
  rw [adrsKeyOfList, ← hks]
  exact (bytesOfList_toList (k : Bytes 32)).symm

/-- **A virtual hit is a projected hit.** Under the key discipline, a virtual hit of the
transcript rebuilt with the seeds `s`, on the cache that the relabelled state `st` stands for at
them, is a projected hit of `st` at the projected keys of the linked points. -/
theorem projHazard_of_virtualHit_fill (hd : (shakeCore vp).KeyDiscipline vp)
    (hnm : vp.params.n ≤ vp.params.m) (hpk : o.pk.pkSeed = pkSeed)
    (h : VirtualHit vp (DeriveOutcome.fill (shakeCore vp) s o,
      (secretEncoding (shakeCore vp) (Equiv.refl _) pkSeed).merge s
        ((slhGraph (shakeCore vp) pkSeed).toSplitCache st))) :
    (linkedProjKeys hnm pkSeed).ProjHazard st := by
  obtain ⟨k, xs, r, rest, u, hhon, hL, hu, hx⟩ := h
  rw [DeriveOutcome.fill_pk, DeriveOutcome.fill_sk_skSeed, hpk] at hhon
  rw [DeriveOutcome.fill_pk, hpk] at hL hu hx
  obtain ⟨κ, vs, hκ, hpt⟩ := exists_childVals_eq_some_of_honestEntry hd hhon
  simp only [slhGraph_pt, Sum.inl.injEq, PublicHashQuery.thash.injEq, true_and] at hpt
  obtain ⟨rfl, rfl⟩ := hpt
  have hk := eq_adrsKeyOfList hL.2.1
  have hnode : linkedNode vp pkSeed (.inl (linkedHmsg vp pkSeed r rest)) = some κ := by
    simp only [linkedNode]
    split_ifs with hc
    · exact congrArg some (Subtype.ext hk.symm)
    · exact absurd ⟨rfl, rfl, hk ▸ κ.2⟩ hc
  refine ⟨.inl (linkedHmsg vp pkSeed r rest), κ, prefixBytes vp.params.n u, u, hnode, ?_, ?_, rfl⟩
  · exact (merge_fst_thash_of_childVals_eq_some hd.keySeparated hκ).symm.trans hx
  · exact (merge_fst_hmsg _ _ _ _).symm.trans hu

/-! ## The charge -/

/-- A uniform first secret seed is the value of the root cell with probability at most
`1 / |Y|`. -/
theorem prEvent_rootSeed_le (st : LabState (shakeCore vp)) :
    Pr{let s ← $ᵗ ((shakeCore vp).SkSeed × (shakeCore vp).SkPrf)}[
      st.2 (.inr (rootNode (shakeCore vp))) = some s.1] ≤ (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹ :=
  SampleableType.prEvent_uniformSample_prod_le_of_forall_snd _ fun _ ↦
    (prEvent_mono _ _ _ fun _ h ↦ h.symm).trans
      (SampleableType.prEvent_uniformSample_apply_eq_le (Option.some_injective _) _)

variable (pkSeed) in
open Classical in
/-- **The charge of the root** at public seed `pkSeed`, for the honest input at a linked point. If
the key with the bytes of `PK.seed` is the key of a node with a child, two cells drawn equal, its
first child cell and the root cell, charged `1 / |Y|`; if that node has no child, nothing;
otherwise the first secret seed equal to the root cell, charged `1 / |Y|`. -/
noncomputable def rootCharge (hd : (shakeCore vp).KeyDiscipline vp) :
    DeferredCharge (shakeCore vp) pkSeed :=
  if h : ∃ κ : NodeKey (shakeCore vp),
      κ.1 = adrsKeyOfList vp (Vector.toList (pkSeed : Bytes vp.params.n)) then
    match hch : (slhGraph (shakeCore vp) pkSeed).ch h.choose with
    | [] => .ofSeed (fun _ _ ↦ False) 0 fun _ ↦ by simp
    | c₁ :: _ => .ofCharged _ _ (CanonicalGraph.isCharged_pairHazard (c₁ := c₁)
        (c₂ := .inr (rootNode (shakeCore vp))) _ fun he ↦
        inr_rootNode_not_mem_ch hd pkSeed h.choose (by rw [hch, ← he]; exact List.mem_cons_self))
        CanonicalGraph.not_pairHazard_empty (fun _ ↦ (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹)
        CanonicalGraph.pairPotential_le
  else
    { P := fun _ ↦ False
      Φ := 0
      isCharged := CanonicalGraph.isCharged_false _
      not_empty := id
      U := 0
      le_U := fun _ ↦ le_rfl
      H := fun s st ↦ st.2 (.inr (rootNode (shakeCore vp))) = some s.1
      c := fun _ ↦ (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹
      prEvent_le := prEvent_rootSeed_le }

/-- The root is charged at most `1 / |Y|` in all. -/
theorem rootCharge_U_add_c_le (hd : (shakeCore vp).KeyDiscipline vp)
    (C : (hashSpec (shakeCore vp)).QueryCache) :
    (rootCharge pkSeed hd).U C + (rootCharge pkSeed hd).c C ≤
      (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹ := by
  unfold rootCharge
  split_ifs with h
  · split <;> simp [DeferredCharge.ofSeed, DeferredCharge.ofCharged]
  · simp

/-- **The root charges the honest input at a linked point.** Under the key discipline, an honest
input at a linked point of the transcript rebuilt with the seeds `s`, on the cache that `st` stands
for at them, is a hazard of the charge of the root, when the root cell of `st` holds `PK.root`. -/
theorem rootCharge_of_linkedHonestInput_fill (hd : (shakeCore vp).KeyDiscipline vp)
    (hroot : st.2 (.inr (rootNode (shakeCore vp))) = some o.pk.pkRoot)
    (hpk : o.pk.pkSeed = pkSeed)
    (h : LinkedHonestInput vp (DeriveOutcome.fill (shakeCore vp) s o,
      (secretEncoding (shakeCore vp) (Equiv.refl _) pkSeed).merge s
        ((slhGraph (shakeCore vp) pkSeed).toSplitCache st))) :
    (rootCharge pkSeed hd).P st ∨ (rootCharge pkSeed hd).H s st := by
  unfold LinkedHonestInput HonestInputIn at h
  rw [DeriveOutcome.fill_pk, DeriveOutcome.fill_sk_skSeed, hpk] at h
  unfold rootCharge
  rcases h with ⟨(⟨s', k, _ | ⟨r, rest⟩⟩ | _), hL, hhon⟩ | ⟨a, b, -, hab, hL⟩
  · exact hL.elim
  · obtain ⟨rfl, hks, hr⟩ := hL
    rw [hpk] at hks hhon
    obtain ⟨κ, vs, hκ, hpt⟩ := exists_childVals_eq_some_of_honestEntry hd hhon
    simp only [slhGraph_pt, Sum.inl.injEq, PublicHashQuery.thash.injEq, true_and] at hpt
    obtain ⟨hk, rfl⟩ := hpt
    split_ifs with hN
    · obtain rfl : κ = hN.choose :=
        Subtype.ext (hk.trans ((eq_adrsKeyOfList hks).trans hN.choose_spec.symm))
      rw [CanonicalGraph.childVals_eq_some_iff] at hκ
      obtain ⟨c₁, cs, h1, -, hch⟩ := List.forall₂_cons_right_iff.1 hκ
      split
      · next hch' => exact (List.cons_ne_nil _ _ (hch.symm.trans hch')).elim
      · next hch' =>
        obtain ⟨rfl, -⟩ := List.cons_eq_cons.1 (hch'.symm.trans hch)
        exact .inl ⟨r, h1, hroot.trans (by rw [hr])⟩
    · exact (hN ⟨κ, hk.trans (eq_adrsKeyOfList hks)⟩).elim
  · exact hL.elim
  · obtain ⟨-, hks, hr⟩ := hL
    split_ifs with hN
    · exact (hd.keySeparated b (nodeAdrs (shakeCore vp) hN.choose)
        (isSecretKey_of_inl_mem_childAdrs hab) (type_le_four_of_mem_constructionAddresses
          (nodeAdrs_mem_constructionAddresses _ _))
        (by rw [adrsToKey_nodeAdrs, hN.choose_spec]; exact eq_adrsKeyOfList hks)).elim
    · exact .inr (show st.2 _ = some s.1 by rw [hroot, ← hr]; rfl)

variable (pkSeed) in
/-- **The charge of the virtual hit and the honest input at a linked point** at public seed
`pkSeed`: projected hits at the projected keys of the linked points, charged once per entry,
with the charge of the root. -/
noncomputable def linkedCharge (hd : (shakeCore vp).KeyDiscipline vp)
    (hnm : vp.params.n ≤ vp.params.m) : DeferredCharge (shakeCore vp) pkSeed :=
  (DeferredCharge.ofCharged _ _ (linkedProjKeys hnm pkSeed).isCharged
    CanonicalGraph.ProjKeys.not_projHazard_empty
    (fun C ↦ (((linkedProjKeys hnm pkSeed).keyEntries C).encard : ℝ≥0∞) /
      Nat.card (shakeCore vp).Y) CanonicalGraph.ProjKeys.potential_le).add
    (rootCharge pkSeed hd)

variable {optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y}

/-- **The virtual hit and the honest input at a linked point are charged** to `linkedCharge`, for
every adversary. -/
theorem charges_linkedCharge (hd : (shakeCore vp).KeyDiscipline vp)
    (hnm : vp.params.n ≤ vp.params.m)
    (A : UnforgeableAdversary (romScheme (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed))) :
    (linkedCharge pkSeed hd hnm).Charges A fun z ↦ VirtualHit vp z ∨ LinkedHonestInput vp z := by
  intro w hw h _
  obtain ⟨hz, hst, -⟩ := (CanonicalGraph.mem_support_deferredFillDraw_iff _).1 hw
  have hpk := (hiddenUndrawn_of_mem_support_deferredImpl_labExperiment pkSeed hd A hz).1
  have hroot := (RelabelState.le_of_mem_support_endFill hst).2
    (cell_rootNode_of_mem_support_deferredImpl_labExperiment A hz)
  refine .inr (.inr ?_)
  rcases h with h | h
  · exact .inl (.inl (projHazard_of_virtualHit_fill hd hnm hpk h))
  · exact (rootCharge_of_linkedHonestInput_fill hd hroot hpk h).imp .inr .inr

/-! ## The budget -/

/-- On every deferred run of the lab experiment, for an adversary with hash budget `qh` and
signing budget `qs`, the public entries at node keys, the cached derivable public points and the
cached `H_msg` points number at most `qh + qs + V`. -/
private theorem encard_le_of_mem_support {A : UnforgeableAdversary
      (romScheme (shakeCore vp) (Equiv.refl _) optRand (pure pkSeed))} {qh qs : ℕ}
    (hsep : (shakeCore vp).KeySeparated) (hA : A.RomQueryBound qh qs)
    {z : DeriveOutcome (shakeCore vp) × LabState (shakeCore vp) ×
      List (DeriveQuery (shakeCore vp) ⊕ NodeKey (shakeCore vp))}
    (hz : z ∈ support ((simulateQ (slhGraph (shakeCore vp) pkSeed).deferredImpl
      (labExperiment (shakeCore vp) A pkSeed)).run ((∅, ∅), []))) :
    ((slhNodeKeys (shakeCore vp) pkSeed).keyEntries z.2.1.1).encard +
        {t | (z.2.1.1 t).isSome ∧
          IsDerivablePublicQuery (shakeCore vp) pkSeed (.inl (.inr t))}.encard +
        {t | (z.2.1.1 t).isSome ∧ IsHmsgPoint (core := shakeCore vp) t}.encard ≤
      qh + GeneralScheme.verifyInternalQueryBound vp.params + qs := by
  have hABH : Disjoint ((slhNodeKeys (shakeCore vp) pkSeed).keyEntries z.2.1.1 ∪
      {t | (z.2.1.1 t).isSome ∧ IsDerivablePublicQuery (shakeCore vp) pkSeed (.inl (.inr t))})
      {t | (z.2.1.1 t).isSome ∧ IsHmsgPoint (core := shakeCore vp) t} := by
    refine Set.disjoint_left.2 fun t ht ⟨_, hh⟩ ↦ ?_
    rcases t with (_ | ⟨R, s, r, m⟩) | _
    · exact hh.elim
    · rcases ht with ⟨_, hk⟩ | ⟨_, hd⟩
      · rw [slhNodeKeys_node_eq_none_of_forall_ne_thash _ (by simp)] at hk; cases hk
      · exact hd
    · exact hh.elim
  rw [← Set.encard_union_eq (disjoint_keyEntries_setOf_isDerivablePublicQuery hsep pkSeed _),
    ← Set.encard_union_eq hABH]
  refine (Set.encard_le_encard (t := {t | (z.2.1.1 t).isSome})
    (by rintro t ((⟨hC, _⟩ | ⟨hC, _⟩) | ⟨hC, _⟩) <;> exact hC)).trans ?_
  simpa [add_right_comm] using (slhGraph (shakeCore vp) pkSeed)
    |>.encard_inter_setOf_isSome_le_add_of_mem_support_simulateQ_deferredImpl (D := Set.univ)
    (p := IsPublicLabQuery (shakeCore vp)) (fun _ _ ↦ trivial)
    (isQueryBoundP_labExperiment_public pkSeed hA) hz

/-- The arithmetic of the two budgets: for `L ≤ h`, `a + b ≤ q` and `a + b + h ≤ q + qs`, twice
`a` plus `L` and `b` is at most `q + (q + qs)`, and with `h` at most `2 (q + qs)`. -/
private theorem budget_arith {a b h L q qs : ℕ∞} (hL : L ≤ h) (h1 : a + b ≤ q)
    (h2 : a + b + h ≤ q + qs) :
    2 * a + L + b ≤ q + (q + qs) ∧ 2 * a + L + b + h ≤ 2 * (q + qs) := by
  constructor
  · calc _ ≤ 2 * a + h + b + b := (by gcongr : _ ≤ 2 * a + h + b).trans le_self_add
      _ = (a + b) + (a + b + h) := by ring
      _ ≤ _ := add_le_add h1 h2
  · calc _ ≤ 2 * a + h + b + h + b := (by gcongr : _ ≤ 2 * a + h + b + h).trans le_self_add
      _ = 2 * (a + b + h) := by ring
      _ ≤ _ := by gcongr

/-- The joint budget with the linked charge, the root charged `1 / |Y|`: twice the public entries
at node keys, the projected entries, the cached derivable public points and one, over `|Y|`, plus
the further charge `c₀`. -/
private theorem budget_linkedCharge_le (hd : (shakeCore vp).KeyDiscipline vp)
    (hnm : vp.params.n ≤ vp.params.m) (c₀ : (hashSpec (shakeCore vp)).QueryCache → ℝ≥0∞)
    (C : (hashSpec (shakeCore vp)).QueryCache) :
    2 * (((slhNodeKeys (shakeCore vp) pkSeed).keyEntries C).encard : ℝ≥0∞) /
          Nat.card (shakeCore vp).Y + (linkedCharge pkSeed hd hnm).U C +
        (seedCharge (shakeCore vp) pkSeed C + (c₀ C + (linkedCharge pkSeed hd hnm).c C)) ≤
      (2 * (((slhNodeKeys (shakeCore vp) pkSeed).keyEntries C).encard : ℝ≥0∞) +
          ((linkedProjKeys hnm pkSeed).keyEntries C).encard +
          {t | (C t).isSome ∧ IsDerivablePublicQuery (shakeCore vp) pkSeed (.inl (.inr t))}.encard +
          1) / Nat.card (shakeCore vp).Y + c₀ C := by
  have hc := rootCharge_U_add_c_le (pkSeed := pkSeed) hd C
  simp only [linkedCharge, DeferredCharge.add, DeferredCharge.ofCharged, Pi.add_apply, zero_add,
    seedCharge, ENNReal.div_eq_inv_mul]
  calc _ = (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹ *
          (2 * (((slhNodeKeys (shakeCore vp) pkSeed).keyEntries C).encard : ℝ≥0∞) +
            ((linkedProjKeys hnm pkSeed).keyEntries C).encard +
            {t | (C t).isSome ∧
              IsDerivablePublicQuery (shakeCore vp) pkSeed (.inl (.inr t))}.encard) + c₀ C +
        ((rootCharge pkSeed hd).U C + (rootCharge pkSeed hd).c C) := by ring
    _ ≤ _ + (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹ := by gcongr
    _ = _ := by ring

/-! ## The advantage -/

/-- **SLH-DSA over one SHAKE256 oracle at `n = 32`, at every public seed.** At `n = 32` and `n ≤ m`,
under the canonical address bounds, for every public seed `pkSeed`, every `opt_rand` distribution
and an adversary with hash budget `qh` and signing budget `qs`, the strong advantage of the
adversary against `shakeRomScheme` at `pkSeed` is at most
`securityBound vp.params |Y| 2 1 (qh + V) qs + (qs + 1) / |Y| + (qs + 1) / |Y|`, with `V` the
verifier's query bound. -/
theorem shakeStrongAdvantage_pure_le_securityBound_add_of_n_eq_32
    (hb : CanonicalAddressBounds vp.params) (h32 : vp.params.n = 32)
    (hnm : vp.params.n ≤ vp.params.m)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) :
    shakeStrongAdvantage vp adv ≤
      securityBound vp.params (Nat.card (shakeCore vp).Y) 2 1
          (qh + GeneralScheme.verifyInternalQueryBound vp.params) qs +
        ((qs : ℝ≥0∞) + 1) / Nat.card (shakeCore vp).Y +
        ((qs : ℝ≥0∞) + 1) / Nat.card (shakeCore vp).Y := by
  refine shakeStrongAdvantage_pure_le_securityBound_add hb h32 hnm adv hadv
    (linkedCharge pkSeed (keyDiscipline_shakePrimitives vp hb) hnm) _
    (div_natCard_ne_top (by simp)) (charges_linkedCharge _ hnm _) fun z hz ↦ ?_
  have hA := romQueryBound_verifyingAdv h32.le hnm hadv
  have hR := ENat.toENNReal_le.2 (budget_arith
    (encard_keyEntries_linkedProjKeys_le hnm pkSeed z.2.1.1)
    (encard_keyEntries_add_encard_setOf_isDerivablePublicQuery_le (keySeparated_shakePrimitives _)
      hA hz) (encard_le_of_mem_support (keySeparated_shakePrimitives _) hA hz)).2
  push_cast at hR
  refine (budget_linkedCharge_le (pkSeed := pkSeed) _ hnm
    (fun C ↦ hmsgCharge (shakeCore vp) C + (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹) z.2.1.1).trans ?_
  simp only [hmsgCharge, inv_eq_one_div, ENNReal.div_add_div_same]
  gcongr ?_ / _
  calc _ = _ + 2 := by ring
    _ ≤ _ + 2 := add_le_add_left hR 2
    _ = _ := by ring

/-- **SLH-DSA over one SHAKE256 oracle at `n = 32`, at every public seed, hedged form.** As
`shakeStrongAdvantage_pure_le_securityBound_add_of_n_eq_32`, with `optRand pk` equal to `PK.seed`
with probability at most `ε` at every public key: the strong advantage is at most
`securityBound vp.params |Y| 2 1 (qh + V) qs + 1 / |Y| + qs · ε · (qh + V + qs + 1) / |Y|`
`+ (qs + 1) / |Y|`. -/
theorem shakeStrongAdvantage_pure_le_securityBound_add_of_n_eq_32_hedged
    (hb : CanonicalAddressBounds vp.params) (h32 : vp.params.n = 32)
    (hnm : vp.params.n ≤ vp.params.m)
    (adv : StrongUnforgeableAdversary (shakeRomScheme vp optRand (pure pkSeed))) {qh qs : ℕ}
    (hadv : adv.RomQueryBound qh qs) {ε : ℝ≥0∞}
    (hε : ∀ pk, Pr{let r ← optRand pk}[r = pkSeed] ≤ ε) :
    shakeStrongAdvantage vp adv ≤
      securityBound vp.params (Nat.card (shakeCore vp).Y) 2 1
          (qh + GeneralScheme.verifyInternalQueryBound vp.params) qs +
        1 / Nat.card (shakeCore vp).Y +
        qs * ε * (((qh + GeneralScheme.verifyInternalQueryBound vp.params : ℕ) : ℝ≥0∞) + qs +
          1) / Nat.card (shakeCore vp).Y + ((qs : ℝ≥0∞) + 1) / Nat.card (shakeCore vp).Y := by
  refine shakeStrongAdvantage_pure_le_securityBound_add_hedged hb h32 hnm adv hadv hε
    (linkedCharge pkSeed (keyDiscipline_shakePrimitives vp hb) hnm) _
    (div_natCard_ne_top (by simp)) (charges_linkedCharge _ hnm _) fun z hz ↦ ?_
  have hA := romQueryBound_verifyingAdv h32.le hnm hadv
  have hR := ENat.toENNReal_le.2 (budget_arith
    (encard_keyEntries_linkedProjKeys_le hnm pkSeed z.2.1.1)
    (encard_keyEntries_add_encard_setOf_isDerivablePublicQuery_le (keySeparated_shakePrimitives _)
      hA hz) (encard_le_of_mem_support (keySeparated_shakePrimitives _) hA hz)).1
  push_cast at hR
  refine (budget_linkedCharge_le (pkSeed := pkSeed) _ hnm
    (fun _ ↦ (Nat.card (shakeCore vp).Y : ℝ≥0∞)⁻¹) z.2.1.1).trans ?_
  simp only [inv_eq_one_div, ENNReal.div_add_div_same]
  gcongr ?_ / _
  calc _ = _ + 2 := by ring
    _ ≤ _ + 2 := add_le_add_left hR 2
    _ = _ := by ring


end Shake

end SLHDSA.Security
