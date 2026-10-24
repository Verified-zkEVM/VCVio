-- imports: VCVio.ProgramLogic.Library
-- reusable
private lemma prEvent_bind_le_add_add {α : Type} {mx : ProbComp α} {my oc ob : α → ProbComp Prop}
    {ε : ℝ≥0∞} (h : ∀ x ∈ support mx, prEvent (my x) ≤ prEvent (oc x) + prEvent (ob x) + ε) :
    prEvent (mx >>= my) ≤ prEvent (mx >>= oc) + prEvent (mx >>= ob) + ε := by
  simpa using prEvent_bind_le_add_bad_disagree (mx := mx) (my := my) (oc := oc) (ob := ob)
    (q := id) (r := id) (D := fun _ => False) (ε₁ := 0) (by simp) fun x hx _ => by
      simpa using h x hx

lemma dcAux_tag_slotZero [Fintype Nonce] [Fintype Digest] (out : Bool)
    (qRInit qR qT : ℕ)
    (s : UnlinkState TagId)
    (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest)
    (R : Finset Nonce)
    (hqRle : qR + R.card ≤ qRInit)
    (hcInv : ∀ tag : TagId, ∀ sid : Fin sessionsPerTag, sid ≠ 0 →
        ∀ n : Nonce, c ((tag, sid), n) = none)
    (hRespInv : ∀ tag : TagId, ∀ n : Nonce, n ∉ R →
        c ((tag, (0 : Fin sessionsPerTag)), n) ≠ none →
        sB.responses (tag, n) ≠ none)
    (tag : TagId)
    (k : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inl tag) →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (ih : ∀ (u : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inl tag))
        (qR qT : ℕ) (s : UnlinkState TagId)
        (c : (((TagId × Fin sessionsPerTag) × Nonce) →ₒ Digest).QueryCache)
        (sB : UnlinkBadState TagId Nonce Digest) (R : Finset Nonce),
        OracleComp.IsQueryBoundP (k u) (·.isRight) qR →
        OracleComp.IsQueryBoundP (k u) (·.isLeft) qT →
        qR + R.card ≤ qRInit →
        (∀ tag : TagId, ∀ sid : Fin sessionsPerTag, sid ≠ 0 →
          ∀ n : Nonce, c ((tag, sid), n) = none) →
        (∀ tag : TagId, ∀ n : Nonce, n ∉ R →
          c ((tag, (0 : Fin sessionsPerTag)), n) ≠ none →
          sB.responses (tag, n) ≠ none) →
        Pr{let b ← (do
            let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
              (simulateQ (multipleBadTableHandlerFine
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) gFine) (k u)).run (s, sB))}[b = out] ≤
          Pr{let b ← (do
            let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (simulateQ (singleTableHandler (OracleComp.tableExtending c gS))
              (k u)).run' s)}[b = out] +
          Pr{let z ← (do
            let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandlerFine
                (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                  (OracleComp.tableExtending c gS)) gFine) (k u)).run (s, sB))}[z.2.bad] +
          ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
          ((qRInit * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
          ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
            (Fintype.card Digest : ℝ≥0∞))
    (hqR : OracleComp.IsQueryBoundP (liftM (OracleSpec.query (Sum.inl tag)) >>= k)
      (·.isRight) qR)
    (hqT : OracleComp.IsQueryBoundP (liftM (OracleSpec.query (Sum.inl tag)) >>= k)
      (·.isLeft) qT)
    (hslot : s.sessionsUsed tag < sessionsPerTag)
    (hzero : s.sessionsUsed tag = 0) :
    Pr{let b ← (do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandlerFine
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)) gFine)
            (liftM (OracleSpec.query (Sum.inl tag)) >>= k)).run (s, sB))}[b = out] ≤
      Pr{let b ← (do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (OracleComp.tableExtending c gS))
          (liftM (OracleSpec.query (Sum.inl tag)) >>= k)).run' s)}[b = out] +
      Pr{let z ← (do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandlerFine
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)) gFine)
            (liftM (OracleSpec.query (Sum.inl tag)) >>= k)).run (s, sB))}[z.2.bad] +
      ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
      ((qRInit * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
      ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  classical
  let : MeasurableSpace Digest := ⊤
  let : MeasurableSpace Nonce := ⊤
  simp only [OracleComp.isQueryBoundP_query_bind_iff] at hqR hqT
  obtain ⟨qT, rfl⟩ : ∃ qT', qT = qT' + 1 := ⟨qT - 1, by simp at hqT; omega⟩
  simp at hqR hqT
  simp only [map_bind] at ih
  have hsid : (⟨s.sessionsUsed tag, hslot⟩ : Fin sessionsPerTag) = 0 := Fin.ext hzero
  simp only [multipleBadTableFine_run_query_bind', singleTable_run'_query_bind', map_bind]
  simp only [multipleBadTableHandlerFine, singleTableHandler_tag_run_of_lt _ tag s hslot, hsid,
    multipleTableHandler_tag_run_eq_singleTableHandler_tag_run_of_sessionsUsed_zero _ tag s hzero,
    unlinkOracleSpec_range_inl, bind_assoc, pure_bind]
  simp only [← evalDist_singleton_true]
  rw [evalDist_bind_bind_bind_rotate ($ᵗ _) ($ᵗ _) ($ᵗ Nonce) _ .of_discrete,
    evalDist_bind_bind_bind_rotate ($ᵗ _) ($ᵗ _) ($ᵗ Nonce) _ .of_discrete,
    evalDist_bind_bind_swap ($ᵗ _) ($ᵗ Nonce) _ .of_discrete]
  simp only [evalDist_singleton_true]
  refine le_trans ?_ (add_le_add_left (add_le_add_right (b := ?m) ?_ _) _)
  · rw [add_assoc, add_assoc]
    refine prEvent_bind_le_add_add fun n _ => ?_
    rcases hc : c ((tag, 0), n) with _ | u₀
    · have hU f := evalDist_bind_bind_update ($ᵗ Digest)
        ($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) SampleableType.evalDist_uniformSample
        SampleableType.evalDist_uniformSample ((tag, 0), n) (α := Prop) f
      simp only [← evalDist_singleton_true]
      rw [← hU, ← hU, ← hU]
      have hcell g u : OracleComp.tableExtending c (Function.update g ((tag, 0), n) u)
          ((tag, 0), n) = u := by simp [OracleComp.tableExtending, hc]
      simp only [evalDist_singleton_true, hcell, ← OracleComp.tableExtending_update_of_none c _ hc,
        ← OracleComp.tableExtending_cacheQuery]
      refine prEvent_bind_le_add_add fun u _ => ?_
      refine (ih (some ⟨n, u⟩) qR qT _ _ _ R (hqR _) (hqT _) hqRle
        (fun t i hi m => by simpa [hi] using hcInv t i hi m) ?_).trans_eq
        (by rw [add_assoc, add_assoc])
      · intro t m hm hne
        by_cases h : t = tag ∧ m = n
        · obtain ⟨rfl, rfl⟩ := h
          simp [multipleBadAdvance]
        · simpa [multipleBadAdvance, h] using hRespInv t m hm (by simpa [h] using hne)
    · have hcell gS : OracleComp.tableExtending c gS ((tag, 0), n) = u₀ := by
        simp [OracleComp.tableExtending, hc]
      simp only [hcell]
      refine (ih (some ⟨n, u₀⟩) qR qT _ c _ R (hqR _) (hqT _) hqRle hcInv ?_).trans_eq
        (by rw [add_assoc, add_assoc])
      intro t m hm hne
      by_cases h : t = tag ∧ m = n
      · obtain ⟨rfl, rfl⟩ := h
        simp [multipleBadAdvance]
      · simpa [multipleBadAdvance, h] using hRespInv t m hm hne
  · gcongr
    omega
