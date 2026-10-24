lemma dcAux_reader_step [Fintype Nonce] [Fintype Digest] (out : Bool)
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
    (transcript : TagTranscript Nonce Digest)
    (k : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inr transcript) →
      OracleComp (UnlinkOracleSpec TagId Nonce Digest) Bool)
    (ih : ∀ (u : (UnlinkOracleSpec TagId Nonce Digest).Range (Sum.inr transcript))
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
    (hqR : OracleComp.IsQueryBoundP (liftM (OracleSpec.query (Sum.inr transcript)) >>= k)
      (·.isRight) qR)
    (hqT : OracleComp.IsQueryBoundP (liftM (OracleSpec.query (Sum.inr transcript)) >>= k)
      (·.isLeft) qT) :
    Pr{let b ← (do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) => z.1) <$>
          (simulateQ (multipleBadTableHandlerFine
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)) gFine)
            (liftM (OracleSpec.query (Sum.inr transcript)) >>= k)).run (s, sB))}[b = out] ≤
      Pr{let b ← (do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (simulateQ (singleTableHandler (OracleComp.tableExtending c gS))
          (liftM (OracleSpec.query (Sum.inr transcript)) >>= k)).run' s)}[b = out] +
      Pr{let z ← (do
        let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
            (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandlerFine
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
              (OracleComp.tableExtending c gS)) gFine)
            (liftM (OracleSpec.query (Sum.inr transcript)) >>= k)).run (s, sB))}[z.2.bad] +
      ((qR * Fintype.card TagId : ℕ) : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) +
      ((qRInit * qT : ℕ) : ℝ≥0∞) / (Fintype.card Nonce : ℝ≥0∞) +
      ((qR * Fintype.card TagId * sessionsPerTag : ℕ) : ℝ≥0∞) /
        (Fintype.card Digest : ℝ≥0∞) := by
  classical
  -- Reader case: the asymmetric-discard argument. Slot-0 column lazification
  -- on both sides makes M's reader bit a constant `m` of the extended cache `c₀′`; on `m = true`
  -- the IH closes directly, on `m = false` the slot-positive acceptance event `E gS` is the
  -- whole gap and is charged to one slack₃ unit via `cacheBadReader`.
  -- **Budget splits.** The head reader query is right-not-left, so `qR = qR' + 1` and `qT`
  -- is unchanged. `R` grows to `insert transcript.nonce R`.
  rw [OracleComp.isQueryBoundP_query_bind_iff] at hqR hqT
  obtain ⟨qR', rfl⟩ : ∃ qR', qR = qR' + 1 := ⟨qR - 1, by have := hqR.1; simp at this; omega⟩
  have hqTk : ∀ u, (k u).IsQueryBoundP (·.isLeft) qT := fun u => by simpa using hqT.2 u
  have hqRk : ∀ u, (k u).IsQueryBoundP (·.isRight) qR' := fun u => by simpa using hqR.2 u
  -- M-Fine reader head step: pure reply, state untouched, `cacheBad` advances by `gFine`.
  have hMstep : ∀ gS gFine {β : Type} (f : _ → ProbComp β),
      multipleBadTableHandlerFine (slotZeroSubTable (sessionsPerTag := sessionsPerTag)
          (OracleComp.tableExtending c gS)) gFine (Sum.inr transcript) (s, sB) >>= f
      = f (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
          (fun tag nonce => slotZeroSubTable (sessionsPerTag := sessionsPerTag)
            (OracleComp.tableExtending c gS) (tag, nonce))
          (multiplePattern (TagId := TagId) sessionsPerTag) transcript), s,
          multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB) := by
    intro gS gFine β f
    simp only [multipleBadTableHandlerFine, multipleTableHandler_reader_run_slotZeroSubTable]; rfl
  -- S reader head step: pure reply, state untouched.
  have hSstep : ∀ gS {β : Type} (f : _ → ProbComp β),
      singleTableHandler (OracleComp.tableExtending c gS) (Sum.inr transcript) s >>= f
      = f (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
          (fun slot nonce => OracleComp.tableExtending c gS (slot, nonce))
          (singlePattern (TagId := TagId) sessionsPerTag) transcript), s) := fun gS β f => by
    rw [singleTableHandler_reader_run (OracleComp.tableExtending c gS) transcript s]; rfl
  -- Collapse the head reader query on all three positions.
  simp only [multipleBadTableFine_run_query_bind', singleTable_run'_query_bind', hMstep, hSstep]
  classical
  -- **C1: slot-0 column lazification.** Cache every slot-0 cell of the queried column.
  set cells : List ((TagId × Fin sessionsPerTag) × Nonce) :=
    (Finset.univ.toList).map
      (fun T : TagId => ((T, (0 : Fin sessionsPerTag)), transcript.nonce)) with hcells
  -- The three terms (LHS-output, RHS-output, BAD) all have the shape
  -- `$ᵗ gS >>= fun gS => Mψ (tableExtending c gS)` for the continuations below; the
  -- lazification lemma rewrites `tableExtending c gS` to `idealCacheMapM cells c >>= …`.
  -- LHS continuation: absorbs the inner `$ᵗ gFine` binder.
  have hM_lazify := fun {α : Type} [MeasurableSpace α]
      (observe : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) → α) =>
    let : MeasurableSpace Digest := ⊤
    (evalDist_idealCacheMapM_bind_uniformTable_comp
      SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample cells c
      (fun T => do
        let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
        observe <$>
          (simulateQ (multipleBadTableHandlerFine
            (slotZeroSubTable (sessionsPerTag := sessionsPerTag) T) gFine)
            (k (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId)
              (fun tag nonce => slotZeroSubTable (sessionsPerTag := sessionsPerTag)
                T (tag, nonce))
              (multiplePattern (TagId := TagId) sessionsPerTag) transcript)))).run
            (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag)
              gFine transcript sB))).symm
  have hLHS_lazify := hM_lazify (α := Bool) (fun z => z.1)
  -- RHS continuation (no `gFine`).
  have hRHS_lazify :=
    let : MeasurableSpace Digest := ⊤
    (evalDist_idealCacheMapM_bind_uniformTable_comp
      SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample cells c
      (fun T => (simulateQ (singleTableHandler T)
        (k (ReaderReply.ofBool (unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
          (fun slot nonce => T (slot, nonce))
          (singlePattern (TagId := TagId) sessionsPerTag) transcript)))).run' s)).symm
  -- BAD continuation: same as LHS but with the `(z.1, z.2.2)` projection.
  let : MeasurableSpace (Bool × UnlinkBadState TagId Nonce Digest) := ⊤
  have hBAD_lazify := hM_lazify (fun z => (z.1, z.2.2))
  -- Rewrite all three terms to their lazified forms.
  rw [(EvalDistEq.of_evalDist_eq hLHS_lazify).prEvent_eq,
    (EvalDistEq.of_evalDist_eq hRHS_lazify).prEvent_eq,
    (EvalDistEq.of_evalDist_eq hBAD_lazify).prEvent_eq]
  -- **Per-rs coupling.** All three terms now share the `idealCacheMapM cells c` head; couple
  -- them via the empty-`D` disagreement bound (mirroring the tag cases' `$ᵗ Nonce` coupling).
  -- The slacks are charged entirely in the per-rs obligation (closed in C2/C3); here `ε₁ = 0`,
  -- `ε₂ = slack₁ + slack₂ + slack₃`.
  -- Regroup the RHS so the three slacks become a single trailing `ε₂` and insert `ε₁ = 0`.
  rw [show ∀ a b c d e : ℝ≥0∞, a + b + c + d + e = a + b + 0 + (c + d + e) from
        fun a b c d e => by ring]
  refine prEvent_bind_le_add_bad_disagree (mx := idealCacheMapM (Digest := Digest) cells c)
    (D := fun _ => False) (by simp) ?_
  intro rs hrs _
  -- **C2: per-rs facts.** Set `c₀′ := rs.2`, the cache with the slot-0 column cached.
  set c₀ := rs.2 with hc₀
  -- (a) hcInv for `c₀`: slot-positive cells are never in `cells`, so unchanged from `c`.
  have hc₀Inv : ∀ tag : TagId, ∀ sid : Fin sessionsPerTag, sid ≠ 0 →
      ∀ n : Nonce, c₀ ((tag, sid), n) = none := fun tag sid hsid n =>
    (idealCacheMapM_cache_not_mem cells c rs hrs _ (by simp [hcells, Ne.symm hsid])).trans
      (hcInv tag sid hsid n)
  -- (c) The slot-0 cell read is independent of `gS` (it is the cached value).
  have hcellConst : ∀ tag : TagId, ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
      OracleComp.tableExtending c₀ gS ((tag, (0 : Fin sessionsPerTag)), transcript.nonce) =
        (c₀ ((tag, (0 : Fin sessionsPerTag)), transcript.nonce)).getD
          (transcript.auth) := fun tag gS => by
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (idealCacheMapM_cache_isSome_of_mem cells c rs
      hrs ((tag, 0), transcript.nonce) (by simp [hcells]))
    simp [OracleComp.tableExtending, c₀, hu]
  -- (d) The M reader bit is therefore a constant `m` independent of `gS`.
  set m : Bool := unlinkReaderAccepts (Slot := TagId)
    (fun tag _nonce => (c₀ ((tag, (0 : Fin sessionsPerTag)), transcript.nonce)).getD
      (transcript.auth))
    (multiplePattern (TagId := TagId) sessionsPerTag) transcript with hm
  have hmConst : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
      unlinkReaderAccepts (Slot := TagId)
        (fun tag nonce => slotZeroSubTable (sessionsPerTag := sessionsPerTag)
          (OracleComp.tableExtending c₀ gS) (tag, nonce))
        (multiplePattern (TagId := TagId) sessionsPerTag) transcript = m := fun gS => by
    simp [hm, unlinkReaderAccepts, tagAccepts, multiplePattern, hcellConst]
  -- (e) Per-rs bookkeeping: `R′ := insert transcript.nonce R`.
  set R' : Finset Nonce := insert transcript.nonce R with hR'
  have hqRle' : qR' + R'.card ≤ qRInit := by
    have : R'.card ≤ R.card + 1 := Finset.card_insert_le _ _
    omega
  -- (f) hRespInv-v2 for `c₀` at `R'`: off `R'` we have `n' ≠ transcript.nonce`, so the cell is
  -- not in `cells`, hence `c₀` agrees with `c` there and `sB` is unchanged by the reader step.
  have hRespInv' : ∀ tag' : TagId, ∀ n' : Nonce, n' ∉ R' →
      c₀ ((tag', (0 : Fin sessionsPerTag)), n') ≠ none →
      sB.responses (tag', n') ≠ none := by
    intro tag' n' hn' hne
    rw [hR', Finset.mem_insert, not_or] at hn'
    exact hRespInv tag' n' hn'.2 fun h0 => hne ((idealCacheMapM_cache_not_mem cells c rs hrs _
      (by simp [hcells, Ne.symm hn'.1])).trans h0)
  -- Discard the `multipleBadReaderAdvance` perturbation of the initial state for any event that
  -- ignores `cacheBad`.
  have hirr : ∀ (r) {β : Type}
      (f : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) → β) (E : β → Prop),
      (∀ z cb, E (f (z.1, z.2.1, {z.2.2 with cacheBad := cb})) ↔ E (f z)) →
      Pr{let b ← (do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          f <$> (simulateQ (multipleBadTableHandlerFine (slotZeroSubTable
            (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c₀ gS)) gFine) (k r)).run
            (s, multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB) :
          ProbComp β)}[E b] =
      Pr{let b ← (do
          let gS ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          let gFine ← $ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)
          f <$> (simulateQ (multipleBadTableHandlerFine (slotZeroSubTable
            (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c₀ gS)) gFine) (k r)).run
            (s, sB) : ProbComp β)}[E b] := by
    intro r β f E hE
    refine prEvent_bind_congr _ _ _ _ _ fun gS => prEvent_bind_congr _ _ _ _ _ fun gFine => ?_
    have h := congrArg (fun X => Pr{let z ← X}[E (f z)])
      (simulateQ_multipleBadTableHandlerFine_cacheBad_irrelevant (slotZeroSubTable
        (sessionsPerTag := sessionsPerTag) (OracleComp.tableExtending c₀ gS)) gFine (k r) s
        (multipleBadReaderAdvance (sessionsPerTag := sessionsPerTag) gFine transcript sB) sB
        sB.cacheBad rfl rfl rfl)
    simpa only [prEvent_map, hE] using h
  -- Rewrite the M reader bit (in LHS and BAD) to the constant `m`.
  simp only [hmConst]
  erw [hirr _ (fun z => z.1) (· = out) fun _ _ => Iff.rfl,
    hirr _ (fun z => (z.1, z.2.2)) (·.2.bad = true) fun _ _ => Iff.rfl]
  refine (ih (ReaderReply.ofBool m) qR' qT s c₀ sB R'
    (hqRk _) (hqTk _) hqRle' hc₀Inv hRespInv').trans ?_
  -- **m-split.**
  rcases Bool.eq_false_or_eq_true m with hmb | hmb
  · -- **Case m = true.** The S reader also accepts (slot-0 witness lifts), so for every `gS` the
    -- S bit is `true`; both sides run `k (ReaderReply.ofBool true)` at the same state, and the
    -- IH at `(c₀, qR', R')` closes it.
    have hsTrue : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
        unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
          (fun slot nonce => OracleComp.tableExtending c₀ gS (slot, nonce))
          (singlePattern (TagId := TagId) sessionsPerTag) transcript = true := fun gS =>
      mReader_accepts_imp_sReader_accepts _ transcript ((hmConst gS).trans hmb)
    -- Rewrite the M bit (LHS/BAD) and the S bit (RHS) to `true`.
    rw [hmb]
    simp only [hsTrue]
    rw [show ∀ a b c d : ℝ≥0∞, a + (b + c + d) = a + b + c + d from
          fun a b c d => by ring]
    gcongr <;> exact Nat.le_succ _
  · -- **Case m = false.** M rejects (slot-0 miss). The S reader bit is exactly the
    -- slot-positive collision indicator `cacheBadReader gS transcript` (the slot-0 disjunct is
    -- ruled out by `m = false`, and slot-positive cells are uncached in `c₀` so they read raw
    -- `gS`). Its uniform-sample mass is bounded by `|TagId|·sp/|Digest|` via
    -- `prEvent_cacheBadReader_uniformSample_le`, charged to the slack₃ unit.
    -- Reading an uncached slot-positive cell of `tableExtending c₀ gS` returns the raw `gS`.
    have htE : ∀ (gS : (TagId × Fin sessionsPerTag) × Nonce → Digest)
        (tag : TagId) (sid : Fin sessionsPerTag), sid ≠ 0 →
        OracleComp.tableExtending c₀ gS ((tag, sid), transcript.nonce) =
          gS ((tag, sid), transcript.nonce) := fun gS tag sid hsid => by
      simp [OracleComp.tableExtending, hc₀Inv tag sid hsid]
    -- (g) Under `m = false`, the S reader bit equals the slot-positive collision flag.
    have hsAccE : ∀ gS : (TagId × Fin sessionsPerTag) × Nonce → Digest,
        unlinkReaderAccepts (Slot := TagId × Fin sessionsPerTag)
          (fun slot nonce => OracleComp.tableExtending c₀ gS (slot, nonce))
          (singlePattern (TagId := TagId) sessionsPerTag) transcript
        = cacheBadReader (sessionsPerTag := sessionsPerTag) gS transcript := fun gS => by
      simp [hm, unlinkReaderAccepts, tagAccepts, multiplePattern] at hmb
      rw [Bool.eq_iff_iff, cacheBadReader_eq_true_iff]
      unfold unlinkReaderAccepts tagAccepts singlePattern
      simp only [decide_eq_true_eq]
      refine ⟨fun ⟨tag, sid, h⟩ => ?_, fun ⟨t, i, hi, h⟩ => ⟨t, i, htE gS t i hi ▸ h⟩⟩
      rcases eq_or_ne sid 0 with rfl | hsid
      · exact absurd (hcellConst tag gS ▸ h) (hmb tag)
      · exact ⟨tag, sid, hsid, htE gS tag sid hsid ▸ h⟩
    -- Rewrite the M bit to `false` (LHS/BAD) and the actual S bit to `cacheBadReader` (RHS).
    rw [hmb]
    simp only [hsAccE]
    rw [show ((qR' + 1) * Fintype.card TagId * sessionsPerTag : ℕ) =
        qR' * Fintype.card TagId * sessionsPerTag + Fintype.card TagId * sessionsPerTag by ring,
      Nat.cast_add, ENNReal.add_div, show ∀ a b c d e f : ℝ≥0∞, a + b + (c + d + (e + f)) =
        a + f + b + c + d + e from fun _ _ _ _ _ _ => by ring]
    gcongr
    · -- **Asymmetric discard.** Replace the S reader bit `false` by its actual value
      -- `cacheBadReader gS`, charging the uniform mass `≤ |TagId| * sessionsPerTag / |Digest|`
      -- of the event where they differ.
      let : MeasurableSpace ((TagId × Fin sessionsPerTag) × Nonce → Digest) := ⊤
      rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton]
      refine (evalDist_bind_apply_le_of_discard _ _ _ measurable_from_top measurable_from_top
        (bad := {gS | cacheBadReader (sessionsPerTag := sessionsPerTag) gS transcript = true})
        MeasurableSet.of_discrete (Filter.Eventually.of_forall fun gS hg => ?_)
        (measurableSet_singleton out)).trans (add_le_add le_rfl ?_)
      · rw [show cacheBadReader (sessionsPerTag := sessionsPerTag) gS transcript = false by
          simpa using hg]
      · rw [← prEvent_eq_evalDist_of_discrete]
        exact prEvent_cacheBadReader_uniformSample_le transcript
    · omega
