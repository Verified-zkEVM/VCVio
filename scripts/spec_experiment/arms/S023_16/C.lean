-- imports: VCVio.ProgramLogic.Library VCVio.ProgramLogic.Library.Derive VCVio.ProgramLogic.Library.T3.PRFTagReader.Table VCVio.ProgramLogic.Library.T3.PRFTagReader.MultipleToHybridSetup
-- inline: VCVio/ProgramLogic/Library/T3/PRFTagReader/MultipleToHybridEagerSetup.lean
lemma evalDist_simulateQ_multipleBadQueryImpl_run_eq_tableExtending [SampleableType Digest]
    [Fintype Nonce] [Finite Digest]
    [MeasurableSpace Digest] [MeasurableSingletonClass Digest]
    [MeasurableSpace (Bool × UnlinkBadState TagId Nonce Digest)]
    [EvalDistSemantics ProbComp] [LawfulEvalDistSemantics ProbComp]
    (hDigest : 𝒟[$ᵗ Digest] = uniformOn Set.univ)
    (hTable : 𝒟[$ᵗ (TagId × Nonce → Digest)] = uniformOn Set.univ)
    (oa : UnlinkAdversary TagId Nonce Digest)
    (s : UnlinkState TagId) (c : ((TagId × Nonce) →ₒ Digest).QueryCache)
    (sB : UnlinkBadState TagId Nonce Digest) :
    𝒟[(fun z : Bool × MultipleBadState TagId Nonce Digest sessionsPerTag => (z.1, z.2.2)) <$>
        (simulateQ (multipleBadQueryImpl TagId Nonce Digest sessionsPerTag) oa).run ((s, c), sB)] =
      𝒟[do let g ← $ᵗ (TagId × Nonce → Digest);
            (fun z : Bool × (UnlinkState TagId × UnlinkBadState TagId Nonce Digest) =>
                (z.1, z.2.2)) <$>
              (simulateQ (multipleBadTableHandler sessionsPerTag
                (OracleComp.tableExtending c g)) oa).run (s, sB)] := by
  classical
  let : MeasurableSpace Nonce := ⊤
  induction oa using OracleComp.inductionOn generalizing s c sB with
  | pure b =>
    simp [hTable]
  | query_bind t f ih =>
    simp only [multipleBad_run_query_bind', multipleBadTable_run_query_bind', map_bind]
    rcases t with tag | transcript
    · by_cases hslot : s.sessionsUsed tag < sessionsPerTag
      · simp only [multipleBadQueryImpl_tag_run, multipleIdealQueryImpl_tag_run_of_lt tag s c hslot,
          multipleBadTableHandler, multipleTableHandler_tag_run_of_lt _ tag s hslot,
          unlinkOracleSpec_range_inl, bind_assoc, pure_bind]
        rw [evalDist_bind_bind_swap ($ᵗ (TagId × Nonce → Digest)) ($ᵗ Nonce) _ .of_discrete]
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun n _ => ?_
        refine Eq.trans ?_ (evalDist_idealCacheStep_bind_uniformTable_comp hDigest hTable c (tag, n)
          fun g' => (fun z => (z.1, z.2.2)) <$> (simulateQ (multipleBadTableHandler _ g')
            (f (some ⟨n, g' (tag, n)⟩))).run (_, multipleBadAdvance tag sB (some ⟨n, g' (tag, n)⟩)))
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun r hr => ?_
        refine (ih _ _ r.2 _).trans ?_
        simp only [OracleComp.tableExtending, idealCacheStep_cache_self c (tag, n) r hr,
          Option.getD_some]
      · simpa [multipleBadQueryImpl_tag_run, multipleBadTableHandler, hslot,
          multipleIdealQueryImpl_tag_run_of_not_lt, multipleTableHandler_tag_run_of_not_lt] using
          ih none s c _
    · simp only [multipleBadQueryImpl_reader_run, multipleIdealQueryImpl_reader_run,
          multipleBadTableHandler, multipleTableHandler_reader_run, unlinkOracleSpec_range_inr,
          bind_assoc, pure_bind]
      refine Eq.trans ?_ (evalDist_idealCacheMapM_bind_uniformTable_comp hDigest hTable
        (Finset.univ.toList.map (·, transcript.nonce)) c fun g' => (fun z => (z.1, z.2.2)) <$>
          (simulateQ (multipleBadTableHandler sessionsPerTag g') (f (ReaderReply.ofBool
            (unlinkReaderAccepts (fun tag nonce => g' (tag, nonce)) (multiplePattern sessionsPerTag)
              transcript)))).run (s, sB))
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ fun rs hrs => (ih _ s rs.2 sB).trans ?_
      refine congrArg _ (congrArg _ (funext fun g => ?_))
      simp [idealCacheMapM_support _ c rs hrs g, unlinkReaderAccepts, tagAccepts, multiplePattern]
