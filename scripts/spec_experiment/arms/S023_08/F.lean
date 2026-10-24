-- imports: VCVio.ProgramLogic.Library
lemma simulateQ_prfReal_unlinkToMultiplePRFReaderImpl_run [Fintype TagId] [DecidableEq Digest]
    [NeZero sessionsPerTag]
    (prfs : TagReaderPRFs K TagId Nonce Digest sessionsPerTag) (k : K)
    (transcript : TagTranscript Nonce Digest) (s : UnlinkState TagId) :
    simulateQ (PRFScheme.prfRealQueryImpl prfs.multiplePRFScheme k)
        ((unlinkToMultiplePRFReaderImpl
            (TagId := TagId) (Nonce := Nonce) (Digest := Digest) transcript).run s) =
      (unlinkReaderQueryImpl (TagId := TagId) (Slot := TagId) (Nonce := Nonce) (Digest := Digest)
        (fun tag nonce => prfs.evalMultiple k tag nonce)
        (multiplePattern (TagId := TagId) sessionsPerTag) transcript).run s := by
  simp [unlinkToMultiplePRFReaderImpl, unlinkReaderQueryImpl, simulateQ_list_mapM,
    unlinkReaderAccepts, tagAccepts, multiplePattern, TagReaderPRFs.multiplePRFScheme]
