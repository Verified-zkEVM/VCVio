-- imports: VCVio.ProgramLogic.Library
lemma log_length_le_of_mem_support_counting_simulate_run_logging [Fintype M] [Fintype S]
    {α : Type} (oa : OracleComp (CMOracle M S C) α)
    {z : (α × QueryLog (CMOracle M S C)) × QueryCount (M × S)}
    (hz : z ∈ support (countingOracle.simulate ((simulateQ loggingOracle oa).run) 0)) :
    z.1.2.length ≤ ∑ ms : M × S, z.2 ms := by
  induction oa using OracleComp.inductionOn generalizing z with
  | pure x => simp_all [countingOracle.simulate, AddWriterT.runAdd]
  | query_bind t mx ih =>
    simp only [countingOracle.simulate, AddWriterT.runAdd, simulateQ_nf] at hz ih
    obtain ⟨u, -, w, hw, rfl⟩ := hz
    simpa [Finset.sum_add_distrib, QueryCount.single, Nat.lt_one_add_iff] using ih u ⟨w, hw, rfl⟩
