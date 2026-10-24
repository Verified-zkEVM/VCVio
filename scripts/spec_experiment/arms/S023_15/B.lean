-- imports: VCVio.ProgramLogic.Library
lemma log_length_le_of_mem_support_counting_simulate_run_logging [Fintype M] [Fintype S]
    {α : Type} (oa : OracleComp (CMOracle M S C) α)
    {z : (α × QueryLog (CMOracle M S C)) × QueryCount (M × S)}
    (hz : z ∈ support (countingOracle.simulate ((simulateQ loggingOracle oa).run) 0)) :
    z.1.2.length ≤ ∑ ms : M × S, z.2 ms := by
  simp only [countingOracle.simulate, AddWriterT.runAdd, simulateQ_nf] at hz
  induction oa using OracleComp.inductionOn generalizing z with
  | pure x => simp_all [simulateQ_nf]; subst hz; simp
  | query_bind t mx ih =>
      simp only [simulateQ_nf, loggingOracle.run_apply, countingOracle.run_apply] at hz
      obtain ⟨_, ⟨u, -, ⟨⟨a, l⟩, w⟩, hw, rfl⟩, rfl⟩ := hz
      have := ih u ⟨_, hw, rfl⟩
      simp [Finset.sum_add_distrib, QueryCount.single] at this ⊢; omega
