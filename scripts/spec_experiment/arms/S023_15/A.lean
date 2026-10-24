lemma log_length_le_of_mem_support_counting_simulate_run_logging [Fintype M] [Fintype S]
    {α : Type} (oa : OracleComp (CMOracle M S C) α)
    {z : (α × QueryLog (CMOracle M S C)) × QueryCount (M × S)}
    (hz : z ∈ support (countingOracle.simulate ((simulateQ loggingOracle oa).run) 0)) :
    z.1.2.length ≤ ∑ ms : M × S, z.2 ms := by
  induction oa using OracleComp.inductionOn generalizing z with
  | pure x => simp_all [countingOracle.simulate]
  | query_bind t mx ih =>
      obtain ⟨⟨x, log⟩, qc⟩ := z
      rw [OracleComp.run_simulateQ_loggingOracle_query_bind,
        countingOracle.mem_support_simulate_queryBind_iff] at hz
      obtain ⟨hz0, u, hz⟩ := hz
      simp [countingOracle.simulate, simulateQ_map] at hz
      obtain ⟨b, hb, rfl⟩ := hz
      have h := ih u (z := ((x, b), _)) (by simpa [countingOracle.simulate] using hb)
      rw [sum_update_pred (Nat.pos_of_ne_zero hz0)] at h
      exact h.trans_lt (Nat.sub_one_lt (Finset.sum_pos' (fun _ _ => Nat.zero_le _)
        ⟨t, Finset.mem_univ _, Nat.pos_of_ne_zero hz0⟩).ne')
