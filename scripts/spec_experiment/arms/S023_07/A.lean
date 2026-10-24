-- imports: VCVio.OracleComp.QueryTracking.QueryBound.Simulation
lemma isQueryBoundP_liftComp_isEncQuery {α : Type} (oa : ProbComp α) :
    IsQueryBoundP (liftComp oa (INDDollarOracleSpec M C)) IsEncQuery 0 :=
  (isQueryBoundP_false oa 0).simulateQ_of_step nofun fun t _ =>
    (isQueryBoundP_query_iff _ (Sum.inl t) 0).2 nofun
