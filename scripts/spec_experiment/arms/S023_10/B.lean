-- imports: VCVio.ProgramLogic.Library
theorem ITSRAdvantage_eq_evalDist_experiment [DecidableEq K] [DecidableEq X]
    [DecidableEq Index] {prob : ITSRProblem K X Y Index} (adv : ITSRAdversary prob) :
    ITSRAdvantage adv = 𝒟[ITSRExperiment adv] {true} :=
  prEvent_eq_evalDist_decide ..
