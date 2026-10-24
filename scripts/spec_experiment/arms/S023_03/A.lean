lemma evalDist_singleIdeal_run'_eq_tableSample [Fintype Nonce] [Finite Digest]
    (adv : UnlinkAdversary TagId Nonce Digest) :
    𝒟[(simulateQ (singleIdealQueryImpl (sessionsPerTag := sessionsPerTag)) adv).run'
        (UnlinkState.init, ∅)] =
      𝒟[($ᵗ ((TagId × Fin sessionsPerTag) × Nonce → Digest)) >>= fun g =>
          (simulateQ (singleTableHandler g) adv).run' UnlinkState.init] :=
  let : MeasurableSpace Digest := ⊤
  evalDist_simulateQ_singleIdealQueryImpl_run'_eq_tableExtending
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample adv _ ∅
