-- imports: VCVio.ProgramLogic.Library
lemma programmedPreimage_perKey_eq_tsum [DecidableEq Domain]
    (domainSample : PK → ProbComp Domain) (pk : PK) (sk : SK) (qSign qHash : ℕ)
    (adv : SignatureAlg.UnforgeableAdversary
      (GPVHashAndSign (m := OracleComp (unifSpec + (Salt × M →ₒ Range))) psf hr M Salt)) :
    Pr{let z ← (do
        let y ← ($ᵗ Range : ProbComp Range)
        let x ← psf.trapdoorSample pk sk y
        let x' ← programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash pk y
        pure (decide (x' = x)) : ProbComp Bool)}[z = true]
      = ∑' y : Range, Pr{let x ← ($ᵗ Range : ProbComp Range)}[x = y] *
          Pr{let z ← (do
            let x ← psf.trapdoorSample pk sk y
            let x' ← programmedPreimageReduction psf hr M Salt adv domainSample qSign qHash pk y
            pure (decide (x' = x)) : ProbComp Bool)}[z = true] :=
  OracleComp.prEvent_bind_eq_tsum ..
