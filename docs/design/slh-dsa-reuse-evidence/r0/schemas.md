# Readable selected contract schemas

These renderings explain the 77 selected signatures. The checked expected types are the
closed structural kernel expressions in `kernel-types.json`; rendering is not a parser input.
Fully quantified binders, implicit instances and universes are retained in that artifact.

## `SLHDSA.Security.strongUnforgeableAdvantage_romScheme_pure_le_securityBound`

```lean
∀ {vp : SLHDSA.ValidatedParams} {core : SLHDSA.CorePrimitives vp.params} [inst : SampleableType core.Y]
  [inst_1 : SampleableType (SLHDSA.Bytes vp.params.m)] [inst_2 : DecidableEq.{1} core.Y]
  [inst_3 : SampleableType core.SkSeed] [inst_4 : SampleableType core.SkPrf] [inst_5 : DecidableEq.{1} core.PkSeed]
  [inst_6 : DecidableEq.{1} core.AdrsKey] [inst_7 : DecidableEq.{1} core.SkPrf],
  core.ByteLaws →
    SLHDSA.CorePrimitives.KeyDiscipline vp core →
      LE.le.{0} (Nat.card.{0} core.Y) (Nat.card.{0} core.SkPrf) →
        ∀ (e : Equiv.{1, 1} core.SkSeed core.Y) (optRand : SLHDSA.PublicKeyCore core → ProbComp core.Y)
          (pkSeed : core.PkSeed)
          {adv :
            SignatureAlg.StrongUnforgeableAdversary.{0}
              (SLHDSA.Security.romScheme core e optRand (Pure.pure.{0, 0} pkSeed))}
          {qh qs : ℕ},
          adv.RomQueryBound qh qs →
            LE.le.{0} (SignatureAlg.strongUnforgeableAdvantage.{0, 0} (ProbCompRuntime.rom (SLHDSA.hashSpec core)) adv)
              (SLHDSA.Security.securityBound vp.params (Nat.card.{0} core.Y) 2 1 qh qs)
```

## `SLHDSA.Security.securityTarget_two_one`

```lean
∀ {vp : SLHDSA.ValidatedParams} {core : SLHDSA.CorePrimitives vp.params} [inst : SampleableType core.Y]
  [inst_1 : SampleableType (SLHDSA.Bytes vp.params.m)] [inst_2 : DecidableEq.{1} core.Y]
  [inst_3 : SampleableType core.SkSeed] [inst_4 : SampleableType core.SkPrf] [inst_5 : DecidableEq.{1} core.PkSeed]
  [inst_6 : DecidableEq.{1} core.AdrsKey] [inst_7 : DecidableEq.{1} core.SkPrf],
  core.ByteLaws →
    SLHDSA.CorePrimitives.KeyDiscipline vp core →
      LE.le.{0} (Nat.card.{0} core.Y) (Nat.card.{0} core.SkPrf) →
        ∀ (e : Equiv.{1, 1} core.SkSeed core.Y) (optRand : SLHDSA.PublicKeyCore core → ProbComp core.Y),
          SLHDSA.Security.SecurityTarget core e optRand 2 1
```

## `SLHDSA.Security.strongUnforgeableAdvantage_romScheme_le_securityBound`

```lean
∀ {vp : SLHDSA.ValidatedParams} {core : SLHDSA.CorePrimitives vp.params} [inst : SampleableType core.Y]
  [inst_1 : SampleableType (SLHDSA.Bytes vp.params.m)] [inst_2 : DecidableEq.{1} core.Y]
  [inst_3 : SampleableType core.SkSeed] [inst_4 : SampleableType core.SkPrf] [inst_5 : DecidableEq.{1} core.PkSeed]
  [inst_6 : DecidableEq.{1} core.AdrsKey] [inst_7 : DecidableEq.{1} core.SkPrf],
  core.ByteLaws →
    SLHDSA.CorePrimitives.KeyDiscipline vp core →
      LE.le.{0} (Nat.card.{0} core.Y) (Nat.card.{0} core.SkPrf) →
        ∀ (e : Equiv.{1, 1} core.SkSeed core.Y) (optRand : SLHDSA.PublicKeyCore core → ProbComp core.Y)
          (pkSeedDist : ProbComp core.PkSeed)
          (adv : SignatureAlg.StrongUnforgeableAdversary.{0} (SLHDSA.Security.romScheme core e optRand pkSeedDist))
          {qh qs : ℕ},
          adv.RomQueryBound qh qs →
            LE.le.{0} (SignatureAlg.strongUnforgeableAdvantage.{0, 0} (ProbCompRuntime.rom (SLHDSA.hashSpec core)) adv)
              (SLHDSA.Security.securityBound vp.params (Nat.card.{0} core.Y) 2 1 qh qs)
```

## `SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound`

```lean
∀ {vp : SLHDSA.ValidatedParams}
  {optRand : SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore vp) → ProbComp (SLHDSA.Security.shakeCore vp).Y},
  SLHDSA.Security.CanonicalAddressBounds vp.params →
    LE.le.{0} 16 vp.params.n →
      LE.le.{0} vp.params.n 32 →
        LE.le.{0} vp.params.n vp.params.m →
          ∀ (pkSeed : (SLHDSA.Security.shakeCore vp).PkSeed)
            (adv :
              SignatureAlg.StrongUnforgeableAdversary.{0}
                (SLHDSA.Security.shakeRomScheme vp optRand (Pure.pure.{0, 0} pkSeed)))
            {qh qs : ℕ},
            adv.RomQueryBound qh qs →
              LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage vp adv)
                (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBound vp qh qs) (SLHDSA.Security.weakKeyMass vp pkSeed))
```

## `SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_of_weakKeyMass_eq_zero`

```lean
∀ {vp : SLHDSA.ValidatedParams}
  {optRand : SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore vp) → ProbComp (SLHDSA.Security.shakeCore vp).Y},
  SLHDSA.Security.CanonicalAddressBounds vp.params →
    LE.le.{0} 16 vp.params.n →
      LE.le.{0} vp.params.n 32 →
        LE.le.{0} vp.params.n vp.params.m →
          ∀ {pkSeed : (SLHDSA.Security.shakeCore vp).PkSeed},
            Eq.{1} (SLHDSA.Security.weakKeyMass vp pkSeed) 0 →
              ∀
                (adv :
                  SignatureAlg.StrongUnforgeableAdversary.{0}
                    (SLHDSA.Security.shakeRomScheme vp optRand (Pure.pure.{0, 0} pkSeed)))
                {qh qs : ℕ},
                adv.RomQueryBound qh qs →
                  LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage vp adv) (SLHDSA.Security.byteBound vp qh qs)
```

## `SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_of_n_eq_32`

```lean
∀ {vp : SLHDSA.ValidatedParams}
  {optRand : SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore vp) → ProbComp (SLHDSA.Security.shakeCore vp).Y},
  SLHDSA.Security.CanonicalAddressBounds vp.params →
    Eq.{1} vp.params.n 32 →
      LE.le.{0} vp.params.n vp.params.m →
        ∀ {pkSeed : (SLHDSA.Security.shakeCore vp).PkSeed},
          ¬SLHDSA.Security.IsHonestKey vp (SLHDSA.Security.shakeCore vp)
                (SLHDSA.Security.adrsKeyOfList vp (Vector.toList.{0} pkSeed)) →
            ∀
              (adv :
                SignatureAlg.StrongUnforgeableAdversary.{0}
                  (SLHDSA.Security.shakeRomScheme vp optRand (Pure.pure.{0, 0} pkSeed)))
              {qh qs : ℕ},
              adv.RomQueryBound qh qs →
                LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage vp adv) (SLHDSA.Security.byteBound vp qh qs)
```

## `SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_of_prEvent_optRand_le`

```lean
∀ {vp : SLHDSA.ValidatedParams}
  {optRand : SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore vp) → ProbComp (SLHDSA.Security.shakeCore vp).Y},
  SLHDSA.Security.CanonicalAddressBounds vp.params →
    LE.le.{0} 16 vp.params.n →
      LE.le.{0} vp.params.n 32 →
        LE.le.{0} vp.params.n vp.params.m →
          ∀ (pkSeed : (SLHDSA.Security.shakeCore vp).PkSeed) {ε : ENNReal},
            (∀ (pk : SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore vp)),
                LE.le.{0} Pr{let r ← optRand pk}[Eq.{1} r pkSeed] ε) →
              ∀
                (adv :
                  SignatureAlg.StrongUnforgeableAdversary.{0}
                    (SLHDSA.Security.shakeRomScheme vp optRand (Pure.pure.{0, 0} pkSeed)))
                {qh qs : ℕ},
                adv.RomQueryBound qh qs →
                  LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage vp adv)
                    (HAdd.hAdd.{0, 0, 0}
                      (HAdd.hAdd.{0, 0, 0}
                        (HAdd.hAdd.{0, 0, 0}
                          (SLHDSA.Security.securityBound vp.params (HPow.hPow.{0, 0, 0} 256 vp.params.n) 2 1 qh qs)
                          (HDiv.hDiv.{0, 0, 0} 1 ↑(HPow.hPow.{0, 0, 0} 256 vp.params.n)))
                        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (↑qs) ε)
                          (HDiv.hDiv.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} ↑qh ↑qs) 1)
                            ↑(HPow.hPow.{0, 0, 0} 256 vp.params.n))))
                      (SLHDSA.Security.weakKeyMass vp pkSeed))
```

## `SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_hedged`

```lean
∀ {vp : SLHDSA.ValidatedParams},
  SLHDSA.Security.CanonicalAddressBounds vp.params →
    LE.le.{0} 16 vp.params.n →
      LE.le.{0} vp.params.n 32 →
        LE.le.{0} vp.params.n vp.params.m →
          ∀ (pkSeed : (SLHDSA.Security.shakeCore vp).PkSeed)
            (adv :
              SignatureAlg.StrongUnforgeableAdversary.{0}
                (SLHDSA.Security.shakeRomScheme vp (fun x => $ᵗ (SLHDSA.Security.shakeCore vp).Y)
                  (Pure.pure.{0, 0} pkSeed)))
            {qh qs : ℕ},
            adv.RomQueryBound qh qs →
              LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage vp adv)
                (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBoundHedged vp qh qs) (SLHDSA.Security.weakKeyMass vp pkSeed))
```

## `SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_hedged_of_n_eq_32`

```lean
∀ {vp : SLHDSA.ValidatedParams},
  SLHDSA.Security.CanonicalAddressBounds vp.params →
    Eq.{1} vp.params.n 32 →
      LE.le.{0} vp.params.n vp.params.m →
        ∀ {pkSeed : (SLHDSA.Security.shakeCore vp).PkSeed},
          ¬SLHDSA.Security.IsHonestKey vp (SLHDSA.Security.shakeCore vp)
                (SLHDSA.Security.adrsKeyOfList vp (Vector.toList.{0} pkSeed)) →
            ∀
              (adv :
                SignatureAlg.StrongUnforgeableAdversary.{0}
                  (SLHDSA.Security.shakeRomScheme vp (fun x => $ᵗ (SLHDSA.Security.shakeCore vp).Y)
                    (Pure.pure.{0, 0} pkSeed)))
              {qh qs : ℕ},
              adv.RomQueryBound qh qs →
                LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage vp adv) (SLHDSA.Security.byteBoundHedged vp qh qs)
```

## `SLHDSA.Security.shakeStrongAdvantage_pure_le_min_of_n_eq_32`

```lean
∀ {vp : SLHDSA.ValidatedParams}
  {optRand : SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore vp) → ProbComp (SLHDSA.Security.shakeCore vp).Y},
  SLHDSA.Security.CanonicalAddressBounds vp.params →
    Eq.{1} vp.params.n 32 →
      LE.le.{0} vp.params.n vp.params.m →
        ∀ (pkSeed : (SLHDSA.Security.shakeCore vp).PkSeed)
          (adv :
            SignatureAlg.StrongUnforgeableAdversary.{0}
              (SLHDSA.Security.shakeRomScheme vp optRand (Pure.pure.{0, 0} pkSeed)))
          {qh qs : ℕ},
          adv.RomQueryBound qh qs →
            LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage vp adv)
              (Min.min.{0}
                (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBound vp qh qs) (SLHDSA.Security.weakKeyMass vp pkSeed))
                (SLHDSA.Security.everySeedBound vp qh qs))
```

## `SLHDSA.Security.shakeStrongAdvantage_pure_le_min_hedged_of_n_eq_32`

```lean
∀ {vp : SLHDSA.ValidatedParams},
  SLHDSA.Security.CanonicalAddressBounds vp.params →
    Eq.{1} vp.params.n 32 →
      LE.le.{0} vp.params.n vp.params.m →
        ∀ (pkSeed : (SLHDSA.Security.shakeCore vp).PkSeed)
          (adv :
            SignatureAlg.StrongUnforgeableAdversary.{0}
              (SLHDSA.Security.shakeRomScheme vp (fun x => $ᵗ (SLHDSA.Security.shakeCore vp).Y)
                (Pure.pure.{0, 0} pkSeed)))
          {qh qs : ℕ},
          adv.RomQueryBound qh qs →
            LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage vp adv)
              (Min.min.{0}
                (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBoundHedged vp qh qs) (SLHDSA.Security.weakKeyMass vp pkSeed))
                (SLHDSA.Security.everySeedBoundHedged vp qh qs))
```

## `SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_add_weakKeyMass_mul`

```lean
∀ {vp : SLHDSA.ValidatedParams}
  {optRand : SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore vp) → ProbComp (SLHDSA.Security.shakeCore vp).Y},
  SLHDSA.Security.CanonicalAddressBounds vp.params →
    LE.le.{0} 16 vp.params.n →
      LE.le.{0} vp.params.n 32 →
        LE.le.{0} vp.params.n vp.params.m →
          ∀ (pkSeed : (SLHDSA.Security.shakeCore vp).PkSeed)
            (adv :
              SignatureAlg.StrongUnforgeableAdversary.{0}
                (SLHDSA.Security.shakeRomScheme vp optRand (Pure.pure.{0, 0} pkSeed)))
            {qh qs : ℕ},
            adv.RomQueryBound qh qs →
              LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage vp adv)
                (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBound vp qh qs)
                  (HMul.hMul.{0, 0, 0} (SLHDSA.Security.weakKeyMass vp pkSeed)
                    (SLHDSA.Security.weakSeedFactor vp (SLHDSA.Security.everySeedBound vp qh qs))))
```

## `SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_hedged_add_weakKeyMass_mul`

```lean
∀ {vp : SLHDSA.ValidatedParams},
  SLHDSA.Security.CanonicalAddressBounds vp.params →
    LE.le.{0} 16 vp.params.n →
      LE.le.{0} vp.params.n 32 →
        LE.le.{0} vp.params.n vp.params.m →
          ∀ (pkSeed : (SLHDSA.Security.shakeCore vp).PkSeed)
            (adv :
              SignatureAlg.StrongUnforgeableAdversary.{0}
                (SLHDSA.Security.shakeRomScheme vp (fun x => $ᵗ (SLHDSA.Security.shakeCore vp).Y)
                  (Pure.pure.{0, 0} pkSeed)))
            {qh qs : ℕ},
            adv.RomQueryBound qh qs →
              LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage vp adv)
                (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBoundHedged vp qh qs)
                  (HMul.hMul.{0, 0, 0} (SLHDSA.Security.weakKeyMass vp pkSeed)
                    (SLHDSA.Security.weakSeedFactor vp (SLHDSA.Security.everySeedBoundHedged vp qh qs))))
```

## `SLHDSA.Security.shakeStrongAdvantage_le_securityBound`

```lean
∀ {vp : SLHDSA.ValidatedParams}
  {optRand : SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore vp) → ProbComp (SLHDSA.Security.shakeCore vp).Y},
  SLHDSA.Security.CanonicalAddressBounds vp.params →
    LE.le.{0} 16 vp.params.n →
      LE.le.{0} vp.params.n 32 →
        LE.le.{0} vp.params.n vp.params.m →
          ∀
            (adv :
              SignatureAlg.StrongUnforgeableAdversary.{0}
                (SLHDSA.Security.shakeRomScheme vp optRand ($ᵗ (SLHDSA.Security.shakeCore vp).PkSeed)))
            {qh qs : ℕ},
            adv.RomQueryBound qh qs →
              LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage vp adv)
                (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBound vp qh qs)
                  (HMul.hMul.{0, 0, 0}
                    (HDiv.hDiv.{0, 0, 0} (↑(SLHDSA.Security.honestAdrsCount vp)) (HPow.hPow.{0, 0, 0} 2 256))
                    (SLHDSA.Security.weakSeedFactor vp (SLHDSA.Security.everySeedBound vp qh qs))))
```

## `SLHDSA.Security.shakeStrongAdvantage_le_securityBound_hedged`

```lean
∀ {vp : SLHDSA.ValidatedParams},
  SLHDSA.Security.CanonicalAddressBounds vp.params →
    LE.le.{0} 16 vp.params.n →
      LE.le.{0} vp.params.n 32 →
        LE.le.{0} vp.params.n vp.params.m →
          ∀
            (adv :
              SignatureAlg.StrongUnforgeableAdversary.{0}
                (SLHDSA.Security.shakeRomScheme vp (fun x => $ᵗ (SLHDSA.Security.shakeCore vp).Y)
                  ($ᵗ (SLHDSA.Security.shakeCore vp).PkSeed)))
            {qh qs : ℕ},
            adv.RomQueryBound qh qs →
              LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage vp adv)
                (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBoundHedged vp qh qs)
                  (HMul.hMul.{0, 0, 0}
                    (HDiv.hDiv.{0, 0, 0} (↑(SLHDSA.Security.honestAdrsCount vp)) (HPow.hPow.{0, 0, 0} 2 256))
                    (SLHDSA.Security.weakSeedFactor vp (SLHDSA.Security.everySeedBoundHedged vp qh qs))))
```

## `SLHDSA.Security.shakeStrongAdvantage_le_securityBound_of_n_eq_32`

```lean
∀ {vp : SLHDSA.ValidatedParams}
  {optRand : SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore vp) → ProbComp (SLHDSA.Security.shakeCore vp).Y},
  SLHDSA.Security.CanonicalAddressBounds vp.params →
    Eq.{1} vp.params.n 32 →
      LE.le.{0} vp.params.n vp.params.m →
        ∀
          (adv :
            SignatureAlg.StrongUnforgeableAdversary.{0}
              (SLHDSA.Security.shakeRomScheme vp optRand ($ᵗ (SLHDSA.Security.shakeCore vp).PkSeed)))
          {qh qs : ℕ},
          adv.RomQueryBound qh qs →
            LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage vp adv)
              (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBound vp qh qs)
                (HMul.hMul.{0, 0, 0}
                  (HDiv.hDiv.{0, 0, 0} (↑(SLHDSA.Security.honestAdrsCount vp)) (HPow.hPow.{0, 0, 0} 2 256))
                  (Min.min.{0} 1 (SLHDSA.Security.everySeedBound vp qh qs))))
```

## `SLHDSA.Security.shakeStrongAdvantage_le_securityBound_hedged_of_n_eq_32`

```lean
∀ {vp : SLHDSA.ValidatedParams},
  SLHDSA.Security.CanonicalAddressBounds vp.params →
    Eq.{1} vp.params.n 32 →
      LE.le.{0} vp.params.n vp.params.m →
        ∀
          (adv :
            SignatureAlg.StrongUnforgeableAdversary.{0}
              (SLHDSA.Security.shakeRomScheme vp (fun x => $ᵗ (SLHDSA.Security.shakeCore vp).Y)
                ($ᵗ (SLHDSA.Security.shakeCore vp).PkSeed)))
          {qh qs : ℕ},
          adv.RomQueryBound qh qs →
            LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage vp adv)
              (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBoundHedged vp qh qs)
                (HMul.hMul.{0, 0, 0}
                  (HDiv.hDiv.{0, 0, 0} (↑(SLHDSA.Security.honestAdrsCount vp)) (HPow.hPow.{0, 0, 0} 2 256))
                  (Min.min.{0} 1 (SLHDSA.Security.everySeedBoundHedged vp qh qs))))
```

## `SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_validatedParams`

```lean
∀ (set : SLHDSA.FipsParameterSet)
  {optRand :
    SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore set.validatedParams) →
      ProbComp (SLHDSA.Security.shakeCore set.validatedParams).Y}
  (pkSeed : (SLHDSA.Security.shakeCore set.validatedParams).PkSeed)
  (adv :
    SignatureAlg.StrongUnforgeableAdversary.{0}
      (SLHDSA.Security.shakeRomScheme set.validatedParams optRand (Pure.pure.{0, 0} pkSeed)))
  {qh qs : ℕ},
  adv.RomQueryBound qh qs →
    LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage set.validatedParams adv)
      (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBound set.validatedParams qh qs)
        (SLHDSA.Security.weakKeyMass set.validatedParams pkSeed))
```

## `SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_hedged_validatedParams`

```lean
∀ (set : SLHDSA.FipsParameterSet) (pkSeed : (SLHDSA.Security.shakeCore set.validatedParams).PkSeed)
  (adv :
    SignatureAlg.StrongUnforgeableAdversary.{0}
      (SLHDSA.Security.shakeRomScheme set.validatedParams
        (fun x => $ᵗ (SLHDSA.Security.shakeCore set.validatedParams).Y) (Pure.pure.{0, 0} pkSeed)))
  {qh qs : ℕ},
  adv.RomQueryBound qh qs →
    LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage set.validatedParams adv)
      (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBoundHedged set.validatedParams qh qs)
        (SLHDSA.Security.weakKeyMass set.validatedParams pkSeed))
```

## `SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_add_validatedParams`

```lean
∀ (set : SLHDSA.FipsParameterSet),
  Eq.{1} set.validatedParams.params.n 32 →
    ∀
      {optRand :
        SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore set.validatedParams) →
          ProbComp (SLHDSA.Security.shakeCore set.validatedParams).Y}
      (pkSeed : (SLHDSA.Security.shakeCore set.validatedParams).PkSeed)
      (adv :
        SignatureAlg.StrongUnforgeableAdversary.{0}
          (SLHDSA.Security.shakeRomScheme set.validatedParams optRand (Pure.pure.{0, 0} pkSeed)))
      {qh qs : ℕ},
      adv.RomQueryBound qh qs →
        LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage set.validatedParams adv)
          (SLHDSA.Security.everySeedBound set.validatedParams qh qs)
```

## `SLHDSA.Security.shakeStrongAdvantage_pure_le_securityBound_add_hedged_validatedParams`

```lean
∀ (set : SLHDSA.FipsParameterSet),
  Eq.{1} set.validatedParams.params.n 32 →
    ∀ (pkSeed : (SLHDSA.Security.shakeCore set.validatedParams).PkSeed)
      (adv :
        SignatureAlg.StrongUnforgeableAdversary.{0}
          (SLHDSA.Security.shakeRomScheme set.validatedParams
            (fun x => $ᵗ (SLHDSA.Security.shakeCore set.validatedParams).Y) (Pure.pure.{0, 0} pkSeed)))
      {qh qs : ℕ},
      adv.RomQueryBound qh qs →
        LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage set.validatedParams adv)
          (SLHDSA.Security.everySeedBoundHedged set.validatedParams qh qs)
```

## `SLHDSA.Security.shakeStrongAdvantage_le_securityBound_validatedParams`

```lean
∀ (set : SLHDSA.FipsParameterSet)
  {optRand :
    SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore set.validatedParams) →
      ProbComp (SLHDSA.Security.shakeCore set.validatedParams).Y}
  (adv :
    SignatureAlg.StrongUnforgeableAdversary.{0}
      (SLHDSA.Security.shakeRomScheme set.validatedParams optRand
        ($ᵗ (SLHDSA.Security.shakeCore set.validatedParams).PkSeed)))
  {qh qs : ℕ},
  adv.RomQueryBound qh qs →
    LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage set.validatedParams adv)
      (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBound set.validatedParams qh qs)
        (HMul.hMul.{0, 0, 0}
          (HDiv.hDiv.{0, 0, 0} (↑(SLHDSA.Security.honestAdrsCount set.validatedParams)) (HPow.hPow.{0, 0, 0} 2 256))
          (SLHDSA.Security.weakSeedFactor set.validatedParams
            (SLHDSA.Security.everySeedBound set.validatedParams qh qs))))
```

## `SLHDSA.Security.shakeStrongAdvantage_le_securityBound_hedged_validatedParams`

```lean
∀ (set : SLHDSA.FipsParameterSet)
  (adv :
    SignatureAlg.StrongUnforgeableAdversary.{0}
      (SLHDSA.Security.shakeRomScheme set.validatedParams
        (fun x => $ᵗ (SLHDSA.Security.shakeCore set.validatedParams).Y)
        ($ᵗ (SLHDSA.Security.shakeCore set.validatedParams).PkSeed)))
  {qh qs : ℕ},
  adv.RomQueryBound qh qs →
    LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage set.validatedParams adv)
      (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBoundHedged set.validatedParams qh qs)
        (HMul.hMul.{0, 0, 0}
          (HDiv.hDiv.{0, 0, 0} (↑(SLHDSA.Security.honestAdrsCount set.validatedParams)) (HPow.hPow.{0, 0, 0} 2 256))
          (SLHDSA.Security.weakSeedFactor set.validatedParams
            (SLHDSA.Security.everySeedBoundHedged set.validatedParams qh qs))))
```

## `SLHDSA.Security.shakeAdvantage_pure_le_securityBound`

```lean
∀ {vp : SLHDSA.ValidatedParams}
  {optRand : SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore vp) → ProbComp (SLHDSA.Security.shakeCore vp).Y},
  SLHDSA.Security.CanonicalAddressBounds vp.params →
    LE.le.{0} 16 vp.params.n →
      LE.le.{0} vp.params.n 32 →
        LE.le.{0} vp.params.n vp.params.m →
          ∀ (pkSeed : (SLHDSA.Security.shakeCore vp).PkSeed)
            (adv :
              SignatureAlg.UnforgeableAdversary.{0}
                (SLHDSA.Security.shakeRomScheme vp optRand (Pure.pure.{0, 0} pkSeed)))
            {qh qs : ℕ},
            adv.RomQueryBound qh qs →
              LE.le.{0} (SLHDSA.Security.shakeAdvantage vp adv)
                (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBound vp qh qs) (SLHDSA.Security.weakKeyMass vp pkSeed))
```

## `SLHDSA.Security.shakeAdvantage_le_securityBound`

```lean
∀ {vp : SLHDSA.ValidatedParams}
  {optRand : SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore vp) → ProbComp (SLHDSA.Security.shakeCore vp).Y},
  SLHDSA.Security.CanonicalAddressBounds vp.params →
    LE.le.{0} 16 vp.params.n →
      LE.le.{0} vp.params.n 32 →
        LE.le.{0} vp.params.n vp.params.m →
          ∀
            (adv :
              SignatureAlg.UnforgeableAdversary.{0}
                (SLHDSA.Security.shakeRomScheme vp optRand ($ᵗ (SLHDSA.Security.shakeCore vp).PkSeed)))
            {qh qs : ℕ},
            adv.RomQueryBound qh qs →
              LE.le.{0} (SLHDSA.Security.shakeAdvantage vp adv)
                (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBound vp qh qs)
                  (HMul.hMul.{0, 0, 0}
                    (HDiv.hDiv.{0, 0, 0} (↑(SLHDSA.Security.honestAdrsCount vp)) (HPow.hPow.{0, 0, 0} 2 256))
                    (SLHDSA.Security.weakSeedFactor vp (SLHDSA.Security.everySeedBound vp qh qs))))
```

## `SLHDSA.Security.shakeAdvantage_le_securityBound_hedged`

```lean
∀ {vp : SLHDSA.ValidatedParams},
  SLHDSA.Security.CanonicalAddressBounds vp.params →
    LE.le.{0} 16 vp.params.n →
      LE.le.{0} vp.params.n 32 →
        LE.le.{0} vp.params.n vp.params.m →
          ∀
            (adv :
              SignatureAlg.UnforgeableAdversary.{0}
                (SLHDSA.Security.shakeRomScheme vp (fun x => $ᵗ (SLHDSA.Security.shakeCore vp).Y)
                  ($ᵗ (SLHDSA.Security.shakeCore vp).PkSeed)))
            {qh qs : ℕ},
            adv.RomQueryBound qh qs →
              LE.le.{0} (SLHDSA.Security.shakeAdvantage vp adv)
                (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBoundHedged vp qh qs)
                  (HMul.hMul.{0, 0, 0}
                    (HDiv.hDiv.{0, 0, 0} (↑(SLHDSA.Security.honestAdrsCount vp)) (HPow.hPow.{0, 0, 0} 2 256))
                    (SLHDSA.Security.weakSeedFactor vp (SLHDSA.Security.everySeedBoundHedged vp qh qs))))
```

## `SLHDSA.Security.shakeAdvantage_pure_le_securityBound_validatedParams`

```lean
∀ (set : SLHDSA.FipsParameterSet)
  {optRand :
    SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore set.validatedParams) →
      ProbComp (SLHDSA.Security.shakeCore set.validatedParams).Y}
  (pkSeed : (SLHDSA.Security.shakeCore set.validatedParams).PkSeed)
  (adv :
    SignatureAlg.UnforgeableAdversary.{0}
      (SLHDSA.Security.shakeRomScheme set.validatedParams optRand (Pure.pure.{0, 0} pkSeed)))
  {qh qs : ℕ},
  adv.RomQueryBound qh qs →
    LE.le.{0} (SLHDSA.Security.shakeAdvantage set.validatedParams adv)
      (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBound set.validatedParams qh qs)
        (SLHDSA.Security.weakKeyMass set.validatedParams pkSeed))
```

## `SLHDSA.Security.shakeAdvantage_pure_le_securityBound_hedged_validatedParams`

```lean
∀ (set : SLHDSA.FipsParameterSet) (pkSeed : (SLHDSA.Security.shakeCore set.validatedParams).PkSeed)
  (adv :
    SignatureAlg.UnforgeableAdversary.{0}
      (SLHDSA.Security.shakeRomScheme set.validatedParams
        (fun x => $ᵗ (SLHDSA.Security.shakeCore set.validatedParams).Y) (Pure.pure.{0, 0} pkSeed)))
  {qh qs : ℕ},
  adv.RomQueryBound qh qs →
    LE.le.{0} (SLHDSA.Security.shakeAdvantage set.validatedParams adv)
      (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBoundHedged set.validatedParams qh qs)
        (SLHDSA.Security.weakKeyMass set.validatedParams pkSeed))
```

## `SLHDSA.Security.shakeAdvantage_pure_le_securityBound_add_validatedParams`

```lean
∀ (set : SLHDSA.FipsParameterSet),
  Eq.{1} set.validatedParams.params.n 32 →
    ∀
      {optRand :
        SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore set.validatedParams) →
          ProbComp (SLHDSA.Security.shakeCore set.validatedParams).Y}
      (pkSeed : (SLHDSA.Security.shakeCore set.validatedParams).PkSeed)
      (adv :
        SignatureAlg.UnforgeableAdversary.{0}
          (SLHDSA.Security.shakeRomScheme set.validatedParams optRand (Pure.pure.{0, 0} pkSeed)))
      {qh qs : ℕ},
      adv.RomQueryBound qh qs →
        LE.le.{0} (SLHDSA.Security.shakeAdvantage set.validatedParams adv)
          (SLHDSA.Security.everySeedBound set.validatedParams qh qs)
```

## `SLHDSA.Security.shakeAdvantage_pure_le_securityBound_add_hedged_validatedParams`

```lean
∀ (set : SLHDSA.FipsParameterSet),
  Eq.{1} set.validatedParams.params.n 32 →
    ∀ (pkSeed : (SLHDSA.Security.shakeCore set.validatedParams).PkSeed)
      (adv :
        SignatureAlg.UnforgeableAdversary.{0}
          (SLHDSA.Security.shakeRomScheme set.validatedParams
            (fun x => $ᵗ (SLHDSA.Security.shakeCore set.validatedParams).Y) (Pure.pure.{0, 0} pkSeed)))
      {qh qs : ℕ},
      adv.RomQueryBound qh qs →
        LE.le.{0} (SLHDSA.Security.shakeAdvantage set.validatedParams adv)
          (SLHDSA.Security.everySeedBoundHedged set.validatedParams qh qs)
```

## `SLHDSA.Security.shakeAdvantage_le_securityBound_validatedParams`

```lean
∀ (set : SLHDSA.FipsParameterSet)
  {optRand :
    SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore set.validatedParams) →
      ProbComp (SLHDSA.Security.shakeCore set.validatedParams).Y}
  (adv :
    SignatureAlg.UnforgeableAdversary.{0}
      (SLHDSA.Security.shakeRomScheme set.validatedParams optRand
        ($ᵗ (SLHDSA.Security.shakeCore set.validatedParams).PkSeed)))
  {qh qs : ℕ},
  adv.RomQueryBound qh qs →
    LE.le.{0} (SLHDSA.Security.shakeAdvantage set.validatedParams adv)
      (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBound set.validatedParams qh qs)
        (HMul.hMul.{0, 0, 0}
          (HDiv.hDiv.{0, 0, 0} (↑(SLHDSA.Security.honestAdrsCount set.validatedParams)) (HPow.hPow.{0, 0, 0} 2 256))
          (SLHDSA.Security.weakSeedFactor set.validatedParams
            (SLHDSA.Security.everySeedBound set.validatedParams qh qs))))
```

## `SLHDSA.Security.shakeAdvantage_le_securityBound_hedged_validatedParams`

```lean
∀ (set : SLHDSA.FipsParameterSet)
  (adv :
    SignatureAlg.UnforgeableAdversary.{0}
      (SLHDSA.Security.shakeRomScheme set.validatedParams
        (fun x => $ᵗ (SLHDSA.Security.shakeCore set.validatedParams).Y)
        ($ᵗ (SLHDSA.Security.shakeCore set.validatedParams).PkSeed)))
  {qh qs : ℕ},
  adv.RomQueryBound qh qs →
    LE.le.{0} (SLHDSA.Security.shakeAdvantage set.validatedParams adv)
      (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBoundHedged set.validatedParams qh qs)
        (HMul.hMul.{0, 0, 0}
          (HDiv.hDiv.{0, 0, 0} (↑(SLHDSA.Security.honestAdrsCount set.validatedParams)) (HPow.hPow.{0, 0, 0} 2 256))
          (SLHDSA.Security.weakSeedFactor set.validatedParams
            (SLHDSA.Security.everySeedBoundHedged set.validatedParams qh qs))))
```

## `SLHDSA.Security.shakeAdvantage_le_shakeStrongAdvantage`

```lean
∀ {vp : SLHDSA.ValidatedParams}
  {optRand : SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore vp) → ProbComp (SLHDSA.Security.shakeCore vp).Y}
  {pkSeedDist : ProbComp (SLHDSA.Security.shakeCore vp).PkSeed}
  (adv : SignatureAlg.UnforgeableAdversary.{0} (SLHDSA.Security.shakeRomScheme vp optRand pkSeedDist)),
  LE.le.{0} (SLHDSA.Security.shakeAdvantage vp adv)
    (SLHDSA.Security.shakeStrongAdvantage vp
      (SignatureAlg.StrongUnforgeableAdversary.mk.{0} (SignatureAlg.UnforgeableAdversary.main.{0} adv)))
```

## `SLHDSA.Security.shakeStrongAdvantage_le_lintegral`

```lean
∀ {vp : SLHDSA.ValidatedParams} [inst : MeasurableSpace.{0} (SLHDSA.Security.shakeCore vp).PkSeed]
  [DiscreteMeasurableSpace.{0} (SLHDSA.Security.shakeCore vp).PkSeed]
  {optRand : SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore vp) → ProbComp (SLHDSA.Security.shakeCore vp).Y}
  (pkSeedDist : ProbComp (SLHDSA.Security.shakeCore vp).PkSeed) (β : (SLHDSA.Security.shakeCore vp).PkSeed → ENNReal)
  {qh qs : ℕ},
  (∀ (pkSeed : (SLHDSA.Security.shakeCore vp).PkSeed)
      (adv :
        SignatureAlg.StrongUnforgeableAdversary.{0}
          (SLHDSA.Security.shakeRomScheme vp optRand (Pure.pure.{0, 0} pkSeed))),
      adv.RomQueryBound qh qs → LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage vp adv) (β pkSeed)) →
    ∀ (adv : SignatureAlg.StrongUnforgeableAdversary.{0} (SLHDSA.Security.shakeRomScheme vp optRand pkSeedDist)),
      adv.RomQueryBound qh qs →
        LE.le.{0} (SLHDSA.Security.shakeStrongAdvantage vp adv)
          (∫⁻ (pkSeed : (SLHDSA.Security.shakeCore vp).PkSeed), β pkSeed ∂evalDist.{0, 0} pkSeedDist)
```

## `SLHDSA.Security.unforgeableAdvantage_romScheme_le`

```lean
∀ {vp : SLHDSA.ValidatedParams} (core : SLHDSA.CorePrimitives vp.params) [inst : SampleableType core.SkSeed]
  [inst_1 : SampleableType core.SkPrf] [inst_2 : DecidableEq.{1} core.Y] [inst_3 : SampleableType core.Y]
  [inst_4 : SampleableType (SLHDSA.Bytes vp.params.m)] [inst_5 : DecidableEq.{1} core.PkSeed]
  [inst_6 : DecidableEq.{1} core.AdrsKey] [inst_7 : DecidableEq.{1} core.SkPrf] {e : Equiv.{1, 1} core.SkSeed core.Y}
  {optRand : SLHDSA.PublicKeyCore core → ProbComp core.Y} {c r : ℕ},
  SLHDSA.Security.SecurityTarget core e optRand c r →
    ∀ (pkSeedDist : ProbComp core.PkSeed)
      (adv : SignatureAlg.UnforgeableAdversary.{0} (SLHDSA.Security.romScheme core e optRand pkSeedDist)) {qh qs : ℕ},
      adv.RomQueryBound qh qs →
        LE.le.{0} (SignatureAlg.unforgeableAdvantage.{0, 0} (ProbCompRuntime.rom (SLHDSA.hashSpec core)) adv)
          (SLHDSA.Security.securityBound vp.params (Nat.card.{0} core.Y) c r qh qs)
```

## `SignatureAlg.unforgeableAdvantage_le_strongUnforgeableAdvantage`

```lean
∀ {ι : Type u} {spec : OracleSpec.{u, 0} ι} {M PK SK S : Type}
  {sigAlg : SignatureAlg.{u} (OracleComp.{u, 0, 0} spec) M PK SK S}
  (runtime : ProbCompRuntime.{u, u_1} (OracleComp.{u, 0, 0} spec)) (adv : SignatureAlg.UnforgeableAdversary.{u} sigAlg),
  LE.le.{0} (SignatureAlg.unforgeableAdvantage.{u, u_1} runtime adv)
    (SignatureAlg.strongUnforgeableAdvantage.{u, u_1} runtime
      (SignatureAlg.StrongUnforgeableAdversary.mk.{u} (SignatureAlg.UnforgeableAdversary.main.{u} adv)))
```

## `SLHDSA.Security.wireShakeScheme_map_shakeAnswer`

```lean
∀ (vp : SLHDSA.ValidatedParams),
  LE.le.{0} vp.params.n vp.params.m →
    ∀ (ctx : SLHDSA.Security.PureContext)
      (optRand : SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore vp) → ProbComp (SLHDSA.Security.shakeCore vp).Y)
      (pkSeedDist : ProbComp (SLHDSA.Security.shakeCore vp).PkSeed),
      Eq.{1}
        (SignatureAlg.map.{0, 0} (simulateQ'.{0, 0, 0} (OracleComp.unifFwdAnswerImpl (SLHDSA.Security.shakeAnswer vp)))
          (SLHDSA.Security.wireShakeScheme vp ctx optRand pkSeedDist))
        (SignatureAlg.Wire.scheme.{0}
          (SLHDSA.Security.internalAlg vp (SLHDSA.Concrete.shakePrimitives vp.params) optRand pkSeedDist) ctx.encode
          (SLHDSA.publicKeyCodec (SLHDSA.Concrete.shakeWireCodec vp.params)).canonicalEncoding
          (SLHDSA.signatureCodec vp (SLHDSA.Concrete.shakeWireCodec vp.params)).canonicalEncoding)
```

## `SLHDSA.Security.romQueryBound_wireReduce`

```lean
∀ (vp : SLHDSA.ValidatedParams) (ctx : SLHDSA.Security.PureContext)
  {optRand : SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore vp) → ProbComp (SLHDSA.Security.shakeCore vp).Y}
  {pkSeedDist : ProbComp (SLHDSA.Security.shakeCore vp).PkSeed}
  (adv : SignatureAlg.StrongUnforgeableAdversary.{0} (SLHDSA.Security.wireShakeScheme vp ctx optRand pkSeedDist))
  {qh qs : ℕ}, adv.RomQueryBound qh qs → (SLHDSA.Security.wireReduce vp ctx adv).RomQueryBound qh qs
```

## `SLHDSA.Security.wireStrongAdvantage_le`

```lean
∀ (vp : SLHDSA.ValidatedParams) (ctx : SLHDSA.Security.PureContext)
  {optRand : SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore vp) → ProbComp (SLHDSA.Security.shakeCore vp).Y}
  {pkSeedDist : ProbComp (SLHDSA.Security.shakeCore vp).PkSeed}
  (adv : SignatureAlg.StrongUnforgeableAdversary.{0} (SLHDSA.Security.wireShakeScheme vp ctx optRand pkSeedDist)),
  LE.le.{0} (SignatureAlg.strongUnforgeableAdvantage.{0, 0} (SLHDSA.Security.shakeRuntime vp) adv)
    (SLHDSA.Security.shakeStrongAdvantage vp (SLHDSA.Security.wireReduce vp ctx adv))
```

## `SLHDSA.Security.wireStrongAdvantage_le_securityBound_validatedParams`

```lean
∀ (set : SLHDSA.FipsParameterSet) (ctx : SLHDSA.Security.PureContext)
  {optRand :
    SLHDSA.PublicKeyCore (SLHDSA.Security.shakeCore set.validatedParams) →
      ProbComp (SLHDSA.Security.shakeCore set.validatedParams).Y}
  (adv :
    SignatureAlg.StrongUnforgeableAdversary.{0}
      (SLHDSA.Security.wireShakeScheme set.validatedParams ctx optRand
        ($ᵗ (SLHDSA.Security.shakeCore set.validatedParams).PkSeed)))
  {qh qs : ℕ},
  adv.RomQueryBound qh qs →
    LE.le.{0} (SignatureAlg.strongUnforgeableAdvantage.{0, 0} (SLHDSA.Security.shakeRuntime set.validatedParams) adv)
      (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBound set.validatedParams qh qs)
        (HMul.hMul.{0, 0, 0}
          (HDiv.hDiv.{0, 0, 0} (↑(SLHDSA.Security.honestAdrsCount set.validatedParams)) (HPow.hPow.{0, 0, 0} 2 256))
          (SLHDSA.Security.weakSeedFactor set.validatedParams
            (SLHDSA.Security.everySeedBound set.validatedParams qh qs))))
```

## `SLHDSA.Security.wireStrongAdvantage_le_securityBound_hedged_validatedParams`

```lean
∀ (set : SLHDSA.FipsParameterSet) (ctx : SLHDSA.Security.PureContext)
  (adv :
    SignatureAlg.StrongUnforgeableAdversary.{0}
      (SLHDSA.Security.wireShakeScheme set.validatedParams ctx
        (fun x => $ᵗ (SLHDSA.Security.shakeCore set.validatedParams).Y)
        ($ᵗ (SLHDSA.Security.shakeCore set.validatedParams).PkSeed)))
  {qh qs : ℕ},
  adv.RomQueryBound qh qs →
    LE.le.{0} (SignatureAlg.strongUnforgeableAdvantage.{0, 0} (SLHDSA.Security.shakeRuntime set.validatedParams) adv)
      (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBoundHedged set.validatedParams qh qs)
        (HMul.hMul.{0, 0, 0}
          (HDiv.hDiv.{0, 0, 0} (↑(SLHDSA.Security.honestAdrsCount set.validatedParams)) (HPow.hPow.{0, 0, 0} 2 256))
          (SLHDSA.Security.weakSeedFactor set.validatedParams
            (SLHDSA.Security.everySeedBoundHedged set.validatedParams qh qs))))
```

## `SLHDSA.Security.ShakeProfile.strongUnforgeableAdvantage_le_boundEvaluator`

```lean
∀ (profile : SLHDSA.Security.ShakeProfile) (adv : SignatureAlg.StrongUnforgeableAdversary.{0} profile.algorithm)
  {qh qs : ℕ},
  adv.RomQueryBound qh qs →
    LE.le.{0}
      (SignatureAlg.strongUnforgeableAdvantage.{0, 0}
        (SLHDSA.Security.shakeRuntime profile.parameterSet.validatedParams) adv)
      (KeyedHash.Covering.rationalValue (profile.boundEvaluator qh qs))
```

## `SLHDSA.SHAKE128s.slhDsa_sufCma_127`

```lean
SLHDSA.SHAKE128s.Game.HasSecurityBits SLHDSA.SHAKE128s.FIPS205.scheme SLHDSA.SHAKE128s.Game.adversaryWork 127
```

## `SLHDSA.SHAKE128s.Bridge.strongUnforgeableAdvantage_eq_fixedContext`

```lean
∀ (ctx : SLHDSA.Security.PureContext)
  (adv : SignatureAlg.StrongUnforgeableAdversary.{0} (SLHDSA.SHAKE128s.Bridge.wireAlgorithm ctx)),
  Eq.{1}
    (SignatureAlg.strongUnforgeableAdvantage.{0, 0} (SLHDSA.Security.shakeRuntime SLHDSA.SHAKE128s.FIPS205.params) adv)
    ((SLHDSA.SHAKE128s.Game.securityGame SLHDSA.SHAKE128s.FIPS205.scheme).advantage ()
      (SLHDSA.SHAKE128s.Bridge.fixedContextAdversary ctx adv))
```

## `SLHDSA.SHAKE128s.Bridge.isTotalQueryBound_FIPS205_internal_verify`

```lean
∀ (pk : SLHDSA.PublicKeyCore SLHDSA.SHAKE128s.FIPS205.core) (msg : SLHDSA.SHAKE128s.Bytes)
  (signature : SLHDSA.GeneralScheme.SignatureCore SLHDSA.SHAKE128s.FIPS205.params SLHDSA.SHAKE128s.FIPS205.core),
  OracleComp.IsTotalQueryBound.{0} (SignatureAlg.verify.{0} SLHDSA.SHAKE128s.FIPS205.internal pk msg signature)
    SLHDSA.SHAKE128s.Bridge.verifierCap
```

## `SLHDSA.SHAKE128s.Bridge.isTotalQueryBound_FIPS205_verify`

```lean
∀ (pk : SLHDSA.PublicKeyCore SLHDSA.SHAKE128s.FIPS205.core) (request : SLHDSA.SHAKE128s.Message)
  (signature : SLHDSA.SHAKE128s.Bytes),
  OracleComp.IsTotalQueryBound.{0} (SLHDSA.SHAKE128s.FIPS205.scheme.verify pk request signature)
    SLHDSA.SHAKE128s.Bridge.verifierCap
```

## `SLHDSA.SHAKE128s.Bridge.withinSigningLimit_fixedContext`

```lean
∀ (ctx : SLHDSA.Security.PureContext)
  (adv : SignatureAlg.StrongUnforgeableAdversary.{0} (SLHDSA.SHAKE128s.Bridge.wireAlgorithm ctx)) {qh qs : ℕ},
  adv.RomQueryBound qh qs →
    LE.le.{0} qs SLHDSA.SHAKE128s.signingLimit →
      SLHDSA.SHAKE128s.Game.WithinSigningLimit SLHDSA.SHAKE128s.FIPS205.scheme
        (SLHDSA.SHAKE128s.Bridge.fixedContextAdversary ctx adv)
```

## `SLHDSA.SHAKE128s.Bridge.hasQueryBound_fixedContext`

```lean
∀ (ctx : SLHDSA.Security.PureContext)
  (adv : SignatureAlg.StrongUnforgeableAdversary.{0} (SLHDSA.SHAKE128s.Bridge.wireAlgorithm ctx)) {qh qs : ℕ},
  adv.RomQueryBound qh qs →
    (SLHDSA.SHAKE128s.Game.securityGame SLHDSA.SHAKE128s.FIPS205.scheme).HasQueryBound ()
      SLHDSA.SHAKE128s.Game.adversaryWork (SLHDSA.SHAKE128s.Bridge.fixedContextAdversary ctx adv)
      (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} qh qs) SLHDSA.SHAKE128s.Bridge.verifierCap)
```

## `SLHDSA.SHAKE128s.wireStrongAdvantage_le_workBound`

```lean
∀ (ctx : SLHDSA.Security.PureContext)
  (adv : SignatureAlg.StrongUnforgeableAdversary.{0} (SLHDSA.SHAKE128s.Bridge.wireAlgorithm ctx)) {qh qs : ℕ},
  adv.RomQueryBound qh qs →
    LE.le.{0} qs SLHDSA.SHAKE128s.signingLimit →
      LE.le.{0}
        (SignatureAlg.strongUnforgeableAdvantage.{0, 0} (SLHDSA.Security.shakeRuntime SLHDSA.SHAKE128s.FIPS205.params)
          adv)
        (HDiv.hDiv.{0, 0, 0} ↑(HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} qh qs) 3929) ↑(HPow.hPow.{0, 0, 0} 2 127))
```

## `SLHDSA.SHAKE128s.wireStrongAdvantage_le_min_bound`

```lean
∀ (ctx : SLHDSA.Security.PureContext)
  (adv : SignatureAlg.StrongUnforgeableAdversary.{0} (SLHDSA.SHAKE128s.Bridge.wireAlgorithm ctx)) {qh qs : ℕ},
  adv.RomQueryBound qh qs →
    LE.le.{0} qs SLHDSA.SHAKE128s.signingLimit →
      LE.le.{0}
        (SignatureAlg.strongUnforgeableAdvantage.{0, 0} (SLHDSA.Security.shakeRuntime SLHDSA.SHAKE128s.FIPS205.params)
          adv)
        (Min.min.{0}
          (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBound SLHDSA.SHAKE128s.FIPS205.params qh qs)
            (HMul.hMul.{0, 0, 0}
              (HDiv.hDiv.{0, 0, 0} (↑(SLHDSA.Security.honestAdrsCount SLHDSA.SHAKE128s.FIPS205.params))
                (HPow.hPow.{0, 0, 0} 2 256))
              (SLHDSA.Security.weakSeedFactor SLHDSA.SHAKE128s.FIPS205.params
                (SLHDSA.Security.everySeedBound SLHDSA.SHAKE128s.FIPS205.params qh qs))))
          (HDiv.hDiv.{0, 0, 0} ↑(HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} qh qs) 3929) ↑(HPow.hPow.{0, 0, 0} 2 127)))
```

## `SLHDSA.forsRootWithSecret_eq_forsRootWith`

```lean
∀ {p : SLHDSA.Params} (core : SLHDSA.CorePrimitives p) {m : Type → Type u_1} [inst : Monad.{0, u_1} m]
  [LawfulMonad.{0, u_1} m] (hash : SLHDSA.Adrs → core.Y → m core.Y)
  (nodeHash : SLHDSA.Adrs → core.Y → core.Y → m core.Y) (sk : core.SkSeed) (pk : core.PkSeed) (adrs : SLHDSA.Adrs)
  (i : ℕ),
  Eq.{u_1 + 1}
    (SLHDSA.forsRootWithSecret.{u_1} core hash nodeHash (fun a => Pure.pure.{0, u_1} (core.PRF pk sk a)) adrs i)
    (SLHDSA.forsRootWith.{u_1} core hash nodeHash sk pk adrs i)
```

## `SLHDSA.forsPkGenWithSecret_eq_forsPkGenWith`

```lean
∀ {p : SLHDSA.Params} (core : SLHDSA.CorePrimitives p) {m : Type → Type u_1} [inst : Monad.{0, u_1} m]
  [LawfulMonad.{0, u_1} m] (hash : SLHDSA.Adrs → core.Y → m core.Y)
  (nodeHash : SLHDSA.Adrs → core.Y → core.Y → m core.Y) (compress : SLHDSA.Adrs → List.{0} core.Y → m core.Y)
  (sk : core.SkSeed) (pk : core.PkSeed) (adrs : SLHDSA.Adrs),
  Eq.{u_1 + 1}
    (SLHDSA.forsPkGenWithSecret.{u_1} core hash nodeHash compress (fun a => Pure.pure.{0, u_1} (core.PRF pk sk a)) adrs)
    (SLHDSA.forsPkGenWith.{u_1} core hash nodeHash compress sk pk adrs)
```

## `SLHDSA.forsRootWithSecret_natural`

```lean
∀ {p : SLHDSA.Params} (core : SLHDSA.CorePrimitives p) {m : Type → Type u_1} {n : Type → Type u_2}
  [inst : Monad.{0, u_1} m] [LawfulMonad.{0, u_1} m] [inst_2 : Monad.{0, u_2} n] [LawfulMonad.{0, u_2} n]
  (F : MonadHom.{0, u_1, u_2} m n) (hashm : SLHDSA.Adrs → core.Y → m core.Y) (hashn : SLHDSA.Adrs → core.Y → n core.Y)
  (nodeHashm : SLHDSA.Adrs → core.Y → core.Y → m core.Y) (nodeHashn : SLHDSA.Adrs → core.Y → core.Y → n core.Y)
  (secretm : SLHDSA.Adrs → m core.Y) (secretn : SLHDSA.Adrs → n core.Y),
  (∀ (a : SLHDSA.Adrs) (y : core.Y),
      Eq.{u_2 + 1} ((fun {α} x => NatHom.toFun.{0, u_1, u_2} (MonadHom.toNatHom.{0, u_1, u_2} F) α x) (hashm a y))
        (hashn a y)) →
    (∀ (a : SLHDSA.Adrs) (l r : core.Y),
        Eq.{u_2 + 1}
          ((fun {α} x => NatHom.toFun.{0, u_1, u_2} (MonadHom.toNatHom.{0, u_1, u_2} F) α x) (nodeHashm a l r))
          (nodeHashn a l r)) →
      (∀ (a : SLHDSA.Adrs),
          a.IsSecretKey →
            Eq.{u_2 + 1} ((fun {α} x => NatHom.toFun.{0, u_1, u_2} (MonadHom.toNatHom.{0, u_1, u_2} F) α x) (secretm a))
              (secretn a)) →
        ∀ (adrs : SLHDSA.Adrs) (i : ℕ),
          Eq.{u_2 + 1}
            ((fun {α} x => NatHom.toFun.{0, u_1, u_2} (MonadHom.toNatHom.{0, u_1, u_2} F) α x)
              (SLHDSA.forsRootWithSecret.{u_1} core hashm nodeHashm secretm adrs i))
            (SLHDSA.forsRootWithSecret.{u_2} core hashn nodeHashn secretn adrs i)
```

## `SLHDSA.forsPkGenWithSecret_natural`

```lean
∀ {p : SLHDSA.Params} (core : SLHDSA.CorePrimitives p) {m : Type → Type u_1} {n : Type → Type u_2}
  [inst : Monad.{0, u_1} m] [LawfulMonad.{0, u_1} m] [inst_2 : Monad.{0, u_2} n] [LawfulMonad.{0, u_2} n]
  (F : MonadHom.{0, u_1, u_2} m n) (hashm : SLHDSA.Adrs → core.Y → m core.Y) (hashn : SLHDSA.Adrs → core.Y → n core.Y)
  (nodeHashm : SLHDSA.Adrs → core.Y → core.Y → m core.Y) (nodeHashn : SLHDSA.Adrs → core.Y → core.Y → n core.Y)
  (compressm : SLHDSA.Adrs → List.{0} core.Y → m core.Y) (compressn : SLHDSA.Adrs → List.{0} core.Y → n core.Y)
  (secretm : SLHDSA.Adrs → m core.Y) (secretn : SLHDSA.Adrs → n core.Y),
  (∀ (a : SLHDSA.Adrs) (y : core.Y),
      Eq.{u_2 + 1} ((fun {α} x => NatHom.toFun.{0, u_1, u_2} (MonadHom.toNatHom.{0, u_1, u_2} F) α x) (hashm a y))
        (hashn a y)) →
    (∀ (a : SLHDSA.Adrs) (l r : core.Y),
        Eq.{u_2 + 1}
          ((fun {α} x => NatHom.toFun.{0, u_1, u_2} (MonadHom.toNatHom.{0, u_1, u_2} F) α x) (nodeHashm a l r))
          (nodeHashn a l r)) →
      (∀ (a : SLHDSA.Adrs) (ys : List.{0} core.Y),
          Eq.{u_2 + 1}
            ((fun {α} x => NatHom.toFun.{0, u_1, u_2} (MonadHom.toNatHom.{0, u_1, u_2} F) α x) (compressm a ys))
            (compressn a ys)) →
        (∀ (a : SLHDSA.Adrs),
            a.IsSecretKey →
              Eq.{u_2 + 1}
                ((fun {α} x => NatHom.toFun.{0, u_1, u_2} (MonadHom.toNatHom.{0, u_1, u_2} F) α x) (secretm a))
                (secretn a)) →
          ∀ (adrs : SLHDSA.Adrs),
            Eq.{u_2 + 1}
              ((fun {α} x => NatHom.toFun.{0, u_1, u_2} (MonadHom.toNatHom.{0, u_1, u_2} F) α x)
                (SLHDSA.forsPkGenWithSecret.{u_1} core hashm nodeHashm compressm secretm adrs))
              (SLHDSA.forsPkGenWithSecret.{u_2} core hashn nodeHashn compressn secretn adrs)
```

## `SLHDSA.forsSignWithSecret_eq_forsSignWith`

```lean
∀ {p : SLHDSA.Params} (core : SLHDSA.CorePrimitives p) {m : Type → Type u_1} [inst : Monad.{0, u_1} m]
  [LawfulMonad.{0, u_1} m] (hash : SLHDSA.Adrs → core.Y → m core.Y)
  (nodeHash : SLHDSA.Adrs → core.Y → core.Y → m core.Y) (md : List.{0} SLHDSA.Byte) (sk : core.SkSeed)
  (pk : core.PkSeed) (adrs : SLHDSA.Adrs),
  Eq.{u_1 + 1}
    (SLHDSA.forsSignWithSecret.{u_1} core hash nodeHash (fun a => Pure.pure.{0, u_1} (core.PRF pk sk a)) md adrs)
    (SLHDSA.forsSignWith.{u_1} core hash nodeHash md sk pk adrs)
```

## `SLHDSA.forsSignWithSecret_natural`

```lean
∀ {p : SLHDSA.Params} (core : SLHDSA.CorePrimitives p) {m : Type → Type u_1} {n : Type → Type u_2}
  [inst : Monad.{0, u_1} m] [LawfulMonad.{0, u_1} m] [inst_2 : Monad.{0, u_2} n] [LawfulMonad.{0, u_2} n]
  (F : MonadHom.{0, u_1, u_2} m n) (hashm : SLHDSA.Adrs → core.Y → m core.Y) (hashn : SLHDSA.Adrs → core.Y → n core.Y)
  (nodeHashm : SLHDSA.Adrs → core.Y → core.Y → m core.Y) (nodeHashn : SLHDSA.Adrs → core.Y → core.Y → n core.Y)
  (secretm : SLHDSA.Adrs → m core.Y) (secretn : SLHDSA.Adrs → n core.Y),
  (∀ (a : SLHDSA.Adrs) (y : core.Y),
      Eq.{u_2 + 1} ((fun {α} x => NatHom.toFun.{0, u_1, u_2} (MonadHom.toNatHom.{0, u_1, u_2} F) α x) (hashm a y))
        (hashn a y)) →
    (∀ (a : SLHDSA.Adrs) (l r : core.Y),
        Eq.{u_2 + 1}
          ((fun {α} x => NatHom.toFun.{0, u_1, u_2} (MonadHom.toNatHom.{0, u_1, u_2} F) α x) (nodeHashm a l r))
          (nodeHashn a l r)) →
      (∀ (a : SLHDSA.Adrs),
          a.IsSecretKey →
            Eq.{u_2 + 1} ((fun {α} x => NatHom.toFun.{0, u_1, u_2} (MonadHom.toNatHom.{0, u_1, u_2} F) α x) (secretm a))
              (secretn a)) →
        ∀ (md : List.{0} SLHDSA.Byte) (adrs : SLHDSA.Adrs),
          Eq.{u_2 + 1}
            ((fun {α} x => NatHom.toFun.{0, u_1, u_2} (MonadHom.toNatHom.{0, u_1, u_2} F) α x)
              (SLHDSA.forsSignWithSecret.{u_1} core hashm nodeHashm secretm md adrs))
            (SLHDSA.forsSignWithSecret.{u_2} core hashn nodeHashn secretn md adrs)
```

## `SLHDSA.forsSignWithSecretM_natural`

```lean
∀ {p : SLHDSA.Params} (core : SLHDSA.CorePrimitives p) {m : Type → Type u_1} {n : Type → Type u_2}
  [inst : Monad.{0, u_1} m] [LawfulMonad.{0, u_1} m] [inst_2 : Monad.{0, u_2} n] [LawfulMonad.{0, u_2} n]
  [inst_4 : HasQuery.{0, 0, u_1} (SLHDSA.publicHashSpec core) m]
  [inst_5 : HasQuery.{0, 0, u_2} (SLHDSA.publicHashSpec core) n]
  (F : HasQuery.QueryHom.{0, 0, u_1, u_2} (SLHDSA.publicHashSpec core) m n) (secretm : SLHDSA.Adrs → m core.Y)
  (secretn : SLHDSA.Adrs → n core.Y),
  (∀ (a : SLHDSA.Adrs),
      a.IsSecretKey →
        Eq.{u_2 + 1}
          ((fun {α} x =>
              NatHom.toFun.{0, u_1, u_2}
                (MonadHom.toNatHom.{0, u_1, u_2} (HasQuery.QueryHom.toMonadHom.{0, 0, u_1, u_2} F)) α x)
            (secretm a))
          (secretn a)) →
    ∀ (md : List.{0} SLHDSA.Byte) (pkSeed : core.PkSeed) (adrs : SLHDSA.Adrs),
      Eq.{u_2 + 1}
        ((fun {α} x =>
            NatHom.toFun.{0, u_1, u_2}
              (MonadHom.toNatHom.{0, u_1, u_2} (HasQuery.QueryHom.toMonadHom.{0, 0, u_1, u_2} F)) α x)
          (SLHDSA.forsSignWithSecretM.{u_1} core secretm md pkSeed adrs))
        (SLHDSA.forsSignWithSecretM.{u_2} core secretn md pkSeed adrs)
```

## `SLHDSA.GeneralHypertree.signWithSecretM_eq_signM`

```lean
∀ {vp : SLHDSA.ValidatedParams} (core : SLHDSA.CorePrimitives vp.params) {m : Type → Type u_1} [inst : Monad.{0, u_1} m]
  [LawfulMonad.{0, u_1} m] [inst_2 : HasQuery.{0, 0, u_1} (SLHDSA.publicHashSpec core) m] (skSeed : core.SkSeed)
  (pkSeed : core.PkSeed) (msg : core.Y) (parts : SLHDSA.DigestParts vp.params),
  Eq.{u_1 + 1}
    (SLHDSA.GeneralHypertree.signWithSecretM.{u_1} core (fun a => Pure.pure.{0, u_1} (core.PRF pkSeed skSeed a)) msg
      pkSeed parts)
    (SLHDSA.GeneralHypertree.signM.{u_1} vp core msg skSeed pkSeed parts)
```

## `SLHDSA.GeneralHypertree.rootWithSecretM_eq_rootM`

```lean
∀ {vp : SLHDSA.ValidatedParams} (core : SLHDSA.CorePrimitives vp.params) {m : Type → Type u_1} [inst : Monad.{0, u_1} m]
  [LawfulMonad.{0, u_1} m] [inst_2 : HasQuery.{0, 0, u_1} (SLHDSA.publicHashSpec core) m] (skSeed : core.SkSeed)
  (pkSeed : core.PkSeed),
  Eq.{u_1 + 1}
    (SLHDSA.GeneralHypertree.rootWithSecretM.{u_1} core (fun a => Pure.pure.{0, u_1} (core.PRF pkSeed skSeed a)) pkSeed)
    (SLHDSA.GeneralHypertree.rootM.{u_1} vp core skSeed pkSeed)
```

## `SLHDSA.GeneralHypertree.signWithSecretM_natural`

```lean
∀ {vp : SLHDSA.ValidatedParams} (core : SLHDSA.CorePrimitives vp.params) {m : Type → Type u_1} {n : Type → Type u_2}
  [inst : Monad.{0, u_1} m] [LawfulMonad.{0, u_1} m] [inst_2 : Monad.{0, u_2} n] [LawfulMonad.{0, u_2} n]
  [inst_4 : HasQuery.{0, 0, u_1} (SLHDSA.publicHashSpec core) m]
  [inst_5 : HasQuery.{0, 0, u_2} (SLHDSA.publicHashSpec core) n]
  (F : HasQuery.QueryHom.{0, 0, u_1, u_2} (SLHDSA.publicHashSpec core) m n) (secretm : SLHDSA.Adrs → m core.Y)
  (secretn : SLHDSA.Adrs → n core.Y),
  (∀ (a : SLHDSA.Adrs),
      a.IsSecretKey →
        Eq.{u_2 + 1}
          ((fun {α} x =>
              NatHom.toFun.{0, u_1, u_2}
                (MonadHom.toNatHom.{0, u_1, u_2} (HasQuery.QueryHom.toMonadHom.{0, 0, u_1, u_2} F)) α x)
            (secretm a))
          (secretn a)) →
    ∀ (msg : core.Y) (pkSeed : core.PkSeed) (parts : SLHDSA.DigestParts vp.params),
      Eq.{u_2 + 1}
        ((fun {α} x =>
            NatHom.toFun.{0, u_1, u_2}
              (MonadHom.toNatHom.{0, u_1, u_2} (HasQuery.QueryHom.toMonadHom.{0, 0, u_1, u_2} F)) α x)
          (SLHDSA.GeneralHypertree.signWithSecretM.{u_1} core secretm msg pkSeed parts))
        (SLHDSA.GeneralHypertree.signWithSecretM.{u_2} core secretn msg pkSeed parts)
```

## `SLHDSA.GeneralHypertree.rootWithSecretM_natural`

```lean
∀ {vp : SLHDSA.ValidatedParams} (core : SLHDSA.CorePrimitives vp.params) {m : Type → Type u_1} {n : Type → Type u_2}
  [inst : Monad.{0, u_1} m] [LawfulMonad.{0, u_1} m] [inst_2 : Monad.{0, u_2} n] [LawfulMonad.{0, u_2} n]
  [inst_4 : HasQuery.{0, 0, u_1} (SLHDSA.publicHashSpec core) m]
  [inst_5 : HasQuery.{0, 0, u_2} (SLHDSA.publicHashSpec core) n]
  (F : HasQuery.QueryHom.{0, 0, u_1, u_2} (SLHDSA.publicHashSpec core) m n) (secretm : SLHDSA.Adrs → m core.Y)
  (secretn : SLHDSA.Adrs → n core.Y),
  (∀ (a : SLHDSA.Adrs),
      a.IsSecretKey →
        Eq.{u_2 + 1}
          ((fun {α} x =>
              NatHom.toFun.{0, u_1, u_2}
                (MonadHom.toNatHom.{0, u_1, u_2} (HasQuery.QueryHom.toMonadHom.{0, 0, u_1, u_2} F)) α x)
            (secretm a))
          (secretn a)) →
    ∀ (pkSeed : core.PkSeed),
      Eq.{u_2 + 1}
        ((fun {α} x =>
            NatHom.toFun.{0, u_1, u_2}
              (MonadHom.toNatHom.{0, u_1, u_2} (HasQuery.QueryHom.toMonadHom.{0, 0, u_1, u_2} F)) α x)
          (SLHDSA.GeneralHypertree.rootWithSecretM.{u_1} core secretm pkSeed))
        (SLHDSA.GeneralHypertree.rootWithSecretM.{u_2} core secretn pkSeed)
```

## `SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_eq_signInternalWithRandomizerM`

```lean
∀ {vp : SLHDSA.ValidatedParams} (core : SLHDSA.CorePrimitives vp.params) {m : Type → Type u_1} [inst : Monad.{0, u_1} m]
  [LawfulMonad.{0, u_1} m] [inst_2 : HasQuery.{0, 0, u_1} (SLHDSA.publicHashSpec core) m] (skSeed : core.SkSeed)
  (pkSeed : core.PkSeed) (msg : List.{0} SLHDSA.Byte) (pkRoot R : core.Y),
  Eq.{u_1 + 1}
    (SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM.{u_1} core
      (fun a => Pure.pure.{0, u_1} (core.PRF pkSeed skSeed a)) msg pkSeed pkRoot R)
    (SLHDSA.GeneralScheme.signInternalWithRandomizerM.{u_1} vp core msg skSeed pkSeed pkRoot R)
```

## `SLHDSA.GeneralScheme.keygenInternalWithSecretM_natural`

```lean
∀ {vp : SLHDSA.ValidatedParams} (core : SLHDSA.CorePrimitives vp.params) {m : Type → Type u_1} {n : Type → Type u_2}
  [inst : Monad.{0, u_1} m] [LawfulMonad.{0, u_1} m] [inst_2 : Monad.{0, u_2} n] [LawfulMonad.{0, u_2} n]
  [inst_4 : HasQuery.{0, 0, u_1} (SLHDSA.publicHashSpec core) m]
  [inst_5 : HasQuery.{0, 0, u_2} (SLHDSA.publicHashSpec core) n]
  (F : HasQuery.QueryHom.{0, 0, u_1, u_2} (SLHDSA.publicHashSpec core) m n) (secretm : SLHDSA.Adrs → m core.Y)
  (secretn : SLHDSA.Adrs → n core.Y),
  (∀ (a : SLHDSA.Adrs),
      a.IsSecretKey →
        Eq.{u_2 + 1}
          ((fun {α} x =>
              NatHom.toFun.{0, u_1, u_2}
                (MonadHom.toNatHom.{0, u_1, u_2} (HasQuery.QueryHom.toMonadHom.{0, 0, u_1, u_2} F)) α x)
            (secretm a))
          (secretn a)) →
    ∀ (pkSeed : core.PkSeed),
      Eq.{u_2 + 1}
        ((fun {α} x =>
            NatHom.toFun.{0, u_1, u_2}
              (MonadHom.toNatHom.{0, u_1, u_2} (HasQuery.QueryHom.toMonadHom.{0, 0, u_1, u_2} F)) α x)
          (SLHDSA.GeneralScheme.keygenInternalWithSecretM.{u_1} core secretm pkSeed))
        (SLHDSA.GeneralScheme.keygenInternalWithSecretM.{u_2} core secretn pkSeed)
```

## `SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM_natural`

```lean
∀ {vp : SLHDSA.ValidatedParams} (core : SLHDSA.CorePrimitives vp.params) {m : Type → Type u_1} {n : Type → Type u_2}
  [inst : Monad.{0, u_1} m] [LawfulMonad.{0, u_1} m] [inst_2 : Monad.{0, u_2} n] [LawfulMonad.{0, u_2} n]
  [inst_4 : HasQuery.{0, 0, u_1} (SLHDSA.publicHashSpec core) m]
  [inst_5 : HasQuery.{0, 0, u_2} (SLHDSA.publicHashSpec core) n]
  (F : HasQuery.QueryHom.{0, 0, u_1, u_2} (SLHDSA.publicHashSpec core) m n) (secretm : SLHDSA.Adrs → m core.Y)
  (secretn : SLHDSA.Adrs → n core.Y),
  (∀ (a : SLHDSA.Adrs),
      a.IsSecretKey →
        Eq.{u_2 + 1}
          ((fun {α} x =>
              NatHom.toFun.{0, u_1, u_2}
                (MonadHom.toNatHom.{0, u_1, u_2} (HasQuery.QueryHom.toMonadHom.{0, 0, u_1, u_2} F)) α x)
            (secretm a))
          (secretn a)) →
    ∀ (msg : List.{0} SLHDSA.Byte) (pkSeed : core.PkSeed) (pkRoot R : core.Y),
      Eq.{u_2 + 1}
        ((fun {α} x =>
            NatHom.toFun.{0, u_1, u_2}
              (MonadHom.toNatHom.{0, u_1, u_2} (HasQuery.QueryHom.toMonadHom.{0, 0, u_1, u_2} F)) α x)
          (SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM.{u_1} core secretm msg pkSeed pkRoot R))
        (SLHDSA.GeneralScheme.signInternalWithSecretRandomizerM.{u_2} core secretn msg pkSeed pkRoot R)
```

## `SignatureAlg.RomWorkBounds`

```lean
{ι : Type} →
  {hs : OracleSpec.{0, 0} ι} →
    {M PK SK S : Type} →
      SignatureAlg.{0} (OracleComp.{0, 0, 0} (HAdd.hAdd.{1, 1, 1} unifSpec hs)) M PK SK S → ℕ → ℕ → ℕ → Prop
```

## `SignatureAlg.isQueryBoundP_runWithSigningOracle`

```lean
∀ {ι : Type} {hs : OracleSpec.{0, 0} ι} {M PK SK S : Type}
  (alg : SignatureAlg.{0} (OracleComp.{0, 0, 0} (HAdd.hAdd.{1, 1, 1} unifSpec hs)) M PK SK S) (key : PK) (sk : SK)
  {α : Type}
  (oa :
    OracleComp.{0, 0, 0} (HAdd.hAdd.{1, 1, 1} (HAdd.hAdd.{1, 1, 1} unifSpec hs) (OracleSpec.ofFn.{0, 0} fun x => S)) α)
  {qh qs sign : ℕ},
  OracleComp.IsQueryBoundP.{0} oa SignatureAlg.IsHashQuery qh →
    OracleComp.IsQueryBoundP.{0} oa SignatureAlg.IsSignQuery qs →
      (∀ (msg : M),
          OracleComp.IsQueryBoundP.{0} (SignatureAlg.sign.{0} alg key sk msg) SignatureAlg.IsAmbientHashQuery sign) →
        OracleComp.IsQueryBoundP.{0} (SignatureAlg.runWithSigningOracle.{0} alg key sk oa)
          SignatureAlg.IsAmbientHashQuery (HAdd.hAdd.{0, 0, 0} qh (HMul.hMul.{0, 0, 0} qs sign))
```

## `SignatureAlg.isQueryBoundP_strongUnforgeableExperiment`

```lean
∀ {ι : Type} {hs : OracleSpec.{0, 0} ι} {M PK SK S : Type}
  (alg : SignatureAlg.{0} (OracleComp.{0, 0, 0} (HAdd.hAdd.{1, 1, 1} unifSpec hs)) M PK SK S)
  (adv : SignatureAlg.StrongUnforgeableAdversary.{0} alg) {qh qs keygen sign verify : ℕ},
  adv.RomQueryBound qh qs →
    alg.RomWorkBounds keygen sign verify →
      OracleComp.IsQueryBoundP.{0} (SignatureAlg.strongUnforgeableExperiment.{0} adv) SignatureAlg.IsAmbientHashQuery
        (HAdd.hAdd.{0, 0, 0} (HAdd.hAdd.{0, 0, 0} keygen (HAdd.hAdd.{0, 0, 0} qh (HMul.hMul.{0, 0, 0} qs sign))) verify)
```

## `SLHDSA.GeneralScheme.verifyInternalQueryBound`

```lean
SLHDSA.Params → ℕ
```

## `SLHDSA.GeneralScheme.verifyInternalM_isTotalQueryBound`

```lean
∀ (vp : SLHDSA.ValidatedParams) (core : SLHDSA.CorePrimitives vp.params) [inst : DecidableEq.{1} core.Y]
  (msg : List.{0} SLHDSA.Byte) (sig : SLHDSA.GeneralScheme.SignatureCore vp core) (pk : SLHDSA.PublicKeyCore core),
  OracleComp.IsTotalQueryBound.{0} (SLHDSA.GeneralScheme.verifyInternalM.{0} vp core msg sig pk)
    (SLHDSA.GeneralScheme.verifyInternalQueryBound vp.params)
```

## `SLHDSA.Security.rationalValue_averagedByteBoundEval`

```lean
∀ (vp : SLHDSA.ValidatedParams) (qh qs : ℕ),
  Eq.{1} (KeyedHash.Covering.rationalValue (SLHDSA.Security.averagedByteBoundEval vp.params qh qs))
    (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBound vp qh qs)
      (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (↑(SLHDSA.Security.honestAdrsCount vp)) (HPow.hPow.{0, 0, 0} 2 256))
        (SLHDSA.Security.weakSeedFactor vp (SLHDSA.Security.everySeedBound vp qh qs))))
```

## `SLHDSA.Security.rationalValue_averagedByteBoundHedgedEval`

```lean
∀ (vp : SLHDSA.ValidatedParams) (qh qs : ℕ),
  Eq.{1} (KeyedHash.Covering.rationalValue (SLHDSA.Security.averagedByteBoundHedgedEval vp.params qh qs))
    (HAdd.hAdd.{0, 0, 0} (SLHDSA.Security.byteBoundHedged vp qh qs)
      (HMul.hMul.{0, 0, 0} (HDiv.hDiv.{0, 0, 0} (↑(SLHDSA.Security.honestAdrsCount vp)) (HPow.hPow.{0, 0, 0} 2 256))
        (SLHDSA.Security.weakSeedFactor vp (SLHDSA.Security.everySeedBoundHedged vp qh qs))))
```

## `SLHDSA.Security.boundTable_certified`

```lean
∀ (entry : Prod.{0, 0} SLHDSA.FipsParameterSet (Prod.{0, 0} ℕ (Prod.{0, 0} ℕ ℕ))),
  Membership.mem.{0, 0} SLHDSA.Security.boundTable entry →
    have p := entry.1.validatedParams.params;
    have q := HPow.hPow.{0, 0, 0} 2 64;
    SLHDSA.Security.RoundedCoefficient
        (HDiv.hDiv.{0, 0, 0} (SLHDSA.Security.securityBoundEval p (HPow.hPow.{0, 0, 0} 256 p.n) 2 1 q q) ↑q) entry.2.1 ∧
      SLHDSA.Security.RoundedCoefficient (HDiv.hDiv.{0, 0, 0} (SLHDSA.Security.averagedByteBoundEval p q q) ↑q)
          entry.2.2.1 ∧
        SLHDSA.Security.RoundedCoefficient (HDiv.hDiv.{0, 0, 0} (SLHDSA.Security.averagedByteBoundHedgedEval p q q) ↑q)
          entry.2.2.2
```

## `SLHDSA.Security.rangeCoefficients_certified`

```lean
∀ (entry : Prod.{0, 0} SLHDSA.FipsParameterSet (Prod.{0, 0} ℕ (Prod.{0, 0} ℕ ℕ))),
  Membership.mem.{0, 0} SLHDSA.Security.boundTable entry →
    ∀ (lifetime : ℕ),
      Membership.mem.{0, 0}
          (List.cons.{0} (HPow.hPow.{0, 0, 0} 2 20)
            (List.cons.{0} (HPow.hPow.{0, 0, 0} 2 32) (List.cons.{0} (HPow.hPow.{0, 0, 0} 2 64) List.nil.{0})))
          lifetime →
        have p := entry.1.validatedParams.params;
        LE.le.{0}
          (SLHDSA.Security.securityCoefficientEval p (HPow.hPow.{0, 0, 0} 256 p.n) (HPow.hPow.{0, 0, 0} 2 32)
            (HPow.hPow.{0, 0, 0} 2 64) lifetime)
          (HDiv.hDiv.{0, 0, 0} 1 (HPow.hPow.{0, 0, 0} 2 (HSub.hSub.{0, 0, 0} (HMul.hMul.{0, 0, 0} 8 p.n) 2)))
```

## `SLHDSA.SHAKE128s.WorkFinal.advantage_eq_zero`

```lean
∀ (adversary : SLHDSA.SHAKE128s.Security.Adversary) (q : ℕ),
  LT.lt.{0} q 569 →
    SLHDSA.SHAKE128s.Security.securityGame.HasQueryBound () SLHDSA.SHAKE128s.Security.adversaryWork adversary q →
      Eq.{1} (SLHDSA.SHAKE128s.Security.securityGame.advantage () adversary) 0
```

## `SLHDSA.SHAKE128s.VerificationBudget.verification_count_bounds`

```lean
∀ (pk : SLHDSA.SHAKE128s.PublicKey) (request : SLHDSA.SHAKE128s.Message) (wire message : SLHDSA.SHAKE128s.Bytes)
  (signature : SLHDSA.SHAKE128s.Signature),
  Eq.{1} request.frame (Option.some.{0} message) →
    Eq.{1} (SLHDSA.SHAKE128s.Signature.fromBytes? wire) (Option.some.{0} signature) →
      ∀ (cache : OracleSpec.QueryCache.{0, 0} SLHDSA.SHAKE128s.HashSpec)
        (result : Prod.{0, 0} Bool SLHDSA.SHAKE128s.Game.Counts),
        Membership.mem.{0, 0}
            (MonadAttach.support.{0, 0}
              (StateT.run'.{0, 0}
                (simulateQ.{0, 0, 0}
                  (SLHDSA.SHAKE128s.RandomOracleModel.impl SLHDSA.SHAKE128s.Bytes SLHDSA.SHAKE128s.HashOutput)
                  (SLHDSA.SHAKE128s.Security.countQueries SLHDSA.SHAKE128s.VerificationBudget.verificationCost
                    (SLHDSA.SHAKE128s.Scheme.verify pk request wire)))
                cache))
            result →
          LE.le.{0} 569 (result.2 SLHDSA.SHAKE128s.Game.QueryKind.verification) ∧
            LE.le.{0} (result.2 SLHDSA.SHAKE128s.Game.QueryKind.verification) 3824
```

## `SLHDSA.SHAKE128s.VerificationBudget.verification_accepted_count_bounds`

```lean
∀ (pk : SLHDSA.SHAKE128s.PublicKey) (request : SLHDSA.SHAKE128s.Message) (wire : SLHDSA.SHAKE128s.Bytes)
  (cache : OracleSpec.QueryCache.{0, 0} SLHDSA.SHAKE128s.HashSpec)
  (result : Prod.{0, 0} Bool SLHDSA.SHAKE128s.Game.Counts),
  Membership.mem.{0, 0}
      (MonadAttach.support.{0, 0}
        (StateT.run'.{0, 0}
          (simulateQ.{0, 0, 0}
            (SLHDSA.SHAKE128s.RandomOracleModel.impl SLHDSA.SHAKE128s.Bytes SLHDSA.SHAKE128s.HashOutput)
            (SLHDSA.SHAKE128s.Security.countQueries SLHDSA.SHAKE128s.VerificationBudget.verificationCost
              (SLHDSA.SHAKE128s.Scheme.verify pk request wire)))
          cache))
      result →
    Eq.{1} result.1 Bool.true →
      LE.le.{0} 569 (result.2 SLHDSA.SHAKE128s.Game.QueryKind.verification) ∧
        LE.le.{0} (result.2 SLHDSA.SHAKE128s.Game.QueryKind.verification) 3824
```

## `SLHDSA.SHAKE128s.VerificationBudget.accepted_outcome_work`

```lean
∀ (adversary : SLHDSA.SHAKE128s.Security.Adversary) (outcome : SLHDSA.SHAKE128s.Security.Outcome),
  Membership.mem.{0, 0} (MonadAttach.support.{0, 0} (SLHDSA.SHAKE128s.Security.run adversary)) outcome →
    Eq.{1} outcome.verified Bool.true → LE.le.{0} 569 outcome.counts.work
```
