/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import LatticeCrypto.MLDSA.Scheme
public import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security
public import LatticeCrypto.HardnessAssumptions.ShortIntegerSolution
public import LatticeCrypto.HardnessAssumptions.LearningWithErrors

/-!
# ML-DSA Security

This file proves completeness and commitment recoverability of the ML-DSA identification scheme
and defines the ML-DSA CMA-to-NMA loss `cmaToNmaLoss`, following the CRYPTO 2023 paper
"Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium" (Barbosa
et al., ePrint 2023/246). The ML-DSA hardness problems are defined in
`LatticeCrypto.MLDSA.SecurityNMA`, and the composed security theorems are in
`LatticeCrypto.MLDSA.SecurityHeadlines`.

The target result (Theorem 4) is that the ML-DSA signature scheme is EUF-CMA secure, reducing
to two computational assumptions plus a statistical loss from the CMA-to-NMA reduction:

  `Adv^{EUF-CMA}_{ML-DSA}(A) ≤ Adv^{MLWE}_{k,l,Sη}(B) + Adv^{SelfTargetMSIS}_{G,k,l+1,ζ}(C) + L`

The two computational assumptions are:

1. **MLWE** (Module Learning With Errors): `(A, As₁ + s₂)` is computationally indistinguishable
   from `(A, uniform)` (Definition 3).
2. **SelfTargetMSIS** (Self-Target Module-SIS): given `A` and a random oracle `H`, it is hard
   to find a short vector satisfying a self-referential hash equation (Definition 4).

For the FIPS-204 signature format, which recovers the commitment at verification, the target
statistical loss is `cmaToNmaLoss`:

  `L = 2·qS·(qH + qS + 1)·ε/(1-p) + qS·ε·(qS+1)/(2·(1-p)²) + qS·ζ_zk/(1-p) + δ`

This is `FiatShamirWithAbort.cmaToNmaLoss` for a per-attempt HVZK simulator
(`IdenSchemeWithAbort.HVZK`) at the hash budget `qH + qS`. The `1/(1-p)` factor on the `qS·ζ_zk`
term comes from gluing that simulator across the restart loop; with a simulator for the
accepted-transcript distribution (the paper's acHVZK notion) the term is `qS·ζ_zk`, as in the
paper's Theorem 4.

The argument has two steps:
1. EUF-CMA → EUF-NMA via the Fiat-Shamir with aborts CMA-to-NMA reduction (Theorem 3),
   plus `qS` extra random-oracle queries to convert standard `(w₁, z, h)` signatures into
   commitment-recoverable `(c̃, z, h)` signatures for ML-DSA.
2. EUF-NMA → MLWE + SelfTargetMSIS (Lemma 7).

The theorems in `LatticeCrypto.MLDSA.SecurityHeadlines` formalize both steps for the
commitment-carrying signature `(w₁, z, h)`, at the loss `FiatShamirWithAbort.cmaToNmaLoss qS qH`
and with additional bridge and key-generation slack terms. The commitment-recovery conversion of
step 1, which moves the hash budget from `qH` to `qH + qS`, is not formalized. The larger gap to
the FIPS-204 statement is in the scheme itself: `identificationScheme` samples the mask from all
of `R_q^l` rather than from the `γ₁` box of FIPS 204, and this departure makes every composed
EUF-CMA bound trivial at the FIPS 204 parameter sets (see the Limitations section of
`LatticeCrypto.MLDSA.SecurityHeadlines`).

## References

- Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium
  (CRYPTO 2023, ePrint 2023/246), Theorems 3, 4 and Lemma 7, Definitions 3, 4
- NIST FIPS 204, Section 3.2 (security properties)
- EasyCrypt `FSabort.eca`, `HVZK_FSa.ec`, `SimplifiedScheme.ec` (formosa-crypto/dilithium)
-/

@[expose] public section


open OracleComp OracleSpec ENNReal
open LatticeCrypto TransformOps

namespace MLDSA

variable (p : Params) (prims : Primitives p)

section Properties

/-! ### Componentwise algebra on `Rq` -/

private lemma neg_rq_get (f : Rq) (i : Fin ringDegree) : (-f).get i = -(f.get i) := by
  change (coeffRing.neg f).get i = _
  simp

private lemma polyNorm_neg (f : Rq) : polyNorm (-f) = polyNorm f := by
  unfold polyNorm normOps
  simp only [LatticeCrypto.zmodPolyNormOps, LatticeCrypto.normOpsOfCenteredView]
  unfold LatticeCrypto.cInfNormOf
  apply Finset.sup_congr rfl
  intro i _
  simp only [LatticeCrypto.zmodCenteredCoeffView, coeffRing.coeff_neg]
  exact LatticeCrypto.centeredRepr_natAbs_neg _

variable [nttOps : NTTRingOps]

/-! ### Hint recovery -/

/-- Vector form of `useHint_makeHint`: `UseHint(MakeHint(z, r), r) = HighBits(r + z)`
componentwise, when each component of `z` is bounded by `γ₂`. -/
theorem useHintVec_makeHintVec (h_laws : Primitives.Laws prims nttOps) {k : ℕ}
    (z r : RqVec k) (hz : ∀ j : Fin k, polyNorm (z.get j) ≤ p.gamma2) :
    prims.useHintVec (prims.makeHintVec z r) r = prims.highBitsVec (r + z) := by
  apply Vector.ext; intro i hi
  simp only [Primitives.useHintVec, Primitives.makeHintVec, Primitives.highBitsVec,
    Vector.getElem_zipWith, Vector.getElem_map, Vector.getElem_add]
  have hzi := hz ⟨i, hi⟩
  rw [Vector.get_eq_getElem] at hzi
  exact h_laws.useHint_makeHint z[i] r[i] hzi

/-- Vector form of `hide_low`: a small additive perturbation does not change the high bits. -/
theorem hide_lowVec (h_laws : Primitives.Laws prims nttOps) {k : ℕ}
    (r s : RqVec k) (b : ℕ)
    (hs : ∀ j : Fin k, polyNorm (s.get j) ≤ b)
    (hr : ∀ j : Fin k, polyNorm (prims.lowBits (r.get j)) + b < p.gamma2) :
    prims.highBitsVec (r + s) = prims.highBitsVec r := by
  apply Vector.ext; intro i hi
  simp only [Primitives.highBitsVec, Vector.getElem_map, Vector.getElem_add]
  have hsi := hs ⟨i, hi⟩
  have hri := hr ⟨i, hi⟩
  rw [Vector.get_eq_getElem] at hsi hri
  exact h_laws.hide_low r[i] s[i] b hsi hri

variable [DecidableEq prims.High]

/-- Commitment recoverability for ML-DSA: the public commitment `w₁` can be reconstructed
from `(pk, c̃, (z, h))` alone using `UseHint(h, Az - ct₁·2^d)`. This is the key property
enabling the CMA-to-NMA reduction in the security proof.

In our formalization, this is directly enforced by the `verify` function: it checks
`UseHint(h, w'_Approx) = w₁`, so any accepted transcript necessarily satisfies
commitment recoverability. -/
theorem idsWithAbort_commitment_recoverable :
    ∃ recover, (identificationScheme p prims).CommitmentRecoverable recover := by
  classical
  refine ⟨fun pk cTilde (z, h) =>
    prims.useHintVec h (computeWApprox p prims (prims.expandA pk.rho)
      (prims.sampleInBall cTilde) z pk.t1), ?_⟩
  rintro s w' c ⟨z, h⟩ hverify
  unfold identificationScheme at hverify
  grind

/-! ### Completeness -/

variable [SampleableType (CommitHashBytes p)]

section conditional

-- The algebraic core of completeness: whenever `respond` produces `some (z, h)`, the
-- `verify` function accepts. This follows from the key generation relationship
-- `A·s₁ + s₂ = t₁·2^d + t₀`, the correctness of `MakeHint`/`UseHint`, and the rounding
-- norm bounds. We isolate it as a hypothesis since the full algebraic derivation requires
-- NTT linearity and primitives laws.
variable
  (hRespondVerify : ∀ (pk : PublicKey p prims) (sk : SecretKey p),
    validKeyPair p prims pk sk = true →
    ∀ (w1 : Commitment p prims) (st : SigningState p) (cTilde : CommitHashBytes p),
    (w1, st) ∈ support ((identificationScheme p prims).commit pk sk) →
    ∀ (zh : Response p prims),
    some zh ∈ support ((identificationScheme p prims).respond pk sk st cTilde) →
    (identificationScheme p prims).verify pk w1 cTilde zh = true)

include hRespondVerify
/-- Completeness of the ML-DSA identification scheme, conditional on `hRespondVerify`:
whenever `respond` returns `some (z, h)`, `verify` accepts. This algebraic fact follows
from the key generation identity, NTT linearity, and `Primitives.Laws`, but is isolated
here to separate the probabilistic argument from the algebraic one. -/
theorem idsWithAbort_complete' :
    (identificationScheme p prims).Complete := by
  classical
  intro pk sk hvalid
  refine (OracleComp.prEvent_eq_one_iff _ (· = true)).2 fun b hb => ?_
  rw [support_bind] at hb
  simp only [Set.mem_iUnion] at hb
  obtain ⟨t?, ht?, hb⟩ := hb
  rw [support_pure] at hb
  simp only [Set.mem_singleton_iff] at hb
  subst hb
  match t? with
  | none => rfl
  | some (w1, cTilde, zh) =>
    simp only [IdenSchemeWithAbort.honestExecution, support_bind, Set.mem_iUnion,
      support_pure, Set.mem_singleton_iff] at ht?
    obtain ⟨⟨w1', st⟩, hw1st, cTilde', hcTilde, oz, hoz, heq⟩ := ht?
    cases oz with
    | none => simp only [Option.map, reduceCtorEq] at heq
    | some zh' =>
      simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact hRespondVerify pk sk hvalid w1 st cTilde hw1st _ hoz

end conditional

/-- The ML-DSA identification scheme is complete: whenever the honest prover does not abort,
the verifier always accepts. This follows from the correctness of the rounding operations
and the norm bounds satisfied by honest responses.

The proof requires deriving the `hRespondVerify` algebraic fact from `Primitives.Laws`;
see `idsWithAbort_complete'` for the conditional version. -/
theorem idsWithAbort_complete (h_laws : Primitives.Laws prims nttOps) :
    (identificationScheme p prims).Complete := by
  classical
  refine idsWithAbort_complete' p prims ?_
  intro pk sk hvalid w1 st cTilde hw1st zh hzh
  obtain ⟨seed, hkeygen⟩ := (validKeyPair_eq_true_iff p prims pk sk).mp hvalid
  simp only [identificationScheme, support_bind, support_pure, Set.mem_iUnion,
    Set.mem_singleton_iff, Prod.mk.injEq] at hw1st
  simp only [identificationScheme] at hzh
  obtain ⟨y, -, hw1, hst⟩ := hw1st
  subst hst hw1
  split_ifs at hzh with hc1 hc2
  · rw [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hzh
    subst hzh
    dsimp only at hc1 hc2 ⊢
    obtain ⟨hz_norm, hr0_norm⟩ := hc1
    obtain ⟨hct0_norm, hweight⟩ := hc2
    -- Honest secret vectors are `η`-bounded, so the challenge product is `β`-bounded.
    have hs2_bound : polyVecBounded sk.s2 p.eta := by
      have h := congrArg Prod.snd hkeygen
      simp only [keyGenFromSeed] at h
      rw [← h]
      exact (h_laws.expandS_bound _).2
    have hcs2_norm : polyVecNorm (prims.sampleInBall cTilde • sk.s2) ≤ p.beta :=
      h_laws.sampleInBall_smul_bound cTilde sk.s2 hs2_bound
    -- Abbreviations matching the goal.
    set c := prims.sampleInBall cTilde with hc_def
    set aHat := prims.expandA pk.rho with haHat_def
    -- The challenge-times-`t₀` hint argument is `γ₂`-bounded (after negation).
    have hcond_t0 : ∀ j : Fin p.k, polyNorm ((-(c • sk.t0)).get j) ≤ p.gamma2 := by
      intro j
      rw [Vector.get_eq_getElem, Vector.getElem_neg, polyNorm_neg]
      exact le_of_lt (lt_of_le_of_lt
        (LatticeCrypto.PolyVec.component_cInfNorm_le normOps (c • sk.t0) j) hct0_norm)
    -- Vector cancellations.
    have harith1 : aHat * y - c • sk.s2 + c • sk.t0 + -(c • sk.t0) = aHat * y - c • sk.s2 := by
      apply Vector.ext; intro i hi
      simp only [Vector.getElem_add, Vector.getElem_sub, Vector.getElem_neg]; abel
    have harith2 : aHat * y - c • sk.s2 + c • sk.s2 = aHat * y := by
      apply Vector.ext; intro i hi
      simp only [Vector.getElem_add, Vector.getElem_sub]; abel
    -- The high bits are unchanged by subtracting `c·s₂`.
    have hhide : prims.highBitsVec (aHat * y - c • sk.s2) = prims.highBitsVec (aHat * y) := by
      have h := hide_lowVec p prims h_laws (aHat * y - c • sk.s2) (c • sk.s2) p.beta
        (fun j => le_trans
          (LatticeCrypto.PolyVec.component_cInfNorm_le normOps (c • sk.s2) j) hcs2_norm)
        (fun j => by
          have hj := lt_of_le_of_lt
            (LatticeCrypto.PolyVec.component_cInfNorm_le normOps
              (prims.lowBitsVec (aHat * y - c • sk.s2)) j) hr0_norm
          simp only [Primitives.lowBitsVec, Vector.get_eq_getElem, Vector.getElem_map,
            polyNorm] at hj ⊢
          omega)
      rw [harith2] at h
      exact h.symm
    -- The key-generation identity for `wApprox`.
    have hwa := keyGenFromSeed_wApprox_eq p prims h_laws seed hkeygen c y
    -- Discharge `verify`.
    simp only [identificationScheme, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hz_norm, ?_⟩, hweight⟩
    rw [hwa, useHintVec_makeHintVec p prims h_laws (-(c • sk.t0))
        (aHat * y - c • sk.s2 + c • sk.t0) hcond_t0, harith1, hhide]
  all_goals (rw [support_pure, Set.mem_singleton_iff] at hzh; exact absurd hzh (by simp))

/-! ### Honest-Verifier Zero-Knowledge

The HVZK theorem `MLDSA.idsWithAbort_hvzk` is proven downstream in
`LatticeCrypto.MLDSA.SecurityHVZK`, where the concrete simulator `hvzkSimulatorReal` and the
extra-rejection-mass bound `hvzkBound` are defined. The simulator reproduces the honest
transcript pointwise on the accept event, so the total-variation distance is bounded by the
honest prover's extra-rejection mass; see that file for the quantitative statement. -/

end Properties

/-! ### EUF-NMA Security (Lemma 7)

The EUF-NMA reduction infrastructure — the concrete MLWE key-swap distinguisher and the
SelfTargetMSIS extractor — is assembled downstream in `LatticeCrypto.MLDSA.SecurityNMA`, together
with the SelfTargetMSIS extraction bound; see that file for the definitions and proofs. -/

/-! ### CMA-to-NMA Statistical Loss (Theorem 4) -/

section CMAtoNMA

/-- The ML-DSA-specific classical ROM loss for the commitment-recoverable signature format.

The abstract Fiat-Shamir-with-aborts reduction applies to the standard signature format where
the commitment `w₁` is part of the signature, giving the loss
`FiatShamirWithAbort.cmaToNmaLoss qS qH ...`.
ML-DSA instead publishes the compressed signature `(c̃, z, h)`, and the paper's
reduction converts each signing-oracle answer back into a standard signature via
one extra random-oracle query. Across `qS` signing queries this adds `qS` to the
effective random-oracle budget, yielding:

  `L = 2·qS·(qH + qS + 1)·ε/(1-p)
     + qS·ε·(qS+1)/(2·(1-p)²)
     + qS·ζ_zk/(1-p)
     + δ`

This is exactly `FiatShamirWithAbort.cmaToNmaLoss qS (qH + qS) ...`. It is the target loss of
the end-to-end FIPS-204 statement; the composed theorems of
`LatticeCrypto.MLDSA.SecurityHeadlines` cover the commitment-carrying format at the smaller
budget `qH`. -/
noncomputable def cmaToNmaLoss
    (qS qH : ℕ) (ε p_abort ζ_zk δ : ℝ) (hp : p_abort < 1) : ℝ :=
  FiatShamirWithAbort.cmaToNmaLoss qS (qH + qS) ε p_abort ζ_zk δ hp

end CMAtoNMA

/-! ### Main Security Theorem (Theorem 4)

The EUF-CMA security theorems for ML-DSA are assembled downstream in
`LatticeCrypto.MLDSA.SecurityHeadlines`. Each composes the Fiat-Shamir-with-aborts CMA-to-NMA
reduction with an EUF-NMA bound, for the commitment-carrying signature and at the loss
`FiatShamirWithAbort.cmaToNmaLoss qS qH`; the commitment-recovery bridge to the FIPS-204
signature format, at the loss `cmaToNmaLoss` above, is not formalized.

- `MLDSA.euf_cma_security_of_nma_fips`: seed-derived key generation, with the EUF-NMA leg
  `MLDSA.nma_security_fips`. `MLDSA.euf_cma_security_of_nma_fips_hvzkReal` discharges its HVZK
  hypothesis with the simulator `hvzkSimulatorReal`, proved HVZK at the bound `hvzkBound` by
  `idsWithAbort_hvzk` under `Primitives.Laws`.
- `MLDSA.euf_cma_security_of_nma_short`: the short-secret model, with the EUF-NMA leg
  `MLDSA.nma_security_short`.

Both take nonnegativity side conditions on the statistical-loss parameters, so the loss cannot
be clamped to `0` by `ENNReal.ofReal`.

None of the three is quantitative at the FIPS 204 parameter sets:

- All three are trivial once `qS ≥ 1`, whatever the simulator and `ζ_zk`. The commitment step of
  `identificationScheme` draws the mask from all of `R_q^l` rather than from the `γ₁` box, so the
  acceptance probability `1 - p_abort` is at most `((2(γ₁ - β) - 1)/q)^(256l)` and the
  commitment-collision term of the loss exceeds `1`.
- The two seed-model theorems are also non-quantitative through `expandSReplacement`, which
  forces `εPRG ≥ 1 - 2^-256` against distinguishers with no cost bound.
- Separately, the HVZK hypothesis of the short-model theorem has no known witness below
  `ζ_zk = 1`.

The Limitations section of `LatticeCrypto.MLDSA.SecurityHeadlines` gives the exact bounds. -/

end MLDSA
