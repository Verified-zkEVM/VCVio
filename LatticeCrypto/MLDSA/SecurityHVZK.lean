/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import LatticeCrypto.MLDSA.Security
public import VCVio.CryptoFoundations.FiatShamir.WithAbort

/-!
# ML-DSA Honest-Verifier Zero-Knowledge

This file proves that the ML-DSA identification scheme with `t₀` in the statement,
`identificationSchemeFull`, is perfectly honest-verifier zero-knowledge for a named simulator,
`hvzkSimulator` (`MLDSA.identificationSchemeFull_perfectHVZK`). An existential statement asserting
only that *some* simulator with *some* error exists would be trivially dischargeable with
`ζ_zk := 1` (because total variation is at most one, `Measure.etvDist_le_one`) and would carry no
content.

## The simulator

`hvzkSimulator` samples the challenge hash `c̃` uniformly and the response `z` as a fresh mask
(`sampleMaskVec`), then computes everything else from the statement `(ρ, t₁, t₀)`:
`wApprox = Az − c·t₁·2^d`, the value `verify` recomputes; the four gates of `respond`; and on
success the pair `h = MakeHint(−c·t₀, wApprox)`, `w₁ = UseHint(h, wApprox)`. On valid key pairs
`wApprox − c·t₀ = w − c·s₂` with `w = A·y` (`keyGenFromSeed_wApprox_eq`), so each gate computes the
same value as the honest prover, and the two transcripts agree as functions of `(c̃, z)`
(`hvzkHonestOut_eq_hvzkSimOut`). The abort pattern therefore matches exactly.

Three of the gates and the hint depend on `t₀`, which FIPS 204 keeps out of the public key. As in
the security analyses of ML-DSA, the statement here carries the full `t = t₁·2^d + t₀`
(`FullPublicKey`), so the simulator reads `t₀` and runs in polynomial time. Transcripts and
verification ignore `t₀`, so a forger against the scheme with public key `(ρ, t₁)` is a forger
against this one.

## The mask coupling

The honest response is `z = y + c·s₁` with `y` uniform on the mask box `[-γ₁ + 1, γ₁]`, so `z` is
uniform on a shifted box rather than on the box itself. When `2γ₁ < q` the mask decoding is
injective, and the two distributions agree on every `z` that can pass the response gate:
`‖z‖∞ < γ₁ − β` and `‖c·s₁‖∞ ≤ β` put both `z` and `z − c·s₁` in the box, and every other `z`
aborts (`honest_pregate_evalDistEq`). This is the rejection-sampling step that makes
the accepted `z` independent of the secret.

## References

- Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium
  (CRYPTO 2023, ePrint 2023/246), Lemma 4 (HVZK of the IDS)
- EasyCrypt `HVZK_FSa.ec`, `SimplifiedScheme.ec` (formosa-crypto/dilithium)
- NIST FIPS 204, Algorithms 7 and 8
-/

@[expose] public section


open OracleComp OracleSpec ENNReal
open LatticeCrypto TransformOps

namespace MLDSA

variable (p : Params) (prims : Primitives p)

section RealHVZK

/-! ### Componentwise algebra on `Rq` and `RqVec` -/

private lemma polyNorm_neg (f : Rq) : polyNorm (-f) = polyNorm f := by
  unfold polyNorm normOps
  simp only [LatticeCrypto.zmodPolyNormOps, LatticeCrypto.normOpsOfCenteredView]
  unfold LatticeCrypto.cInfNormOf
  apply Finset.sup_congr rfl
  intro i _
  simp only [LatticeCrypto.zmodCenteredCoeffView, coeffRing.coeff_neg]
  exact LatticeCrypto.centeredRepr_natAbs_neg _

/-- Right-cancellation for componentwise `RqVec` arithmetic: `y + v - v = y`. -/
private lemma rqVec_add_sub_cancel {k : ℕ} (y v : RqVec k) : y + v - v = y := by
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_sub, Vector.getElem_add]
  exact add_sub_cancel_right _ _

/-- Left-cancellation for componentwise `RqVec` arithmetic: `z - v + v = z`. -/
private lemma rqVec_sub_add_cancel {k : ℕ} (z v : RqVec k) : z - v + v = z := by
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_sub, Vector.getElem_add]
  exact sub_add_cancel _ _

variable [nttOps : NTTRingOps]

/-- **The mask coupling.** With `s` a vector whose challenge products stay `β`-bounded and
`2γ₁ < q`, the honest pre-gate joint distribution of the challenge hash and the masked response
`(c̃, z = y + c·s)`, with the mask `y` drawn before the uniform challenge, equals the simulator's
direct draw of `(c̃, z)` with `z` a fresh mask, as observed by any continuation that ignores `z`
outside the response gate. Both draws are injections of the raw mask samples, `a ↦ maskDecode a +
c·s` and `maskDecode`, and both cover every `z` that passes the gate
(`SampleableType.uniformSample_bind_evalDistEq_of_cover`). -/
theorem honest_pregate_evalDistEq [SampleableType (CommitHashBytes p)] [NeZero p.gamma1]
    {s : RqVec p.l} (hq : 2 * p.gamma1 < modulus)
    (hs : ∀ cTilde : CommitHashBytes p, polyVecNorm (prims.sampleInBall cTilde • s) ≤ p.beta)
    {γ : Type} (g : CommitHashBytes p → RqVec p.l → ProbComp γ)
    (d : CommitHashBytes p → ProbComp γ)
    (hg : ∀ cTilde z, ¬polyVecNorm z < p.gamma1 - p.beta → g cTilde z = d cTilde) :
    (do
        let y ← sampleMaskVec p.l p.gamma1
        let cTilde ← $ᵗ (CommitHashBytes p)
        g cTilde (y + prims.sampleInBall cTilde • s)) =ᵈ
      (do
        let cTilde ← $ᵗ (CommitHashBytes p)
        let z ← sampleMaskVec p.l p.gamma1
        g cTilde z) := by
  let : MeasurableSpace γ := ⊤
  refine (EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_bind_swap _ _ _)).trans ?_
  refine EvalDistEq.bind_right _ fun cTilde => ?_
  have hgamma : ∀ {z : RqVec p.l}, polyVecNorm z < p.gamma1 - p.beta →
      polyVecNorm z < p.gamma1 := fun hz => by omega
  simpa only [sampleMaskVec, bind_map_left] using
    SampleableType.uniformSample_bind_evalDistEq_of_cover
      (α := MaskSample p.l p.gamma1)
      (f₁ := fun a => maskDecode a + prims.sampleInBall cTilde • s) (f₂ := maskDecode)
      (S := {z | polyVecNorm z < p.gamma1 - p.beta})
      (fun a b h => maskDecode_injective hq (by
        simpa only [rqVec_add_sub_cancel] using
          congrArg (· - prims.sampleInBall cTilde • s) h))
      (maskDecode_injective hq)
      (fun z hz => by
        obtain ⟨a, ha⟩ := exists_maskDecode_eq_of_polyVecNorm_lt (gamma1 := p.gamma1)
          (z := z - prims.sampleInBall cTilde • s) (by
            have := polyVecNorm_sub_le z (prims.sampleInBall cTilde • s)
            have := hs cTilde
            have hz' : polyVecNorm z < p.gamma1 - p.beta := hz
            omega)
        exact ⟨a, by simp only [ha, rqVec_sub_add_cancel]⟩)
      (fun z hz => exists_maskDecode_eq_of_polyVecNorm_lt (hgamma hz))
      (g cTilde) (d cTilde) (fun z hz => hg cTilde z hz)

/-! ### The accept-branch transcripts coincide pointwise -/

/-- **The accept-branch transcript match.** On honestly generated key pairs, whenever the
honest secret-dependent gates hold — `‖LowBits(w − c·s₂)‖∞ < γ₂ − β` and `‖c·t₀‖∞ < γ₂` — the
simulator's reconstructed pair `(w₁, h)` at the honest response `z = y + c·s₁` coincides with
the honest accept-branch pair: the commitment `HighBits(A·y)` from `commit` and the hint
`MakeHint(−c·t₀, w − c·s₂ + c·t₀)` from `respond`.

The hint components agree because `wApprox = w − c·s₂ + c·t₀` (`keyGenFromSeed_wApprox_eq`). The
commitment components agree by the hint round-trip `useHint_makeHint` followed by `hide_low` for
the `c·s₂` perturbation. -/
theorem hvzkSimulator_accept_match (h_laws : Primitives.Laws prims nttOps)
    {pk : PublicKey p prims} {sk : SecretKey p} (seed : Bytes 32)
    (hkeygen : keyGenFromSeed p prims seed = (pk, sk))
    (cTilde : CommitHashBytes p) (y : RqVec p.l)
    (hr0 : polyVecNorm (prims.lowBitsVec
      (prims.expandA pk.rho * y - prims.sampleInBall cTilde • sk.s2)) < p.gamma2 - p.beta)
    (hct0 : polyVecNorm (prims.sampleInBall cTilde • sk.t0) < p.gamma2) :
    (prims.useHintVec
        (prims.makeHintVec (-(prims.sampleInBall cTilde • sk.t0))
          (computeWApprox p prims (prims.expandA pk.rho) (prims.sampleInBall cTilde)
            (y + prims.sampleInBall cTilde • sk.s1) pk.t1))
        (computeWApprox p prims (prims.expandA pk.rho) (prims.sampleInBall cTilde)
          (y + prims.sampleInBall cTilde • sk.s1) pk.t1),
      prims.makeHintVec (-(prims.sampleInBall cTilde • sk.t0))
        (computeWApprox p prims (prims.expandA pk.rho) (prims.sampleInBall cTilde)
          (y + prims.sampleInBall cTilde • sk.s1) pk.t1)) =
    (prims.highBitsVec (prims.expandA pk.rho * y),
      prims.makeHintVec (-(prims.sampleInBall cTilde • sk.t0))
        (prims.expandA pk.rho * y - prims.sampleInBall cTilde • sk.s2
          + prims.sampleInBall cTilde • sk.t0)) := by
  have hwa := keyGenFromSeed_wApprox_eq p prims h_laws seed hkeygen
    (prims.sampleInBall cTilde) y
  rw [hwa]
  set c := prims.sampleInBall cTilde with hc_def
  set aHat := prims.expandA pk.rho with haHat_def
  simp only [Prod.mk.injEq]
  refine ⟨?_, trivial⟩
  -- Honest secret vectors are `η`-bounded, so the challenge product is `β`-bounded.
  have hs2_bound : polyVecBounded sk.s2 p.eta := by
    have h := congrArg Prod.snd hkeygen
    simp only [keyGenFromSeed] at h
    rw [← h]
    exact (h_laws.expandS_bound _).2
  have hcs2_norm : polyVecNorm (c • sk.s2) ≤ p.beta :=
    h_laws.sampleInBall_smul_bound cTilde sk.s2 hs2_bound
  -- The challenge-times-`t₀` hint argument is `γ₂`-bounded (after negation).
  have hcond_t0 : ∀ j : Fin p.k, polyNorm ((-(c • sk.t0)).get j) ≤ p.gamma2 := by
    intro j
    rw [Vector.get_eq_getElem, Vector.getElem_neg, polyNorm_neg]
    exact le_of_lt (lt_of_le_of_lt
      (LatticeCrypto.PolyVec.component_cInfNorm_le normOps (c • sk.t0) j) hct0)
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
            (prims.lowBitsVec (aHat * y - c • sk.s2)) j) hr0
        simp only [Primitives.lowBitsVec, Vector.get_eq_getElem, Vector.getElem_map,
          polyNorm] at hj ⊢
        omega)
    rw [harith2] at h
    exact h.symm
  rw [useHintVec_makeHintVec p prims h_laws (-(c • sk.t0))
      (aHat * y - c • sk.s2 + c • sk.t0) hcond_t0, harith1, hhide]

/-! ### The simulator -/

/-- The simulator's transcript as a deterministic function of `(c̃, z)`: the four gates of the
honest `respond`, recomputed from the statement `(ρ, t₁, t₀)`, and on success the pair `(w₁, h)`
recovered from `wApprox = Az − c·t₁·2^d` and `t₀`. -/
def hvzkSimOut (fpk : FullPublicKey p prims) (cTilde : CommitHashBytes p)
    (z : RqVec p.l) :
    Option (Commitment p prims × CommitHashBytes p × Response p prims) :=
  let c := prims.sampleInBall cTilde
  let wApprox := computeWApprox p prims (prims.expandA fpk.pk.rho) c z fpk.pk.t1
  let ct0 := c • fpk.t0
  let r0 := prims.lowBitsVec (wApprox - ct0)
  if polyVecNorm z < p.gamma1 - p.beta ∧ polyVecNorm r0 < p.gamma2 - p.beta then
    let h := prims.makeHintVec (-ct0) wApprox
    if polyVecNorm ct0 < p.gamma2 ∧ prims.hintWeight h ≤ p.omega then
      some (prims.useHintVec h wApprox, cTilde, (z, h))
    else none
  else none

/-- The Dilithium HVZK simulator for the ML-DSA identification scheme with `t₀` in the statement. It
receives only the statement `(ρ, t₁, t₀)`, samples the challenge hash `c̃` uniformly and the
response `z` from the mask box, and outputs `hvzkSimOut`. -/
def hvzkSimulator [SampleableType (CommitHashBytes p)] [NeZero p.gamma1]
    (fpk : FullPublicKey p prims) :
    ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims)) := do
  let cTilde ← $ᵗ (CommitHashBytes p)
  let z ← sampleMaskVec p.l p.gamma1
  return hvzkSimOut p prims fpk cTilde z

/-! ### The honest transcript as a function of `(c̃, z)` -/

/-- The honest transcript as a deterministic function of `(c̃, z)`, with the commit mask
recovered as `y = z − c·s₁`: the four abort gates of the honest `commit`/`respond` followed by
the honest accept output `(HighBits(A·y), c̃, (z, h))`. -/
def hvzkHonestOut (pk : PublicKey p prims) (sk : SecretKey p)
    (cTilde : CommitHashBytes p) (z : RqVec p.l) :
    Option (Commitment p prims × CommitHashBytes p × Response p prims) :=
  let c := prims.sampleInBall cTilde
  let w := prims.expandA pk.rho * (z - c • sk.s1)
  let r0 := prims.lowBitsVec (w - c • sk.s2)
  if polyVecNorm z < p.gamma1 - p.beta ∧ polyVecNorm r0 < p.gamma2 - p.beta then
    let ct0 := c • sk.t0
    let h := prims.makeHintVec (-ct0) (w - c • sk.s2 + ct0)
    if polyVecNorm ct0 < p.gamma2 ∧ prims.hintWeight h ≤ p.omega then
      some (prims.highBitsVec w, cTilde, (z, h))
    else none
  else none

/-- On valid key pairs the honest and simulated transcripts agree for every `(c̃, z)`. With
`y = z − c·s₁` and `w = A·y`, `wApprox = w − c·s₂ + c·t₀` (`keyGenFromSeed_wApprox_eq`), so the
gates and the hint coincide; on accept the commitment does too (`hvzkSimulator_accept_match`). -/
lemma hvzkHonestOut_eq_hvzkSimOut (h_laws : Primitives.Laws prims nttOps)
    {fpk : FullPublicKey p prims} {sk : SecretKey p} (seed : Bytes 32)
    (hkeygen : keyGenFromSeed p prims seed = (fpk.pk, sk)) (ht0 : fpk.t0 = sk.t0)
    (cTilde : CommitHashBytes p) (z : RqVec p.l) :
    hvzkHonestOut p prims fpk.pk sk cTilde z = hvzkSimOut p prims fpk cTilde z := by
  have hy := rqVec_sub_add_cancel z (prims.sampleInBall cTilde • sk.s1)
  have hwa := keyGenFromSeed_wApprox_eq p prims h_laws seed hkeygen
    (prims.sampleInBall cTilde) (z - prims.sampleInBall cTilde • sk.s1)
  rw [hy] at hwa
  simp only [hvzkHonestOut, hvzkSimOut, ht0, hwa, rqVec_add_sub_cancel]
  split_ifs with h1 h2
  · have hmatch := hvzkSimulator_accept_match p prims h_laws seed hkeygen cTilde
      (z - prims.sampleInBall cTilde • sk.s1) h1.2 h2.1
    rw [hy, hwa, Prod.mk.injEq] at hmatch
    rw [hmatch.1]
  all_goals rfl

/-! ### The honest execution over the simulator's randomness -/

/-- The honest execution as the `(y, c̃)` draw followed by a deterministic continuation of
`(c̃, z = y + c·s₁)`: the commit value `w = A·y` is re-expressed through `z` by
`hvzkHonestOut` (which recovers `y = z − c·s₁`), so the uniform-shift coupling
`honest_pregate_evalDistEq` applies. -/
lemma honestExecution_eq_pregate [DecidableEq prims.High] [SampleableType (CommitHashBytes p)]
    [NeZero p.gamma1] (pk : PublicKey p prims) (sk : SecretKey p) :
    (identificationScheme p prims).honestExecution pk sk =
      sampleMaskVec p.l p.gamma1 >>= fun y => ($ᵗ (CommitHashBytes p)) >>= fun cTilde =>
        (fun cT zv =>
            (pure (hvzkHonestOut p prims pk sk cT zv) :
              ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims))))
          cTilde (y + prims.sampleInBall cTilde • sk.s1) := by
  simp only [IdenSchemeWithAbort.honestExecution, identificationScheme, bind_assoc, pure_bind]
  refine bind_congr fun y => bind_congr fun cTilde => ?_
  simp only [hvzkHonestOut, rqVec_add_sub_cancel]
  split_ifs with h1 h2 <;> simp

/-- The honest transcript distribution over the simulator's `(c̃, z)` randomness, on a valid key
pair with `2γ₁ < q`. Honest secrets are `η`-bounded, so their challenge products are `β`-bounded,
and the honest transcript aborts outside the response gate; the mask coupling then applies. -/
lemma honestExecution_evalDistEq_gated [DecidableEq prims.High] [NeZero p.gamma1]
    [SampleableType (CommitHashBytes p)] (h_laws : Primitives.Laws prims nttOps)
    (hq : 2 * p.gamma1 < modulus)
    {pk : PublicKey p prims} {sk : SecretKey p} (seed : Bytes 32)
    (hkeygen : keyGenFromSeed p prims seed = (pk, sk)) :
    (identificationScheme p prims).honestExecution pk sk =ᵈ
      (do
        let cTilde ← $ᵗ (CommitHashBytes p)
        let z ← sampleMaskVec p.l p.gamma1
        return hvzkHonestOut p prims pk sk cTilde z) := by
  have hs1 : polyVecBounded sk.s1 p.eta := by
    have h := congrArg Prod.snd hkeygen
    simp only [keyGenFromSeed] at h
    rw [← h]
    exact (h_laws.expandS_bound _).1
  rw [honestExecution_eq_pregate p prims pk sk]
  exact honest_pregate_evalDistEq p prims hq
    (fun cTilde => h_laws.sampleInBall_smul_bound cTilde sk.s1 hs1)
    (fun cT zv =>
      (pure (hvzkHonestOut p prims pk sk cT zv) :
        ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims))))
    (fun _ => pure none) (fun cT z hz => by simp [hvzkHonestOut, hz])

/-- The scheme with `t₀` in the statement runs the honest prover of `identificationScheme` at the
public key `fpk.pk`. -/
lemma honestExecution_identificationSchemeFull [DecidableEq prims.High] [NeZero p.gamma1]
    [SampleableType (CommitHashBytes p)] (fpk : FullPublicKey p prims) (sk : SecretKey p) :
    (identificationSchemeFull p prims).honestExecution fpk sk =
      (identificationScheme p prims).honestExecution fpk.pk sk := rfl

/-! ### The headline statement -/

/-- **Honest-verifier zero-knowledge for the ML-DSA identification scheme with `t₀` in the
statement.** For every valid key pair the honest transcript and `hvzkSimulator` are equal in
distribution, aborts included. By `IdenSchemeWithAbort.perfectHVZK_iff_hvzk_zero` this is `HVZK` at
`ζ_zk = 0`. The hypothesis `2γ₁ < q`, which every FIPS 204 parameter set meets, makes the mask
decoding injective. -/
theorem identificationSchemeFull_perfectHVZK [DecidableEq prims.High] [NeZero p.gamma1]
    [SampleableType (CommitHashBytes p)] (h_laws : Primitives.Laws prims nttOps)
    (hq : 2 * p.gamma1 < modulus) :
    (identificationSchemeFull p prims).PerfectHVZK (hvzkSimulator p prims) := by
  intro fpk sk hrel
  obtain ⟨hvalid, ht0⟩ := (validFullKeyPair_eq_true_iff p prims fpk sk).mp hrel
  obtain ⟨seed, hkeygen⟩ := (validKeyPair_eq_true_iff p prims fpk.pk sk).mp hvalid
  rw [honestExecution_identificationSchemeFull]
  simpa only [hvzkSimulator, hvzkHonestOut_eq_hvzkSimOut p prims h_laws seed hkeygen ht0] using
    honestExecution_evalDistEq_gated p prims h_laws hq seed hkeygen

end RealHVZK

/-! ### Forgers against the scheme are forgers against the variant -/

section FullTransfer

variable [nttOps : NTTRingOps]

/-- Key generation with `t₀` published: run `hr.gen` and publish the secret key's `t₀`. -/
def fullRelation
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims)) :
    GenerableRelation (FullPublicKey p prims) (SecretKey p) (validFullKeyPair p prims) where
  gen := (fun ks => (⟨ks.1, ks.2.t0⟩, ks.2)) <$> hr.gen
  gen_sound fpk sk h := by
    rw [support_map] at h
    obtain ⟨⟨pk, sk'⟩, hmem, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simpa [validFullKeyPair_eq_true_iff] using hr.gen_sound pk sk' hmem

/-- The signing loop of the variant at `fpk` is the signing loop of `identificationScheme` at the
public key `fpk.pk`. -/
lemma fsAbortSignLoop_identificationSchemeFull [DecidableEq prims.High] [NeZero p.gamma1]
    {M : Type}
    {m : Type → Type} [Monad m]
    [MonadLiftT ProbComp m] [HasQuery (M × Commitment p prims →ₒ CommitHashBytes p) m]
    (fpk : FullPublicKey p prims) (sk : SecretKey p) (msg : M) (n : ℕ) :
    fsAbortSignLoop (identificationSchemeFull p prims) (m := m) M fpk sk msg n =
      fsAbortSignLoop (identificationScheme p prims) M fpk.pk sk msg n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [fsAbortSignLoop, ih]
    rfl

/-- **A forger against the scheme is a forger against the variant with `t₀` published.** Signing
and verification ignore `t₀`, so running a forger for the Fiat-Shamir-with-aborts signature over
`identificationScheme` on the public key `fpk.pk` of the variant over `identificationSchemeFull`
gives the same unforgeability advantage. -/
theorem unforgeableAdvantage_eq_full [DecidableEq prims.High] [NeZero p.gamma1] {M : Type}
    [DecidableEq M] [SampleableType (CommitHashBytes p)]
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPair p prims))
    (maxAttempts : ℕ)
    (adv : SignatureAlg.UnforgeableAdversary
      (FiatShamirWithAbort (identificationScheme p prims) hr M maxAttempts)) :
    SignatureAlg.unforgeableAdvantage
        (FiatShamirWithAbort.runtime (Commit := Commitment p prims) (Chal := CommitHashBytes p) M)
        adv =
      SignatureAlg.unforgeableAdvantage
        (FiatShamirWithAbort.runtime (Commit := Commitment p prims) (Chal := CommitHashBytes p) M)
        (⟨fun fpk => adv.main fpk.pk⟩ : SignatureAlg.UnforgeableAdversary
          (FiatShamirWithAbort (identificationSchemeFull p prims) (fullRelation p prims hr) M
            maxAttempts)) := by
  unfold SignatureAlg.unforgeableAdvantage
  congr 1
  simp only [SignatureAlg.unforgeableExperiment, FiatShamirWithAbort, fullRelation,
    SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle,
    fsAbortSignLoop_identificationSchemeFull]
  rw [monadLift_map, bind_map_left]
  rfl

end FullTransfer

end MLDSA
