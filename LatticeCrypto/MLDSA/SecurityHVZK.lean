/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import LatticeCrypto.MLDSA.Security

/-!
# ML-DSA Honest-Verifier Zero-Knowledge

This file proves that the ML-DSA identification scheme is perfectly honest-verifier zero-knowledge
for a named simulator, `hvzkSimulatorReal` (`MLDSA.idsWithAbort_hvzk`). An existential statement
asserting only that *some* simulator with *some* error exists would be trivially dischargeable with
`ζ_zk := 1` (because total variation is at most one, `Measure.etvDist_le_one`) and would carry no
content.

## The simulator

`hvzkSimulatorReal` samples the challenge hash `c̃` uniformly and the response `z` uniformly from
the mask box, then computes everything else from the public key and the withheld key part `t₀`:
`wApprox = Az − c·t₁·2^d`, the value `verify` recomputes; the four gates of `respond`; and on
success the pair
`h = MakeHint(−c·t₀, wApprox)`, `w₁ = UseHint(h, wApprox)`. On valid key pairs
`wApprox − c·t₀ = w − c·s₂` with `w = A·y` (`keyGenFromSeed_wApprox_eq`), so each gate computes the
same value as the honest prover, and the two transcripts agree as functions of `(c̃, z)`
(`hvzkHonestOut_eq_hvzkSimOut`). The abort pattern therefore matches exactly.

Three of the gates and the hint depend on `t₀`, which the encoded public key `(ρ, t₁)` does not
contain. The simulator recovers it from the public key by a search over all key-generation seeds
(`recoverT0`). The recovery is correct on honestly generated keys under the modelling law
`Primitives.Laws.keyVector_t0_determined`, which no concrete instantiation proves. The search makes
the simulator inefficient. The literature treats the full `t = t₁·2^d + t₀` as public instead, so
its simulator reads `t₀` and runs in polynomial time. On a key that no seed generates, `recoverT0`
returns `0`, so a reduction that runs this simulator can behave differently on seed-derived keys
and on keys sampled independently of any seed.

## The mask coupling

The honest response is `z = y + c·s₁` with `y` uniform on the mask box, so `z` is uniform on a
shifted box rather than on the box itself. The two distributions agree on every `z` that can pass
the response gate: `‖z‖∞ < γ₁ − β` and `‖c·s₁‖∞ ≤ β` put both `z` and `z − c·s₁` in the box, and
every other `z` aborts (`honest_pregate_evalDistEq`). This is the rejection-sampling step that makes
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

/-- **The mask coupling.** With `s` a vector whose challenge products stay `β`-bounded, the honest
pre-gate joint distribution of the challenge hash and the masked response `(c̃, z = y + c·s)`, with
`y` drawn from the mask box before the uniform challenge, equals the simulator's direct draw of
`(c̃, z)` with `z` from the box, as observed by any continuation that ignores `z` outside the
response gate. The two draws are injections of the box, `y ↦ y + c·s` and the inclusion, and both
cover every `z` that passes the gate (`SampleableType.uniformSample_bind_evalDistEq_of_cover`). -/
theorem honest_pregate_evalDistEq [SampleableType (CommitHashBytes p)] {s : RqVec p.l}
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
      (α := {v : RqVec p.l // maskBounded v p.gamma1})
      (f₁ := fun a => a.1 + prims.sampleInBall cTilde • s) (f₂ := Subtype.val)
      (S := {z | polyVecNorm z < p.gamma1 - p.beta})
      (fun a b h => Subtype.ext (by
        simpa only [rqVec_add_sub_cancel] using
          congrArg (· - prims.sampleInBall cTilde • s) h))
      Subtype.val_injective
      (fun z hz => ⟨⟨z - prims.sampleInBall cTilde • s,
        maskBounded_of_polyVecNorm_lt (by
          have := polyVecNorm_sub_le z (prims.sampleInBall cTilde • s)
          have := hs cTilde
          have hz' : polyVecNorm z < p.gamma1 - p.beta := hz
          omega)⟩,
        rqVec_sub_add_cancel z _⟩)
      (fun z hz => ⟨⟨z, maskBounded_of_polyVecNorm_lt (hgamma hz)⟩, rfl⟩)
      (g cTilde) (d cTilde) (fun z hz => hg cTilde z hz)

/-! ### Public recovery of the withheld key part `t₀` -/

/-- Noncomputable recovery of the withheld key part `t₀` from the public key alone: pick any
seed that key generation maps to `pk` and return its `t₀` (or `0` if `pk` is not honestly
generated). On valid key pairs this agrees with the actual secret `t₀` exactly under the
key-generation collision-freeness law `Primitives.Laws.keyVector_t0_determined`
(`recoverT0_eq`). It is a function of the statement only, so the HVZK simulator may use it, but
it searches over all seeds and is not efficient. -/
noncomputable def recoverT0 (pk : PublicKey p prims) : RqVec p.k :=
  by
    letI : Decidable (∃ seed : Bytes 32, (keyGenFromSeed p prims seed).1 = pk) :=
      Classical.propDecidable _
    exact if h : ∃ seed : Bytes 32, (keyGenFromSeed p prims seed).1 = pk then
      (keyGenFromSeed p prims (Classical.choose h)).2.t0
    else 0

/-- The public seed `ρ` of a generated key, in primitives-level form. -/
lemma keyGenFromSeed_rho (seed : Bytes 32) :
    (keyGenFromSeed p prims seed).1.rho = (prims.expandSeed seed).1 := rfl

/-- The published key part `t₁` of a generated key, in primitives-level form. -/
lemma keyGenFromSeed_t1 (seed : Bytes 32) :
    (keyGenFromSeed p prims seed).1.t1 =
      (prims.power2RoundVec (prims.keyVector nttOps seed)).1 := rfl

/-- The withheld key part `t₀` of a generated key, in primitives-level form. -/
lemma keyGenFromSeed_t0 (seed : Bytes 32) :
    (keyGenFromSeed p prims seed).2.t0 =
      (prims.power2RoundVec (prims.keyVector nttOps seed)).2 := rfl

/-- On honestly generated key pairs, `recoverT0` recovers the actual withheld key part `t₀`.
This is where the key-generation collision-freeness law
`Primitives.Laws.keyVector_t0_determined` is used: any seed consistent with the public key
yields the same `t₀` as the seed that actually generated the pair. -/
theorem recoverT0_eq (h_laws : Primitives.Laws prims nttOps)
    {pk : PublicKey p prims} {sk : SecretKey p} (seed : Bytes 32)
    (hkeygen : keyGenFromSeed p prims seed = (pk, sk)) :
    recoverT0 p prims pk = sk.t0 := by
  have hex : ∃ s : Bytes 32, (keyGenFromSeed p prims s).1 = pk :=
    ⟨seed, congrArg Prod.fst hkeygen⟩
  have hpk' : (keyGenFromSeed p prims (Classical.choose hex)).1 = pk :=
    Classical.choose_spec hex
  have hpk : (keyGenFromSeed p prims seed).1 = pk := congrArg Prod.fst hkeygen
  have hrho : (prims.expandSeed (Classical.choose hex)).1 = (prims.expandSeed seed).1 := by
    rw [← keyGenFromSeed_rho p prims, ← keyGenFromSeed_rho p prims, hpk', hpk]
  have ht1 : (prims.power2RoundVec (prims.keyVector nttOps (Classical.choose hex))).1 =
      (prims.power2RoundVec (prims.keyVector nttOps seed)).1 := by
    rw [← keyGenFromSeed_t1 p prims, ← keyGenFromSeed_t1 p prims, hpk', hpk]
  have ht0 := h_laws.keyVector_t0_determined (Classical.choose hex) seed hrho ht1
  have hchoose : recoverT0 p prims pk =
      (keyGenFromSeed p prims (Classical.choose hex)).2.t0 := by
    simp only [recoverT0, dite_eq_left hex]
  rw [hchoose, keyGenFromSeed_t0 p prims, ht0, ← keyGenFromSeed_t0 p prims, hkeygen]

/-! ### The accept-branch transcripts coincide pointwise -/

/-- **The accept-branch transcript match.** On honestly generated key pairs, whenever the
honest secret-dependent gates hold — `‖LowBits(w − c·s₂)‖∞ < γ₂ − β` and `‖c·t₀‖∞ < γ₂` — the
simulator's reconstructed pair `(w₁, h)` at the honest response `z = y + c·s₁` coincides with
the honest accept-branch pair: the commitment `HighBits(A·y)` from `commit` and the hint
`MakeHint(−c·t₀, w − c·s₂ + c·t₀)` from `respond`.

The hint components agree because `wApprox = w − c·s₂ + c·t₀` (`keyGenFromSeed_wApprox_eq`)
and `recoverT0` returns the actual `t₀` (`recoverT0_eq`). The commitment components agree by
the hint round-trip `useHint_makeHint` followed by `hide_low` for the `c·s₂` perturbation. -/
theorem hvzkSimulatorReal_accept_match (h_laws : Primitives.Laws prims nttOps)
    {pk : PublicKey p prims} {sk : SecretKey p} (seed : Bytes 32)
    (hkeygen : keyGenFromSeed p prims seed = (pk, sk))
    (cTilde : CommitHashBytes p) (y : RqVec p.l)
    (hr0 : polyVecNorm (prims.lowBitsVec
      (prims.expandA pk.rho * y - prims.sampleInBall cTilde • sk.s2)) < p.gamma2 - p.beta)
    (hct0 : polyVecNorm (prims.sampleInBall cTilde • sk.t0) < p.gamma2) :
    (prims.useHintVec
        (prims.makeHintVec (-(prims.sampleInBall cTilde • recoverT0 p prims pk))
          (computeWApprox p prims (prims.expandA pk.rho) (prims.sampleInBall cTilde)
            (y + prims.sampleInBall cTilde • sk.s1) pk.t1))
        (computeWApprox p prims (prims.expandA pk.rho) (prims.sampleInBall cTilde)
          (y + prims.sampleInBall cTilde • sk.s1) pk.t1),
      prims.makeHintVec (-(prims.sampleInBall cTilde • recoverT0 p prims pk))
        (computeWApprox p prims (prims.expandA pk.rho) (prims.sampleInBall cTilde)
          (y + prims.sampleInBall cTilde • sk.s1) pk.t1)) =
    (prims.highBitsVec (prims.expandA pk.rho * y),
      prims.makeHintVec (-(prims.sampleInBall cTilde • sk.t0))
        (prims.expandA pk.rho * y - prims.sampleInBall cTilde • sk.s2
          + prims.sampleInBall cTilde • sk.t0)) := by
  have ht0 : recoverT0 p prims pk = sk.t0 := recoverT0_eq p prims h_laws seed hkeygen
  have hwa := keyGenFromSeed_wApprox_eq p prims h_laws seed hkeygen
    (prims.sampleInBall cTilde) y
  rw [ht0, hwa]
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
honest `respond`, recomputed from the public key and the recovered `t₀` (`recoverT0`), and on
success the pair `(w₁, h)` recovered from `wApprox = Az − c·t₁·2^d` and `t₀`. -/
noncomputable def hvzkSimOut (pk : PublicKey p prims) (cTilde : CommitHashBytes p)
    (z : RqVec p.l) :
    Option (Commitment p prims × CommitHashBytes p × Response p prims) :=
  let c := prims.sampleInBall cTilde
  let wApprox := computeWApprox p prims (prims.expandA pk.rho) c z pk.t1
  let ct0 := c • recoverT0 p prims pk
  let r0 := prims.lowBitsVec (wApprox - ct0)
  if polyVecNorm z < p.gamma1 - p.beta ∧ polyVecNorm r0 < p.gamma2 - p.beta then
    let h := prims.makeHintVec (-ct0) wApprox
    if polyVecNorm ct0 < p.gamma2 ∧ prims.hintWeight h ≤ p.omega then
      some (prims.useHintVec h wApprox, cTilde, (z, h))
    else none
  else none

/-- The Dilithium HVZK simulator for the ML-DSA identification scheme. It takes only the public key
`pk` and recovers `t₀` from it by `recoverT0`, a search over seeds, so it is not efficient. It
samples the challenge hash `c̃` uniformly and the response `z` from the mask box, and outputs
`hvzkSimOut`. -/
noncomputable def hvzkSimulatorReal [SampleableType (CommitHashBytes p)]
    (pk : PublicKey p prims) :
    ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims)) := do
  let cTilde ← $ᵗ (CommitHashBytes p)
  let z ← sampleMaskVec p.l p.gamma1
  return hvzkSimOut p prims pk cTilde z

/-! ### The honest transcript as a function of `(c̃, z)` -/

/-- The honest transcript as a deterministic function of `(c̃, z)`, with the commit mask
recovered as `y = z − c·s₁`: the four abort gates of the honest `commit`/`respond` followed by
the honest accept output `(HighBits(A·y), c̃, (z, h))`. -/
noncomputable def hvzkHonestOut (pk : PublicKey p prims) (sk : SecretKey p)
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
`y = z − c·s₁` and `w = A·y`, `wApprox = w − c·s₂ + c·t₀` (`keyGenFromSeed_wApprox_eq`), and
`recoverT0` returns the actual `t₀`, so the gates and the hint coincide; on accept the commitment
does too (`hvzkSimulatorReal_accept_match`). -/
lemma hvzkHonestOut_eq_hvzkSimOut (h_laws : Primitives.Laws prims nttOps)
    {pk : PublicKey p prims} {sk : SecretKey p} (seed : Bytes 32)
    (hkeygen : keyGenFromSeed p prims seed = (pk, sk))
    (cTilde : CommitHashBytes p) (z : RqVec p.l) :
    hvzkHonestOut p prims pk sk cTilde z = hvzkSimOut p prims pk cTilde z := by
  have ht0 : recoverT0 p prims pk = sk.t0 := recoverT0_eq p prims h_laws seed hkeygen
  have hy := rqVec_sub_add_cancel z (prims.sampleInBall cTilde • sk.s1)
  have hwa := keyGenFromSeed_wApprox_eq p prims h_laws seed hkeygen
    (prims.sampleInBall cTilde) (z - prims.sampleInBall cTilde • sk.s1)
  rw [hy] at hwa
  simp only [hvzkHonestOut, hvzkSimOut, ht0, hwa, rqVec_add_sub_cancel]
  split_ifs with h1 h2
  · have hmatch := hvzkSimulatorReal_accept_match p prims h_laws seed hkeygen cTilde
      (z - prims.sampleInBall cTilde • sk.s1) h1.2 h2.1
    rw [hy, ht0, hwa, Prod.mk.injEq] at hmatch
    rw [hmatch.1]
  all_goals rfl

/-! ### The honest execution over the simulator's randomness -/

/-- The honest execution as the `(y, c̃)` draw followed by a deterministic continuation of
`(c̃, z = y + c·s₁)`: the commit value `w = A·y` is re-expressed through `z` by
`hvzkHonestOut` (which recovers `y = z − c·s₁`), so the uniform-shift coupling
`honest_pregate_evalDistEq` applies. -/
lemma honestExecution_eq_pregate [DecidableEq prims.High] [SampleableType (CommitHashBytes p)]
    (pk : PublicKey p prims) (sk : SecretKey p) :
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
pair. Honest secrets are `η`-bounded, so their challenge products are `β`-bounded, and the honest
transcript aborts outside the response gate; the mask coupling then applies. -/
lemma honestExecution_evalDistEq_gated [DecidableEq prims.High]
    [SampleableType (CommitHashBytes p)] (h_laws : Primitives.Laws prims nttOps)
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
  exact honest_pregate_evalDistEq p prims
    (fun cTilde => h_laws.sampleInBall_smul_bound cTilde sk.s1 hs1)
    (fun cT zv =>
      (pure (hvzkHonestOut p prims pk sk cT zv) :
        ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims))))
    (fun _ => pure none) (fun cT z hz => by simp [hvzkHonestOut, hz])

/-! ### The headline statement -/

/-- **Honest-verifier zero-knowledge for the ML-DSA identification scheme.** For every valid key
pair the honest transcript and `hvzkSimulatorReal` are equal in distribution, aborts included. By
`IdenSchemeWithAbort.perfectHVZK_iff_hvzk_zero` this is `HVZK` at `ζ_zk = 0`.

The simulator recovers `t₀` by a search over seeds (`recoverT0`), which is correct under the
`keyVector_t0_determined` field of `h_laws`, so it is not efficient. -/
theorem idsWithAbort_hvzk [DecidableEq prims.High] [SampleableType (CommitHashBytes p)]
    (h_laws : Primitives.Laws prims nttOps) :
    (identificationScheme p prims).PerfectHVZK (hvzkSimulatorReal p prims) := by
  intro pk sk hrel
  obtain ⟨seed, hkeygen⟩ := (validKeyPair_eq_true_iff p prims pk sk).mp hrel
  simpa only [hvzkSimulatorReal, hvzkHonestOut_eq_hvzkSimOut p prims h_laws seed hkeygen] using
    honestExecution_evalDistEq_gated p prims h_laws seed hkeygen

end RealHVZK

end MLDSA
