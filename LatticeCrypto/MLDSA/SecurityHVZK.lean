/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/
import LatticeCrypto.MLDSA.Security

/-!
# ML-DSA Honest-Verifier Zero-Knowledge: simulators and the quantitative bound

This file develops the honest-verifier zero-knowledge (HVZK) simulators for the ML-DSA
identification scheme, towards refining the vacuous placeholder `MLDSA.idsWithAbort_hvzk`
(`LatticeCrypto/MLDSA/Security.lean`). The placeholder asserts only that *some* simulator with
*some* nonnegative total-variation error exists; that is trivially dischargeable with
`ζ_zk := 1` (because `tvDist ≤ 1` always, `SPMF.tvDist_le_one`) and carries no content.

## The marginal simulator `hvzkSimulator`

`hvzkSimulator` is the simplest Dilithium HVZK simulator (no witness), built from the
commitment-recovery equation. It samples the challenge hash `c̃` and the short response `z` from
their marginals, applies the same `‖z‖∞ < γ₁ − β` rejection gate that the honest `respond`
applies, and reconstructs the commitment `w₁` as `UseHint(h, Az − c·t₁·2^d)` via
`computeWApprox`, exactly the value that `verify` recomputes. `hvzkSimulator_verify` records the
consequence: every non-aborting simulated transcript is accepted by `verify` (modulo the
hint-weight side condition the honest distribution also imposes).

A *perfect* HVZK statement pinning this simulator with error `ζ_zk = 0`, i.e.
`(identificationScheme p prims).HVZK (hvzkSimulator p prims) 0`, is **unsound**.
`HVZK ids sim ζ` compares the full honest and simulated distributions
over `Option (Commit × Chal × Resp)` by total-variation distance, so it is sensitive to the
abort probability. The honest `respond` (`Scheme.lean`) aborts on four gates — `‖z‖∞ < γ₁ − β`,
the secret-dependent `‖LowBits(w − c·s₂)‖∞ < γ₂ − β`, `‖c·t₀‖∞ < γ₂`, and `hintWeight h ≤ ω` —
whereas `hvzkSimulator` applies only the first. Because the honest abort event is a strict
superset and `tvDist ≥ |Pr_honest[none] − Pr_sim[none]|`, the distance is strictly positive in
general (with `p`/`prims` unconstrained and no `Primitives.Laws` hypothesis a literal
counterexample exists, e.g. `hintWeight ≡ 1` with `ω = 0`). The honest hint `h` is moreover a
deterministic function of the witness, against the simulator's independent-uniform draw.

## The exact-on-accept simulator `hvzkSimulatorReal`

`hvzkSimulatorReal` reproduces the honest transcript *pointwise* on the accept event: it
samples `(c̃, z)` from the honest marginals (`evalDist_uniform_add_right_swap` is the
`y ↦ y + c·s₁` shift bijection making `z` uniform), applies the `‖z‖∞ < γ₁ − β` gate, and on
success reconstructs `(w₁, h)` exactly as the honest accept branch does
(`hvzkSimulatorReal_accept_match`). The honest pair genuinely depends on `t₀` — on the accept
event the hint carries `HighBits(wApprox − c·t₀)` versus `HighBits(wApprox)`, and `t₀` is not
determined by the encoded public key `(ρ, t₁)` as raw data — so the simulator recovers `t₀`
noncomputably from the public key (`recoverT0`). This recovery is sound under the
key-generation collision-freeness law `Primitives.Laws.keyVector_t0_determined`, matching the
literature's treatment of the full `t = t₁·2^d + t₀` as public (the `t₁` compression is a
bandwidth optimization, not a hiding mechanism).

The resulting quantitative statement `idsWithAbort_hvzk_real` bounds the total-variation
distance by `hvzkBoundReal`, the honest prover's *extra-rejection mass*: the probability that
the `z`-gate passes but one of the three secret-dependent gates fails. On the accept event the
two transcripts coincide, so this bound is exact rather than a slack inequality.

## References

- Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium
  (CRYPTO 2023, ePrint 2023/246), Lemma 4 (HVZK of the IDS)
- EasyCrypt `HVZK_FSa.ec`, `SimplifiedScheme.ec` (formosa-crypto/dilithium)
- NIST FIPS 204, Algorithms 7 and 8
-/


open OracleComp OracleSpec ENNReal
open LatticeCrypto TransformOps

namespace MLDSA

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps]
  [DecidableEq prims.High]

section HVZK

variable [SampleableType (RqVec p.l)] [SampleableType (CommitHashBytes p)]
  [SampleableType (Vector prims.Hint p.k)] [IsUniformSpec unifSpec]

/-! ### The simulator -/

/-- The Dilithium honest-verifier zero-knowledge simulator for the ML-DSA identification
scheme. It receives only the public key `pk` (no secret) and produces an optional transcript
`(w₁, c̃, (z, h))`:

1. sample the challenge hash `c̃` uniformly (its honest marginal is uniform);
2. sample the short response `z` uniformly from `RqVec p.l` and the hint vector `h` from its
   marginal;
3. apply the same response gate `‖z‖∞ < γ₁ − β` the honest `respond` applies — on failure,
   abort (`none`);
4. on success, reconstruct the commitment via the verification equation
   `w₁ = UseHint(h, computeWApprox(Â, c, z, t₁))` and output `some (w₁, c̃, (z, h))`.

Because `w₁` is defined exactly as the value `verify` recomputes, every non-aborting simulated
transcript is accepted by `verify` (see `hvzkSimulator_verify`). The remaining HVZK content is
that this distribution is statistically close to the honest transcript distribution; the gap is
the rejection-sampling error `hvzkBound`. -/
noncomputable def hvzkSimulator (pk : PublicKey p prims) :
    ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims)) := do
  let cTilde ← $ᵗ (CommitHashBytes p)
  let z ← $ᵗ (RqVec p.l)
  let h ← $ᵗ (Vector prims.Hint p.k)
  if polyVecNorm z < p.gamma1 - p.beta then
    let c := prims.sampleInBall cTilde
    let aHat := prims.expandA pk.rho
    let wApprox := computeWApprox p prims aHat c z pk.t1
    let w1 := prims.useHintVec h wApprox
    return some (w1, cTilde, (z, h))
  else
    return none

/-! ### Well-definedness: simulated non-aborts are accepted -/

omit [SampleableType (CommitHashBytes p)]
  [SampleableType (Vector prims.Hint p.k)] [IsUniformSpec unifSpec] in
/-- Every transcript in the support of `hvzkSimulator pk` is either an abort or an accepting
transcript: the recovered `w₁` satisfies `verify pk w₁ c̃ (z, h) = true` whenever the
hint-weight side condition `hintWeight h ≤ ω` holds. (The `‖z‖∞ < γ₁ − β` half of `verify`
is exactly the simulator's own rejection gate, so it holds on the support by construction.)

This is the simulator's well-definedness: it never emits a non-aborting transcript that the
verifier would reject, modulo the hint-weight side condition that the honest distribution also
imposes. -/
theorem hvzkSimulator_verify (pk : PublicKey p prims) (cTilde : CommitHashBytes p)
    (z : RqVec p.l) (h : Vector prims.Hint p.k)
    (hz : polyVecNorm z < p.gamma1 - p.beta)
    (hw : prims.hintWeight h ≤ p.omega) :
    (identificationScheme p prims).verify pk
        (prims.useHintVec h
          (computeWApprox p prims (prims.expandA pk.rho) (prims.sampleInBall cTilde) z pk.t1))
        cTilde (z, h) = true := by
  simp only [identificationScheme, Bool.and_eq_true, decide_eq_true_eq, and_true]
  exact ⟨hz, hw⟩

end HVZK

/-! ## The exact-on-accept simulator and the quantitative HVZK bound -/

section RealHVZK

/-! ### Generic uniform-shift coupling (L1) -/

/-- Additive commutative group structure on `RqVec k`, componentwise over the existing core
`Vector` operations (so `+`, `-`, `0` are unchanged). Local because it is needed only to apply
the uniform-translation lemmas of `SampleableType` to `RqVec`. -/
local instance instAddCommGroupRqVec {k : ℕ} : AddCommGroup (RqVec k) where
  add := (· + ·)
  zero := 0
  neg := (- ·)
  sub := (· - ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := Vector.add_assoc fun x y z => add_assoc x y z
  zero_add := Vector.zero_add fun x => zero_add x
  add_zero := Vector.add_zero fun x => add_zero x
  add_comm := Vector.add_comm fun x y => add_comm x y
  sub_eq_add_neg := Vector.sub_eq_add_neg fun x y => sub_eq_add_neg x y
  neg_add_cancel := Vector.neg_add_cancel fun x => neg_add_cancel x

omit nttOps [DecidableEq prims.High] in
/-- **The `z`-bijection (L1).** Sampling `y` uniformly and transporting through the per-`a`
right-translation `y ↦ y + f a` yields the same joint distribution as sampling the translated
value directly: the joint distribution of `(a, y + f a)` for independent uniform `y ← $ᵗ β` and
`a ← $ᵗ α` equals that of `(a, z)` for uniform `z ← $ᵗ β`. Combines independence of the two
draws (`probOutput_bind_bind_swap`) with right-translation invariance of the uniform
distribution on an additive group (`probOutput_bind_add_right_uniform`).

For ML-DSA this couples the honest pre-gate joint `(c̃, z = y + c·s₁)` (uniform mask `y` drawn
by `commit` before the challenge) with the simulator's direct draw of `(c̃, z)`. -/
lemma evalDist_uniform_add_right_swap {α β γ : Type} [SampleableType α] [SampleableType β]
    [AddGroup β] (f : α → β) (g : α → β → ProbComp γ) :
    𝒟[do let y ← $ᵗ β; let a ← $ᵗ α; g a (y + f a)] =
      𝒟[do let a ← $ᵗ α; let z ← $ᵗ β; g a z] := by
  refine evalDist_ext fun x => ?_
  rw [probOutput_bind_bind_swap ($ᵗ β) ($ᵗ α) (fun y a => g a (y + f a)) x]
  exact probOutput_bind_congr fun a _ => probOutput_bind_add_right_uniform β (f a) (g a) x

variable [SampleableType (RqVec p.l)] [SampleableType (CommitHashBytes p)]

omit [DecidableEq prims.High] in
/-- **L1, ML-DSA form.** The honest pre-gate joint distribution of the challenge hash and the
masked response `(c̃, z = y + c·s₁)` — with the mask `y` drawn uniformly by `commit` before
the uniform challenge — equals the simulator's direct draw of `(c̃, z)` with `z` uniform, as
observed by any continuation. Over uniform `y`, the map `y ↦ y + c·s₁` is a bijection of
`RqVec p.l`, so `z` is uniform and independent of `c̃`. -/
theorem evalDist_honest_pregate (sk : SecretKey p) {γ : Type}
    (g : CommitHashBytes p → RqVec p.l → ProbComp γ) :
    𝒟[do
        let y ← $ᵗ (RqVec p.l)
        let cTilde ← $ᵗ (CommitHashBytes p)
        g cTilde (y + prims.sampleInBall cTilde • sk.s1)] =
      𝒟[do
        let cTilde ← $ᵗ (CommitHashBytes p)
        let z ← $ᵗ (RqVec p.l)
        g cTilde z] :=
  evalDist_uniform_add_right_swap (fun cTilde => prims.sampleInBall cTilde • sk.s1) g

/-! ### Public recovery of the withheld key part `t₀` -/

open Classical in
/-- Noncomputable recovery of the withheld key part `t₀` from the public key alone: pick any
seed that key generation maps to `pk` and return its `t₀` (or `0` if `pk` is not honestly
generated). On valid key pairs this agrees with the actual secret `t₀` exactly under the
key-generation collision-freeness law `Primitives.Laws.keyVector_t0_determined`
(`recoverT0_eq`). The HVZK simulator may use it because it is a function of the statement
only; cryptographically this corresponds to treating the full `t = t₁·2^d + t₀` as public. -/
noncomputable def recoverT0 (pk : PublicKey p prims) : RqVec p.k :=
  if h : ∃ seed : Bytes 32, (keyGenFromSeed p prims seed).1 = pk then
    (keyGenFromSeed p prims (Classical.choose h)).2.t0
  else 0

omit [SampleableType (RqVec p.l)] [SampleableType (CommitHashBytes p)]
  [DecidableEq prims.High] in
/-- The public seed `ρ` of a generated key, in primitives-level form. -/
lemma keyGenFromSeed_rho (seed : Bytes 32) :
    (keyGenFromSeed p prims seed).1.rho = (prims.expandSeed seed).1 := rfl

omit [SampleableType (RqVec p.l)] [SampleableType (CommitHashBytes p)]
  [DecidableEq prims.High] in
/-- The published key part `t₁` of a generated key, in primitives-level form. -/
lemma keyGenFromSeed_t1 (seed : Bytes 32) :
    (keyGenFromSeed p prims seed).1.t1 =
      (prims.power2RoundVec (prims.keyVector nttOps seed)).1 := rfl

omit [SampleableType (RqVec p.l)] [SampleableType (CommitHashBytes p)]
  [DecidableEq prims.High] in
/-- The withheld key part `t₀` of a generated key, in primitives-level form. -/
lemma keyGenFromSeed_t0 (seed : Bytes 32) :
    (keyGenFromSeed p prims seed).2.t0 =
      (prims.power2RoundVec (prims.keyVector nttOps seed)).2 := rfl

omit [SampleableType (RqVec p.l)] [SampleableType (CommitHashBytes p)]
  [DecidableEq prims.High] in
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
    simp only [recoverT0, dif_pos hex]
  rw [hchoose, keyGenFromSeed_t0 p prims, ht0, ← keyGenFromSeed_t0 p prims, hkeygen]

/-! ### The exact-on-accept simulator -/

/-- The exact-on-accept Dilithium HVZK simulator for the ML-DSA identification scheme. It
receives only the public key `pk` (no secret) and produces an optional transcript
`(w₁, c̃, (z, h))`:

1. sample the challenge hash `c̃` uniformly (its honest marginal is uniform);
2. sample the short response `z` uniformly from `RqVec p.l` (its honest pre-gate marginal is
   uniform by the `y ↦ y + c·s₁` shift bijection, `evalDist_honest_pregate`);
3. apply the response gate `‖z‖∞ < γ₁ − β`, exactly the first gate of the honest `respond` —
   on failure, abort (`none`);
4. on success, reconstruct the honest accept-branch values from the statement: with
   `wApprox = Az − c·t₁·2^d` (which equals `w − c·s₂ + c·t₀` on valid keys,
   `keyGenFromSeed_wApprox_eq`) and the recovered `t₀` (`recoverT0`), output
   `h = MakeHint(−c·t₀, wApprox)` and `w₁ = UseHint(h, wApprox)`.

On the honest accept event the output `(w₁, c̃, (z, h))` coincides with the honest transcript
pointwise (`hvzkSimulatorReal_accept_match`); the simulator does not mirror the three
secret-dependent gates, so the total-variation distance to the honest distribution is exactly
the extra-rejection mass `hvzkBadMass` (bounded by `hvzkBoundReal`). -/
noncomputable def hvzkSimulatorReal (pk : PublicKey p prims) :
    ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims)) := do
  let cTilde ← $ᵗ (CommitHashBytes p)
  let z ← $ᵗ (RqVec p.l)
  if polyVecNorm z < p.gamma1 - p.beta then
    let c := prims.sampleInBall cTilde
    let aHat := prims.expandA pk.rho
    let wApprox := computeWApprox p prims aHat c z pk.t1
    let ct0 := c • recoverT0 p prims pk
    let h := prims.makeHintVec (-ct0) wApprox
    let w1 := prims.useHintVec h wApprox
    return some (w1, cTilde, (z, h))
  else
    return none

/-! ### L2: the accept-branch transcripts coincide pointwise -/

omit nttOps [SampleableType (RqVec p.l)] [SampleableType (CommitHashBytes p)]
  [DecidableEq prims.High] in
private lemma neg_rq_get (f : Rq) (i : Fin ringDegree) : (-f).get i = -(f.get i) := by
  change (coeffRing.neg f).get i = _
  simp

omit nttOps [SampleableType (RqVec p.l)] [SampleableType (CommitHashBytes p)]
  [DecidableEq prims.High] in
private lemma polyNorm_neg (f : Rq) : polyNorm (-f) = polyNorm f := by
  unfold polyNorm normOps
  simp only [LatticeCrypto.zmodPolyNormOps, LatticeCrypto.normOpsOfCenteredView]
  unfold LatticeCrypto.cInfNormOf
  apply Finset.sup_congr rfl
  intro i _
  simp only [LatticeCrypto.zmodCenteredCoeffView, coeffRing.coeff_neg]
  exact LatticeCrypto.centeredRepr_natAbs_neg _

omit [SampleableType (RqVec p.l)] [SampleableType (CommitHashBytes p)]
  [DecidableEq prims.High] in
/-- **The accept-branch transcript match (L2).** On honestly generated key pairs, whenever the
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

/-! ### Deterministic transcript maps over the shared `(c̃, z)` randomness -/

omit nttOps [SampleableType (RqVec p.l)] [SampleableType (CommitHashBytes p)]
  [DecidableEq prims.High] in
/-- Right-cancellation for componentwise `RqVec` arithmetic: `y + v - v = y`. -/
private lemma rqVec_add_sub_cancel {k : ℕ} (y v : RqVec k) : y + v - v = y := by
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_sub, Vector.getElem_add]
  exact add_sub_cancel_right _ _

omit nttOps [SampleableType (RqVec p.l)] [SampleableType (CommitHashBytes p)]
  [DecidableEq prims.High] in
/-- Left-cancellation for componentwise `RqVec` arithmetic: `z - v + v = z`. -/
private lemma rqVec_sub_add_cancel {k : ℕ} (z v : RqVec k) : z - v + v = z := by
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_sub, Vector.getElem_add]
  exact sub_add_cancel _ _

/-- The transcript emitted by `hvzkSimulatorReal` on its accept branch, as a deterministic
function of the challenge hash `c̃` and the response `z`. -/
noncomputable def hvzkSimOut (pk : PublicKey p prims) (cTilde : CommitHashBytes p)
    (z : RqVec p.l) :
    Commitment p prims × CommitHashBytes p × Response p prims :=
  let c := prims.sampleInBall cTilde
  let aHat := prims.expandA pk.rho
  let wApprox := computeWApprox p prims aHat c z pk.t1
  let ct0 := c • recoverT0 p prims pk
  let h := prims.makeHintVec (-ct0) wApprox
  let w1 := prims.useHintVec h wApprox
  (w1, cTilde, (z, h))

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

/-- The gate-mismatch indicator over the shared `(c̃, z)` randomness (`y = z − c·s₁` recovers
the honest mask): the response gate passes but at least one of the three secret-dependent
gates fails. On this event the honest prover aborts while the simulator emits a transcript;
everywhere else the two deterministic transcripts coincide. -/
def hvzkBadIndicator (pk : PublicKey p prims) (sk : SecretKey p)
    (cTilde : CommitHashBytes p) (z : RqVec p.l) : Bool :=
  let c := prims.sampleInBall cTilde
  let w := prims.expandA pk.rho * (z - c • sk.s1)
  let r0 := prims.lowBitsVec (w - c • sk.s2)
  let ct0 := c • sk.t0
  let h := prims.makeHintVec (-ct0) (w - c • sk.s2 + ct0)
  decide (polyVecNorm z < p.gamma1 - p.beta ∧
    ¬(polyVecNorm r0 < p.gamma2 - p.beta ∧ polyVecNorm ct0 < p.gamma2 ∧
      prims.hintWeight h ≤ p.omega))

omit [DecidableEq prims.High] in
/-- `hvzkSimulatorReal` as the `(c̃, z)` draw followed by its deterministic gated output. -/
lemma hvzkSimulatorReal_eq_gated (pk : PublicKey p prims) :
    hvzkSimulatorReal p prims pk = do
      let cTilde ← $ᵗ (CommitHashBytes p)
      let z ← $ᵗ (RqVec p.l)
      return (if polyVecNorm z < p.gamma1 - p.beta
        then some (hvzkSimOut p prims pk cTilde z) else none) := by
  simp only [hvzkSimulatorReal]
  refine bind_congr fun cTilde => bind_congr fun z => ?_
  by_cases hz : polyVecNorm z < p.gamma1 - p.beta <;> simp [hvzkSimOut, hz]

/-- The honest execution as the `(y, c̃)` draw followed by a deterministic continuation of
`(c̃, z = y + c·s₁)`: the commit value `w = A·y` is re-expressed through `z` by
`hvzkHonestOut` (which recovers `y = z − c·s₁`), so the uniform-shift coupling
`evalDist_honest_pregate` applies. -/
lemma honestExecution_eq_pregate (pk : PublicKey p prims) (sk : SecretKey p) :
    (identificationScheme p prims).honestExecution pk sk =
      ($ᵗ (RqVec p.l)) >>= fun y => ($ᵗ (CommitHashBytes p)) >>= fun cTilde =>
        (fun cT zv =>
            (pure (hvzkHonestOut p prims pk sk cT zv) :
              ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims))))
          cTilde (y + prims.sampleInBall cTilde • sk.s1) := by
  simp only [IdenSchemeWithAbort.honestExecution, identificationScheme, bind_assoc, pure_bind]
  refine bind_congr fun y => bind_congr fun cTilde => ?_
  simp only [hvzkHonestOut, rqVec_add_sub_cancel]
  split_ifs with h1 h2 <;> simp

/-- The honest transcript distribution over the simulator's `(c̃, z)` randomness. -/
lemma evalDist_honestExecution_eq_gated (pk : PublicKey p prims) (sk : SecretKey p) :
    𝒟[(identificationScheme p prims).honestExecution pk sk] =
      𝒟[do
        let cTilde ← $ᵗ (CommitHashBytes p)
        let z ← $ᵗ (RqVec p.l)
        return hvzkHonestOut p prims pk sk cTilde z] := by
  rw [honestExecution_eq_pregate p prims pk sk]
  exact evalDist_honest_pregate p prims sk
    (fun cT zv =>
      (pure (hvzkHonestOut p prims pk sk cT zv) :
        ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims))))

omit [SampleableType (RqVec p.l)] [SampleableType (CommitHashBytes p)]
  [DecidableEq prims.High] in
/-- Off the gate-mismatch event the honest and gated-simulator deterministic transcripts
coincide pointwise: if the response gate fails both abort, and if additionally the three
secret-dependent gates hold the accept-branch outputs match
(`hvzkSimulatorReal_accept_match`). -/
lemma hvzkHonestOut_eq_gated_of_not_bad (h_laws : Primitives.Laws prims nttOps)
    {pk : PublicKey p prims} {sk : SecretKey p} (seed : Bytes 32)
    (hkeygen : keyGenFromSeed p prims seed = (pk, sk))
    (cTilde : CommitHashBytes p) (z : RqVec p.l)
    (hbad : ¬hvzkBadIndicator p prims pk sk cTilde z = true) :
    hvzkHonestOut p prims pk sk cTilde z =
      if polyVecNorm z < p.gamma1 - p.beta then some (hvzkSimOut p prims pk cTilde z)
      else none := by
  simp only [hvzkBadIndicator, decide_eq_true_eq] at hbad
  push Not at hbad
  by_cases hz : polyVecNorm z < p.gamma1 - p.beta
  · obtain ⟨hr0, hct0, hw⟩ := hbad hz
    have hmatch := hvzkSimulatorReal_accept_match p prims h_laws seed hkeygen cTilde
      (z - prims.sampleInBall cTilde • sk.s1) hr0 hct0
    rw [rqVec_sub_add_cancel] at hmatch
    rw [Prod.mk.injEq] at hmatch
    obtain ⟨hm1, hm2⟩ := hmatch
    simp only [hvzkHonestOut, hvzkSimOut]
    rw [if_pos (⟨hz, hr0⟩ : _ ∧ _), if_pos (⟨hct0, hw⟩ : _ ∧ _), if_pos hz, ← hm1, ← hm2]
  · simp [hvzkHonestOut, hz]

/-! ### The quantitative bound and the headline statement -/

/-- The honest prover's *extra-rejection mass* relative to the simulator's single
`‖z‖∞ < γ₁ − β` gate, for a fixed key pair: the probability over the honest randomness
`(y, c̃)` that the response gate passes but at least one of the three secret-dependent gates —
`‖LowBits(w − c·s₂)‖∞ < γ₂ − β`, `‖c·t₀‖∞ < γ₂`, `hintWeight h ≤ ω` — fails. On this event the
honest prover aborts while the simulator emits a transcript; everywhere else the two
distributions coincide, so this mass is exactly the total-variation distance. -/
noncomputable def hvzkBadMass (pk : PublicKey p prims) (sk : SecretKey p) : ℝ≥0∞ :=
  Pr[= true | do
    let y ← $ᵗ (RqVec p.l)
    let cTilde ← $ᵗ (CommitHashBytes p)
    let c := prims.sampleInBall cTilde
    let w := prims.expandA pk.rho * y
    let z := y + c • sk.s1
    let r0 := prims.lowBitsVec (w - c • sk.s2)
    let ct0 := c • sk.t0
    let h := prims.makeHintVec (-ct0) (w - c • sk.s2 + ct0)
    return decide (polyVecNorm z < p.gamma1 - p.beta ∧
      ¬(polyVecNorm r0 < p.gamma2 - p.beta ∧ polyVecNorm ct0 < p.gamma2 ∧
        prims.hintWeight h ≤ p.omega))]

omit [DecidableEq prims.High] in
/-- The extra-rejection mass is a probability. -/
lemma hvzkBadMass_le_one (pk : PublicKey p prims) (sk : SecretKey p) :
    hvzkBadMass p prims pk sk ≤ 1 := by
  unfold hvzkBadMass; exact probOutput_le_one

omit [DecidableEq prims.High] in
/-- `hvzkBadMass` over the simulator's `(c̃, z)` randomness: transporting the honest `(y, c̃)`
draw through the `y ↦ y + c·s₁` shift (`evalDist_honest_pregate`) re-expresses the
extra-rejection mass as the probability that `hvzkBadIndicator` fires on a direct draw. -/
lemma hvzkBadMass_eq_probOutput_indicator (pk : PublicKey p prims) (sk : SecretKey p) :
    hvzkBadMass p prims pk sk =
      Pr[= true | do
        let cTilde ← $ᵗ (CommitHashBytes p)
        let z ← $ᵗ (RqVec p.l)
        return hvzkBadIndicator p prims pk sk cTilde z] := by
  have hnorm : (do
      let y ← $ᵗ (RqVec p.l)
      let cTilde ← $ᵗ (CommitHashBytes p)
      let c := prims.sampleInBall cTilde
      let w := prims.expandA pk.rho * y
      let z := y + c • sk.s1
      let r0 := prims.lowBitsVec (w - c • sk.s2)
      let ct0 := c • sk.t0
      let h := prims.makeHintVec (-ct0) (w - c • sk.s2 + ct0)
      return decide (polyVecNorm z < p.gamma1 - p.beta ∧
        ¬(polyVecNorm r0 < p.gamma2 - p.beta ∧ polyVecNorm ct0 < p.gamma2 ∧
          prims.hintWeight h ≤ p.omega)) : ProbComp Bool) =
      ($ᵗ (RqVec p.l)) >>= fun y => ($ᵗ (CommitHashBytes p)) >>= fun cTilde =>
        (fun cT zv => (pure (hvzkBadIndicator p prims pk sk cT zv) : ProbComp Bool))
          cTilde (y + prims.sampleInBall cTilde • sk.s1) := by
    refine bind_congr fun y => bind_congr fun cTilde => ?_
    simp only [hvzkBadIndicator, rqVec_add_sub_cancel]
  have hdist : 𝒟[($ᵗ (RqVec p.l)) >>= fun y => ($ᵗ (CommitHashBytes p)) >>= fun cTilde =>
      (pure (hvzkBadIndicator p prims pk sk cTilde
        (y + prims.sampleInBall cTilde • sk.s1)) : ProbComp Bool)] =
      𝒟[do
        let cTilde ← $ᵗ (CommitHashBytes p)
        let z ← $ᵗ (RqVec p.l)
        return hvzkBadIndicator p prims pk sk cTilde z] :=
    evalDist_honest_pregate p prims sk
      (fun cT zv => (pure (hvzkBadIndicator p prims pk sk cT zv) : ProbComp Bool))
  unfold hvzkBadMass
  rw [hnorm]
  simp only [probOutput_def]
  rw [hdist]

/-- The quantitative HVZK bound for `hvzkSimulatorReal`: the supremum over honestly generated
key pairs of the extra-rejection mass `hvzkBadMass`. Taking the supremum over seeds makes the
bound a single real number valid for every key pair satisfying `validKeyPair`, as required by
`IdenSchemeWithAbort.HVZK`. -/
noncomputable def hvzkBoundReal : ℝ :=
  (⨆ seed : Bytes 32, hvzkBadMass p prims
    (keyGenFromSeed p prims seed).1 (keyGenFromSeed p prims seed).2).toReal

/-- **Honest-verifier zero-knowledge for the ML-DSA identification scheme.** The transcript
distribution of `hvzkSimulatorReal` is within total-variation distance `hvzkBoundReal` of the
honest transcript distribution, for every valid key pair.

Unlike a `ζ_zk = 0` claim for a single-gate simulator (see the module docstring), this
statement is sound: the simulator reproduces the honest transcript pointwise on the accept
event, so the only discrepancy between the two distributions is the honest prover's
extra-rejection mass, which is what `hvzkBoundReal` measures. -/
theorem idsWithAbort_hvzk_real (h_laws : Primitives.Laws prims nttOps) :
    (identificationScheme p prims).HVZK (hvzkSimulatorReal p prims)
      (hvzkBoundReal p prims) := by
  intro pk sk hrel
  obtain ⟨seed, hkeygen⟩ := (validKeyPair_eq_true_iff p prims pk sk).mp hrel
  -- The coupling over the shared `(c̃, z)` draw: the honest and simulated continuations are
  -- deterministic and agree off the gate-mismatch event (`hvzkHonestOut_eq_gated_of_not_bad`),
  -- so `tvDist ≤ Pr[gate mismatch]` by `tvDist_bind_left_event_le`.
  have heq : ∀ a : CommitHashBytes p × RqVec p.l,
      ¬ hvzkBadIndicator p prims pk sk a.1 a.2 = true →
      𝒟[(pure (hvzkHonestOut p prims pk sk a.1 a.2) :
        ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims)))] =
      𝒟[(pure (if polyVecNorm a.2 < p.gamma1 - p.beta
          then some (hvzkSimOut p prims pk a.1 a.2) else none) :
        ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims)))] :=
    fun a hbad => congrArg
      (fun o => 𝒟[(pure o :
        ProbComp (Option (Commitment p prims × CommitHashBytes p × Response p prims)))])
      (hvzkHonestOut_eq_gated_of_not_bad p prims h_laws seed hkeygen a.1 a.2 hbad)
  have hb := tvDist_bind_left_event_le
    (do
      let cTilde ← $ᵗ (CommitHashBytes p)
      let z ← $ᵗ (RqVec p.l)
      return (cTilde, z))
    (fun a => pure (hvzkHonestOut p prims pk sk a.1 a.2))
    (fun a => pure (if polyVecNorm a.2 < p.gamma1 - p.beta
      then some (hvzkSimOut p prims pk a.1 a.2) else none))
    (fun a : CommitHashBytes p × RqVec p.l =>
      hvzkBadIndicator p prims pk sk a.1 a.2 = true)
    (fun a hbad => by exact heq a hbad)
  -- Identify the bound computations with the honest execution and the simulator.
  have hbindHon : (do
      let cTilde ← $ᵗ (CommitHashBytes p)
      let z ← $ᵗ (RqVec p.l)
      return hvzkHonestOut p prims pk sk cTilde z) =
      (do
        let cTilde ← $ᵗ (CommitHashBytes p)
        let z ← $ᵗ (RqVec p.l)
        return (cTilde, z)) >>= fun a => pure (hvzkHonestOut p prims pk sk a.1 a.2) := by
    simp only [bind_assoc, pure_bind]
  have hbindSim : hvzkSimulatorReal p prims pk =
      (do
        let cTilde ← $ᵗ (CommitHashBytes p)
        let z ← $ᵗ (RqVec p.l)
        return (cTilde, z)) >>= fun a => pure (if polyVecNorm a.2 < p.gamma1 - p.beta
          then some (hvzkSimOut p prims pk a.1 a.2) else none) := by
    rw [hvzkSimulatorReal_eq_gated p prims pk]
    simp only [bind_assoc, pure_bind]
  rw [← hbindSim] at hb
  have hgoal : tvDist ((identificationScheme p prims).honestExecution pk sk)
      (hvzkSimulatorReal p prims pk) ≤
      Pr[fun a : CommitHashBytes p × RqVec p.l =>
        hvzkBadIndicator p prims pk sk a.1 a.2 = true | do
          let cTilde ← $ᵗ (CommitHashBytes p)
          let z ← $ᵗ (RqVec p.l)
          return (cTilde, z)].toReal := by
    refine le_of_eq_of_le ?_ hb
    unfold tvDist
    rw [evalDist_honestExecution_eq_gated p prims pk sk, hbindHon]
  refine le_trans hgoal ?_
  -- The mismatch probability is the extra-rejection mass, bounded by its supremum over seeds.
  have hmass : Pr[fun a : CommitHashBytes p × RqVec p.l =>
      hvzkBadIndicator p prims pk sk a.1 a.2 = true | do
        let cTilde ← $ᵗ (CommitHashBytes p)
        let z ← $ᵗ (RqVec p.l)
        return (cTilde, z)] = hvzkBadMass p prims pk sk := by
    rw [hvzkBadMass_eq_probOutput_indicator p prims pk sk]
    have hmap : (do
        let cTilde ← $ᵗ (CommitHashBytes p)
        let z ← $ᵗ (RqVec p.l)
        return hvzkBadIndicator p prims pk sk cTilde z) =
        (fun a : CommitHashBytes p × RqVec p.l => hvzkBadIndicator p prims pk sk a.1 a.2) <$>
          (do
            let cTilde ← $ᵗ (CommitHashBytes p)
            let z ← $ᵗ (RqVec p.l)
            return (cTilde, z)) := by
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
    rw [hmap, ← probEvent_eq_eq_probOutput, probEvent_map]
    rfl
  rw [hmass]
  unfold hvzkBoundReal
  refine ENNReal.toReal_mono ?_ ?_
  · exact ne_top_of_le_ne_top one_ne_top
      (iSup_le fun s => hvzkBadMass_le_one p prims _ _)
  · have h := le_iSup (fun s : Bytes 32 => hvzkBadMass p prims
      (keyGenFromSeed p prims s).1 (keyGenFromSeed p prims s).2) seed
    rwa [hkeygen] at h

/-- Honest-verifier zero-knowledge for the ML-DSA identification scheme, existential form:
some simulator achieves some nonnegative total-variation bound. Witnessed by the concrete
simulator `hvzkSimulatorReal` with the extra-rejection-mass bound `hvzkBoundReal`
(`idsWithAbort_hvzk_real`); the bound is nonnegative as the real projection of a probability
mass. -/
theorem idsWithAbort_hvzk (h_laws : Primitives.Laws prims nttOps) :
    ∃ sim ζ_zk, 0 ≤ ζ_zk ∧ (identificationScheme p prims).HVZK sim ζ_zk :=
  ⟨hvzkSimulatorReal p prims, hvzkBoundReal p prims, ENNReal.toReal_nonneg,
    idsWithAbort_hvzk_real p prims h_laws⟩

end RealHVZK

end MLDSA
