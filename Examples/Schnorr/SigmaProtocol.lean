/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.SigmaProtocol
public import VCVio.EvalDist.Monad.Branch
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.ProgramLogic.Tactics.Unary
public import VCVio.ProgramLogic.Tactics.Relational

/-!
# Schnorr Σ-protocol

Standard Schnorr Σ-protocol for proof of knowledge of discrete logarithm
over a cyclic group, formalized using `Module F G`. This file is the
σ-protocol layer of the end-to-end EUF-CMA proof for the Schnorr signature
in `Examples/Schnorr/Signature.lean`; everything proven here is fed verbatim into
`FiatShamir.euf_cma_bound`.

## Mathematical setup

- `F` : scalar field (e.g. `ZMod p` for a prime-order group)
- `G` : group of elements with `[AddCommGroup G]` and `[Module F G]`
- `g : G` : fixed public generator

## Protocol

Given public key `pk : G` with witness `sk : F` satisfying `sk • g = pk`:

1. **Commit**: sample `r ← F`, output `(R, r) := (r • g, r)`
2. **Challenge**: receive `c ← F` (full-field challenge)
3. **Respond**: `z = r + c · sk`
4. **Verify**: check `z • g = R + c • pk`

This matches the textbook Schnorr protocol. In multiplicative notation,
verification is `g^z = R · pk^c`.

## What's in this file

| Theorem                              | Plays the role of …
| ------------------------------------ | --------------------------------------
| `sigma_complete`                     | perfect completeness of the σ-protocol
| `sigma_speciallySound`               | the special-soundness extractor
|                                      |     `(z₁ - z₂) · (c₁ - c₂)⁻¹`
| `sigma_hvzk`                         | perfect HVZK (`ζ_zk = 0`)
| `sigma_simCommitPredictability`      | simulator commit-predictability
|                                      |     `β = 1/|F|` (needs the bijection
|                                      |     `· • g : F → G`)
| `sigma_simChalUniformGivenCommit`    | simulator's challenge is conditionally
|                                      |     uniform given the commit

The first three are the textbook Σ-protocol security properties. The last
two are the additional facts the Fiat-Shamir CMA-to-NMA reduction needs to
control the signing-simulator's collisions with the random oracle.

## Sketches

* **Completeness**: trivial from `Module` axioms (`add_smul`, `mul_smul`).
* **Special soundness**: from two accepting transcripts with distinct
  challenges, extract `sk = (z₁ - z₂) · (c₁ - c₂)⁻¹` using field division.
* **HVZK**: simulator picks `c, z ← F`, computes `R = z • g - c • pk`;
  distribution matches via the bijection `r ↦ r + c · sk`.
* **Commit-predictability**: when `· • g : F → G` is a bijection, both
  `r • g` (real) and `z • g - c • pk` (simulator) are uniform on `G`,
  giving probability `1/|G| = 1/|F|` for any specific commit.
* **Conditional challenge uniformity**: in the closed form
  `(r • g, c, r + c · sk)` with `r, c ← $ᵗ F` independent, the joint
  marginal on `(commit, chal)` factors as `Pr[commit] · 1/|F|`.
-/

@[expose] public section

open OracleSpec OracleComp SigmaProtocol
open scoped ENNReal

namespace Schnorr

variable (F : Type) [Field F] [SampleableType F]
variable (G : Type) [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]

/-- Standard Schnorr Σ-protocol for knowledge of discrete log.
Challenge space is the full scalar field `F`. -/
def sigma (g : G) : SigmaProtocol G F G F F F
    (fun pk sk => decide (sk • g = pk)) where
  commit _pk _sk := do
    let r ← $ᵗ F
    return (r • g, r)
  respond _pk sk sc c := pure (sc + c * sk)
  verify pk R c z := decide (z • g = R + c • pk)
  sim _pk := $ᵗ G
  extract c₁ z₁ c₂ z₂ := pure ((z₁ - z₂) * (c₁ - c₂)⁻¹)

/-! ## Textbook Σ-protocol security properties

The three classical Σ-protocol properties: completeness, special soundness,
and (perfect) honest-verifier zero-knowledge. -/

/-- Perfect completeness: an honest prover with a valid witness always produces
an accepting transcript. Follows from `add_smul` and `mul_smul`. -/
theorem sigma_complete (g : G) :
    (sigma F G g).PerfectlyComplete := by
  intro pk sk h
  rw [← prEvent_eq_evalDist_singleton]
  have h_eq : sk • g = pk := of_decide_eq_true h
  simp only [sigma, monad_norm]
  have hverify : ∀ (r c : F), (r + c * sk) • g = r • g + c • pk := by
    intro r c; rw [add_smul, mul_smul, h_eq]
  simp [hverify]

/-- Special soundness: from two accepting transcripts `(R, c₁, z₁)` and `(R, c₂, z₂)` with
`c₁ ≠ c₂`, the extracted witness `(z₁ - z₂) * (c₁ - c₂)⁻¹` satisfies the relation. -/
theorem sigma_speciallySound (g : G) :
    SpeciallySound (sigma F G g) := by
  intro pk R c₁ c₂ z₁ z₂ h_ne h_v1 h_v2 w h_w
  dsimp [sigma] at *
  simp only [Set.mem_singleton_iff] at h_w
  subst h_w
  simp only [decide_eq_true_eq] at h_v1 h_v2 ⊢
  have h_sub : (z₁ - z₂) • g = (c₁ - c₂) • pk := by
    rw [sub_smul, sub_smul, h_v1, h_v2, add_sub_add_left_eq_sub]
  have h_ne' : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr h_ne
  calc ((z₁ - z₂) * (c₁ - c₂)⁻¹) • g
      = (c₁ - c₂)⁻¹ • ((z₁ - z₂) • g) := by rw [mul_comm, mul_smul]
    _ = (c₁ - c₂)⁻¹ • ((c₁ - c₂) • pk) := by rw [h_sub]
    _ = ((c₁ - c₂)⁻¹ * (c₁ - c₂)) • pk := by rw [← mul_smul]
    _ = (1 : F) • pk := by rw [inv_mul_cancel₀ h_ne']
    _ = pk := one_smul F pk

/-- Full transcript simulator: pick `c, z ← F`, compute commitment from verification equation. -/
def simTranscript (g : G) (pk : G) : ProbComp (G × F × F) := do
  let c ← $ᵗ F
  let z ← $ᵗ F
  return (z • g - c • pk, c, z)

/-- Closed-form for the Schnorr `realTranscript`: the real transcript is the joint
distribution of `(r • g, c, r + c * sk)` where `r, c ← $ᵗ F` are sampled *independently*.
This is the form in which the commitment `r • g` and the challenge `c` are literally
independent (by sampling order), making conditional uniformity trivial. -/
private lemma realTranscript_eq_indep (g : G) (pk : G) (sk : F) :
    (sigma F G g).realTranscript pk sk =
      (do
        let r ← $ᵗ F
        let c ← $ᵗ F
        pure ((r • g, c, r + c * sk) : G × F × F)) := by
  simp only [ChallengeVerifyProtocol.realTranscript, sigma, monad_norm]

open OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational in
/-- Honest-verifier zero-knowledge: the real transcript distribution equals the simulated one.
The proof swaps the two independent samples of the real transcript and reindexes the
response by the bijection `r ↦ r + c * sk`. -/
theorem sigma_hvzk (g : G) :
    (sigma F G g).PerfectHVZK (simTranscript F G g) := by
  intro pk sk h_sk
  have h_eq : sk • g = pk := of_decide_eq_true h_sk
  let : MeasurableSpace (G × F × F) := ⊤
  refine EvalDistEq.of_evalDist_eq ?_
  calc 𝒟[(sigma F G g).realTranscript pk sk]
      = 𝒟[do
          let c ← $ᵗ F
          let r ← $ᵗ F
          pure (((r + c * sk) • g - c • pk, c, r + c * sk) : G × F × F)] := by
        rw [realTranscript_eq_indep, OracleComp.evalDist_bind_bind_swap]
        simp [← h_eq, add_smul, mul_smul]
    _ = 𝒟[simTranscript F G g pk] := by
        unfold simTranscript
        refine evalDist_eq_of_relTriple_eqRel (spec₁ := unifSpec) (spec₂ := unifSpec) ?_
        rvcstep
        intro c _ hc; subst hc
        rvcstep using (· + c * sk)
        exact ⟨fun _ _ h => add_right_cancel h, fun z => ⟨z - c * sk, sub_add_cancel z _⟩⟩

/-! ## Companion facts for the Fiat-Shamir reduction

Two additional properties that the FS CMA-to-NMA reduction needs (on top of
HVZK) to bound the probability that the signing-simulator collides with the
random oracle when programming a hash entry. They concern the shape of the
*simulator transcript distribution*, not the σ-protocol itself. -/

/-- **Simulator commit-predictability for Schnorr.** With the standard bijection
hypothesis `hg : Function.Bijective (· • g : F → G)` (`F` acts simply transitively on
`G`, so `g` generates the group), the simulator's commit marginal is uniform over `G`,
giving predictability bound `β = 1/|F|` (equivalently `1/|G|`).

This is the `β` parameter consumed by `FiatShamir.euf_cma_bound`: it controls the
`qS · (qS + qH) · β` collision term in the CMA-to-NMA reduction, where each
simulator-programmed hash entry collides with the adversary's view with probability
at most `β`.

Proof: for any fixed challenge `c`, the response map `z ↦ z • g - c • pk : F → G` is
a bijection (composition of `· • g` with translation), so `(z • g - c • pk)` is uniform
on `G` when `z ← $ᵗ F` and hits any specific commitment with probability
`1/|G| = 1/|F|`. The bound survives averaging over `c ← $ᵗ F`. -/
theorem sigma_simCommitPredictability [Fintype F] (g : G)
    (hg : Function.Bijective (· • g : F → G)) :
    (sigma F G g).simCommitPredictability (simTranscript F G g)
      ((Fintype.card F : ℝ≥0∞)⁻¹) := by
  classical
  let : Fintype G := Fintype.ofBijective _ hg
  intro pk c₀
  have hcard_FG : Fintype.card G = Fintype.card F := (Fintype.card_of_bijective hg).symm
  have h_inner : ∀ c : F,
      Pr{let z ← $ᵗ F}[z • g - c • pk = c₀] = (Fintype.card F : ℝ≥0∞)⁻¹ := fun c =>
    (SampleableType.prEvent_uniformSample_comp_of_bijective
      (f := fun z : F => z • g - c • pk) ((Equiv.subRight (c • pk)).bijective.comp hg)
      (· = c₀)).trans
      ((SampleableType.prEvent_uniformSample_eq_singleton c₀).trans (by rw [hcard_FG]))
  refine prEvent_bind_le_of_forall_le ($ᵗ F) _ (fun t : G × F × F => t.1 = c₀) fun c => ?_
  simpa only [prEvent_norm] using (h_inner c).le

/-- **Simulator-challenge uniformity given commit, for Schnorr.** For any commit value
`c₀ : G` and challenge value `ch₀ : F`, the simulator's joint marginal on
`(commit, chal)` factors as `Pr[commit = c₀] · (1/|F|)`.

This is the strengthening of commit-predictability that the FS reduction's joint
coupling needs: it asserts that conditional on any commit value, the simulator's
challenge is uniform on `F`. The proof reduces to the explicit independent product
`(do r ← $ᵗ F; c ← $ᵗ F; pure (r • g, c, r + c · sk))` via perfect HVZK and the
closed form `realTranscript_eq_indep`; in that form the commit `r • g` and challenge
`c` are literally independent (by sampling order), so both events factor through
`Pr{let r ← $ᵗ F}[r • g = c₀]`. -/
theorem sigma_simChalUniformGivenCommit [Fintype F] (g : G) :
    (sigma F G g).simChalUniformGivenCommit (simTranscript F G g) := by
  classical
  intro pk sk hsk c₀ ch₀
  have hHVZK := sigma_hvzk F G g pk sk hsk
  rw [← hHVZK.prEvent_eq, ← hHVZK.prEvent_eq, realTranscript_eq_indep]
  let cont : F → ProbComp (G × F × F) := fun r => do
    let c ← $ᵗ F
    pure (r • g, c, r + c * sk)
  have hjoint := prEvent_bind_eq_mul_of_ite ($ᵗ F) cont (fun r => r • g = c₀)
    (fun t => t.1 = c₀ ∧ t.2.1 = ch₀) ($ᵗ F) (· = ch₀) fun r => by
      by_cases hr : r • g = c₀ <;> simp [cont, hr, prEvent_norm]
  have hmarg := prEvent_bind_eq_mul_of_ite ($ᵗ F) cont (fun r => r • g = c₀)
    (fun t => t.1 = c₀) (pure () : ProbComp Unit) (fun _ => True) fun r => by
      by_cases hr : r • g = c₀ <;> simp [cont, hr, prEvent_norm]
  simp only [cont] at hjoint hmarg
  rw [hjoint, hmarg, SampleableType.prEvent_uniformSample_eq_singleton]
  simp

end Schnorr
