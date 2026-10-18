/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import LatticeCrypto.Falcon.Scheme
public import LatticeCrypto.HardnessAssumptions.ShortIntegerSolution
public import VCVio.OracleComp.Constructions.SampleableType.Basic
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.EvalDist.Measure

/-!
# Falcon Security

This file collects the security-facing definitions for the Falcon signature scheme.

## Correctness

`verify(pk, m, sign(sk, m)) = true` whenever:
1. The key pair is valid (NTRU equation holds, `h = g · f⁻¹ mod q`).
2. Signing does not abort (norm check passes, compression succeeds).

## EUF-CMA Security

Falcon is the GPV hash-and-sign construction instantiated with `falconPSF`, so its
EUF-CMA security is read off the generic GPV endpoints
`GPVHashAndSign.euf_cma_split_bound_of_queryBound` and
`GPVHashAndSign.euf_cma_collision_bound_of_queryBound`. They bound the unforgeability
advantage of `falconSignatureAlg` by the PSF collision advantage of the GPV reduction, an
exact-match term, and the salt-collision term `(qSign + qHash + 1)² / (2 · |Salt|)`, under
trapdoor-sampler correctness and regularity at the chosen forward sampler. This file
provides the Falcon-side collision target `ntruPSFCollisionProblem` for the collision branch,
together with the kernel-vector formulation `ntruSISProblem`.

The published concrete bounds ([FGdG+25] Theorem 1, refined by [Jia+26]) additionally
charge the finite-precision loss of `ffSampling` through Rényi divergences
`r_p = R_{a_p}(PreSmp ‖ D_{Λ,s,c})` and `r_u = R_{a_u}(U(R_q) ‖ Q_h)`; with exact arithmetic
`r_p = 1`. For a 320-bit salt their salt-collision term `Q_s · (C_s + Q_H) / 2^k` is
negligible, as is the birthday term above.

## References

- [FGdG+25]: Fouque, Gajland, de Groote, Janneck, Kiltz. "A Closer Look at Falcon."
  ePrint 2024/1769, updated 2025. First concrete security proof for Falcon+.
- [Jia+26]: Jia, Zhang, Yu, Tang. "Revisiting the Concrete Security of Falcon-type
  Signatures." ePrint 2026/096. Basis-specific analysis eliminating the 7-bit loss.
- [TWFalcon]: Halmans et al. "TWFalcon: Triple-Word Arithmetic for Falcon."
  ePrint 2025/1991. Shows binary64 misses the published Rényi threshold.
- GPV08: Gentry, Peikert, Vaikuntanathan. STOC 2008, Propositions 6.1–6.2.
- [Pre17]: Prest. ASIACRYPT 2017. Rényi-based precision analysis for Klein's sampler.
-/

@[expose] public section


open OracleComp OracleSpec ENNReal

namespace Falcon

variable (p : Params) (prims : Primitives p)

/-! ### Correctness -/

/-- **Falcon verification correctness, conditional on the sampler landing on the coset.**

If the fuel-bounded signer returns a signature, `verify` accepts it, given two facts about the
primitives at the honest key:

1. `hcompress`: the codec round-trips (the `compress_decompress` law of `Primitives.Laws`,
   a theorem for the concrete codec: `Falcon.Concrete.decompress_compress`);
2. `hpreimage`: every output of the trapdoor sampler is a preimage of its target,
   `s₁ + s₂ · h = c`.

Hypothesis 2 is the coset obligation of the FFT pipeline. `fromFFTPreimage` rounds an inverse
FFT and returns `(c − v₀, −v₁)`. For a valid basis, a sufficient condition is that the rounded
`v` equals the integer lattice point `z · B`; coordinatewise error strictly below `1/2` before
rounding establishes that condition. The coset identity itself is the hypothesis here, so exact
FFT arithmetic and a certified numerical implementation can discharge it separately. Neither the
NTRU equation nor `validKeyPair` is needed in this theorem: the signer emits only attempts that
passed the norm check, and that check is `verify`'s own. -/
theorem verify_sign_correct (pk : PublicKey p) (sk : SecretKey p) (msg : List Byte)
    (maxAttempts : ℕ) (sig : Signature)
    (hcompress : ∀ (s : IntPoly p.n) (slen : ℕ) (bytes : List Byte),
      prims.compress s slen = some bytes → prims.decompress bytes slen = some s)
    (hpreimage : ∀ (c : Rq p.n) (x : Rq p.n × Rq p.n),
      x ∈ support ((falconPSF p prims).trapdoorSample pk sk c) →
        (falconPSF p prims).eval pk x = c)
    (hsig : some sig ∈ support (sign p prims pk sk msg maxAttempts)) :
    verify p prims pk msg sig = true := by
  induction maxAttempts with
  | zero =>
    simp only [sign, support_pure, Set.mem_singleton_iff] at hsig
    exact absurd hsig (by simp)
  | succ k ih =>
    rw [sign, mem_support_bind_iff] at hsig
    obtain ⟨salt, _hsalt, hsig⟩ := hsig
    rw [mem_support_bind_iff] at hsig
    obtain ⟨r, hr, hsig⟩ := hsig
    match r, hr, hsig with
    | none, _hr, hsig => exact ih hsig
    | some (s₁, s₂), hr, hsig =>
      dsimp only at hsig
      cases hcomp : prims.compress (rqToIntPolyCentered s₂) p.sbytelen with
      | none =>
        rw [hcomp] at hsig
        exact ih hsig
      | some comp =>
        rw [hcomp] at hsig
        simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hsig
        subst hsig
        -- The accepting attempt is a `trapdoorSample` output that passed the norm check.
        set c := prims.hashToPointForPublicKey pk.h salt msg with hc
        rw [signAttempt, mem_support_bind_iff] at hr
        obtain ⟨x, hx, hr⟩ := hr
        have hshort_eval :
            (s₁, s₂) ∈ support ((falconPSF p prims).trapdoorSample pk sk c) ∧
              (falconPSF p prims).isShort (s₁, s₂) = true := by
          by_cases hshort : (falconPSF p prims).isShort x = true
          · rw [ite_eq_left hshort, support_pure, Set.mem_singleton_iff, Option.some.injEq] at hr
            subst hr
            exact ⟨hx, hshort⟩
          · rw [ite_eq_right hshort, support_pure, Set.mem_singleton_iff] at hr
            exact absurd hr (by simp)
        obtain ⟨hmem, hshort⟩ := hshort_eval
        have heval : (falconPSF p prims).eval pk (s₁, s₂) = c := hpreimage c (s₁, s₂) hmem
        -- `verify` decompresses to the same `s₂`, recomputes the same `s₁`, and runs the norm
        -- check the attempt already passed.
        have hdec := hcompress _ _ _ hcomp
        unfold verify
        simp only [hdec]
        rw [toRq_rqToIntPolyCentered]
        have hs1 : c - negacyclicMul s₂ pk.h = s₁ := by
          rw [← heval]
          change s₁ + negacyclicMul s₂ pk.h - negacyclicMul s₂ pk.h = s₁
          apply LatticeCrypto.Poly.ext_get_eq
          intro i
          calc (s₁ + negacyclicMul s₂ pk.h - negacyclicMul s₂ pk.h).get i
              = (s₁ + negacyclicMul s₂ pk.h).get i - (negacyclicMul s₂ pk.h).get i :=
                LatticeCrypto.NegacyclicRing.coeff_sub (coeffRing p.n) _ _ i
            _ = s₁.get i + (negacyclicMul s₂ pk.h).get i - (negacyclicMul s₂ pk.h).get i :=
                congrArg (· - (negacyclicMul s₂ pk.h).get i)
                  (LatticeCrypto.NegacyclicRing.coeff_add (coeffRing p.n) _ _ i)
            _ = s₁.get i := add_sub_cancel_right _ _
        change decide (pairL2NormSq (c - negacyclicMul s₂ pk.h) s₂ ≤ p.betaSquared) = true
        rw [hs1]
        exact hshort

/-! ### NTRU-SIS Hardness Assumption -/

/-- The NTRU-SIS problem: given `h ∈ R_q` (the Falcon public key), find short
`(s₁, s₂) ∈ R_q²` satisfying `s₁ + s₂ · h = 0 mod q` with
`‖(s₁, s₂)‖₂² ≤ ⌊β²⌋`.

This is the lattice problem underlying Falcon's security. It is an instance of
the generic SIS problem where the matrix is the single-row matrix `[I | h]`
over the cyclotomic ring `R_q = ℤ_q[x]/(x^n + 1)`. -/
noncomputable def ntruSISProblem :
    SIS.Problem (Rq p.n) (Rq p.n × Rq p.n) where
  sampleChallenge := $ᵗ (Rq p.n)
  isValid h x :=
    decide (x ≠ (0, 0)) &&
    decide (pairL2NormSq x.1 x.2 ≤ p.betaSquared) &&
    decide (x.1 + negacyclicMul x.2 h = 0)

/-- The direct Falcon PSF collision problem induced by the generic GPV reduction.

The challenger samples a Falcon public key from the same key distribution used by the
signature scheme, and the adversary must produce two distinct short preimages with the
same image under the Falcon PSF `(s₁, s₂) ↦ s₁ + s₂ · h`.

This is the immediate hardness target of the collision-style GPV bound before any further
translation to a kernel-vector NTRU-SIS formulation. -/
noncomputable def ntruPSFCollisionProblem
    (hr : GenerableRelation (PublicKey p) (SecretKey p) (validKeyPair p)) :
    SIS.Problem (PublicKey p) ((Rq p.n × Rq p.n) × (Rq p.n × Rq p.n)) where
  sampleChallenge := do
    let (pk, _) ← hr.gen
    pure pk
  isValid pk xs :=
    decide (xs.1 ≠ xs.2) &&
    decide ((falconPSF p prims).eval pk xs.1 = (falconPSF p prims).eval pk xs.2) &&
    (falconPSF p prims).isShort xs.1 &&
    (falconPSF p prims).isShort xs.2

end Falcon
