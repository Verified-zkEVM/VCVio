/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Falcon.Scheme

/-!
# Falcon Correctness

This file proves the abstract signing/verification correctness theorem for Falcon:
if the fuel-bounded signer returns a signature, then the abstract verifier accepts it.
-/

open OracleComp OracleSpec

namespace Falcon

variable (p : Params) (prims : Primitives p)

/-! ## Signing and Verification -/

/-- Falcon verification correctness: if the key pair is valid and signing produces a
signature (does not abort), then verification accepts.

The proof proceeds by induction on `maxAttempts` over the rejection loop:

1. The compress/decompress roundtrip (`h_laws.compress_decompress` + `toRq_rqToIntPolyCentered`)
   makes `verify` recover exactly the `s₂` that signing compressed.
2. PSF correctness (`falconPSF_eval_trapdoorSample`) gives `s₁ + s₂ · h = c`, so `verify`'s
   recomputed `s₁ = c - s₂ · h` matches the sampled `s₁`.
3. The `isShort` flag that the accepting attempt passed is exactly `verify`'s `ℓ₂` norm check.

This is conditional correctness: validity of the key pair (`_hvalid`) is *not* needed — `hsig`
already ranges only over the `some`-branch of the real `Falcon.sign` rejection loop (an attempt
where both `isShort` and `compress = some` held). Note the two-world gap (UN-1): this concerns
`Falcon.verify`, not the GPV verify the EUF-CMA theorems use. See `docs/agents/falcon-review.md`
(UN-1 / B2). -/
theorem verify_sign_correct (pk : PublicKey p) (sk : SecretKey p)
    (_hvalid : validKeyPair p pk sk = true)
    (msg : List Byte) (maxAttempts : ℕ) (sig : Signature)
    (h_laws : Primitives.Laws prims)
    (hsig : some sig ∈ support (Falcon.sign p prims pk sk msg maxAttempts)) :
    Falcon.verify p prims pk msg sig = true := by
  induction maxAttempts with
  | zero =>
    simp only [Falcon.sign, support_pure, Set.mem_singleton_iff] at hsig
    exact absurd hsig (by simp)
  | succ k ih =>
    rw [Falcon.sign, mem_support_bind_iff] at hsig
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
        -- Recover from `signAttempt` membership: the accepting attempt is a `trapdoorSample`
        -- output that passed the `isShort` check.
        set c := prims.hashToPointForPublicKey pk.h salt msg with hc
        rw [signAttempt, mem_support_bind_iff] at hr
        obtain ⟨x, hx, hr⟩ := hr
        have hshort_eval :
            (s₁, s₂) ∈ support ((falconPSF p prims).trapdoorSample pk sk c) ∧
              (falconPSF p prims).isShort (s₁, s₂) = true := by
          by_cases hshort : (falconPSF p prims).isShort x = true
          · rw [if_pos hshort, support_pure, Set.mem_singleton_iff, Option.some.injEq] at hr
            subst hr
            exact ⟨hx, hshort⟩
          · rw [if_neg hshort, support_pure, Set.mem_singleton_iff] at hr
            exact absurd hr (by simp)
        obtain ⟨hmem, hshort⟩ := hshort_eval
        -- `eval pk (s₁, s₂) = c`, i.e. `s₁ + s₂ · h = c`, holds by construction of the sampler.
        have heval : (falconPSF p prims).eval pk (s₁, s₂) = c :=
          falconPSF_eval_trapdoorSample p prims pk sk c (s₁, s₂) hmem
        -- `verify` decompresses to the same `s₂` and recomputes the same `s₁`, then runs the
        -- same `ℓ₂` check that `isShort` already passed.
        have hdec := h_laws.compress_decompress _ _ _ hcomp
        unfold verify
        simp only [hdec]
        rw [toRq_rqToIntPolyCentered]
        have hs1 : c - negacyclicMul s₂ pk.h = s₁ := by
          rw [← heval]
          change s₁ + negacyclicMul s₂ pk.h - negacyclicMul s₂ pk.h = s₁
          ext i
          simp only [LatticeCrypto.NegacyclicRing.coeff_add,
            LatticeCrypto.NegacyclicRing.coeff_sub]
          ring
        change decide (pairL2NormSq (c - negacyclicMul s₂ pk.h) s₂ ≤ p.betaSquared) = true
        rw [hs1]
        exact hshort

end Falcon
