/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub, Alexander Hicks
-/

module
public import LatticeCrypto.Falcon.Scheme

/-!
# Falcon Correctness

This file proves the abstract signing/verification correctness theorem for Falcon:
if the fuel-bounded signer `Falcon.sign` returns a signature, then the abstract verifier
`Falcon.verify` accepts it (`verify_sign_correct`), given that the codec round-trips and that
the trapdoor sampler lands on the coset of its target.

`LatticeCrypto.Falcon.Coset` reduces the coset condition to a lattice-point condition on the
primitives, and the concrete instances discharge both hypotheses in
`Extern/Falcon/SignCorrectness.lean`. The security theorems live in
`LatticeCrypto.Falcon.Security`.
-/

public section

open OracleComp OracleSpec

namespace Falcon

variable (p : Params) (prims : Primitives p)

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

end Falcon
