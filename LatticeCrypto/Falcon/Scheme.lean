/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Falcon.Primitives
import VCVio.CryptoFoundations.GPVHashAndSign
import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.Coercions.Add

/-!
# Falcon Signature Scheme

This file defines the core Falcon signature scheme: key types and validity, the one-shot
signing core (`signAttempt`), and verification (`verify`), together with the bridge to the
generic GPV hash-and-sign framework via a `PreimageSampleableFunction` instantiation. Key
generation and the full fresh-salt retry-loop signer are realized in
`LatticeCrypto.Falcon.Concrete`.

## Architecture

The Falcon scheme is an instantiation of the GPV hash-and-sign framework over NTRU lattices:

- **Public key**: `h = g · f⁻¹ mod q` (a single polynomial in `R_q`).
- **Secret key**: short integer polynomials `(f, g, F, G)` satisfying the NTRU equation
  `fG - gF = q`, plus the precomputed Falcon tree for fast sampling.
- **Signing** (Falcon+): on each attempt, sample a fresh 40-byte salt `r`, hash
  `c = HashToPoint(r, pk, message)` to a target in `R_q`, use `ffSampling` with the secret
  basis to find a short preimage `(s₁, s₂)` with `s₁ + s₂ · h = c mod q`, then check the
  norm bound and compress. Retry with a new salt on failure.
- **Verification**: recompute `c`, recover `s₁ = c - s₂ · h mod q`, check
  `‖(s₁, s₂)‖₂² ≤ ⌊β²⌋`.

The signing flow follows the Falcon+ convention (fresh salt per retry, pk-bound hashing),
matching the concrete executable signer in `LatticeCrypto.Falcon.Concrete.Sign`.

## References

- Falcon specification v1.2, Algorithms 1–16
- FIPS 206 (FN-DSA) draft
- GPV08: Gentry, Peikert, Vaikuntanathan. STOC 2008.
-/


open OracleComp OracleSpec

namespace Falcon

variable (p : Params) (prims : Primitives p)

/-! ### Key Types -/

/-- The Falcon public key: a single polynomial `h ∈ R_q` where `h = g · f⁻¹ mod q`. -/
structure PublicKey where
  h : Rq p.n

noncomputable instance : DecidableEq (PublicKey p) := by
  intro a b
  cases a with
  | mk h1 =>
    cases b with
    | mk h2 =>
      simpa using (inferInstanceAs (Decidable (h1 = h2)))

/-- The Falcon secret key: the short NTRU basis polynomials `(f, g, F, G)` over `ℤ`,
plus the precomputed Falcon tree for efficient signing.

The FFT recursion depth is `p.fftDepth = p.logn - 1`. The tree encodes the normalized
LDL decomposition of the Gram matrix `[[g, -f], [G, -F]]^T · [[g, -f], [G, -F]]`
in packed FFT representation. -/
structure SecretKey where
  f : IntPoly p.n
  g : IntPoly p.n
  capF : IntPoly p.n
  capG : IntPoly p.n
  tree : FalconTree p.fftDepth

/-- A Falcon signature: a 40-byte random salt `r` paired with the compressed
representation of the short polynomial `s₂`. -/
structure Signature where
  salt : Bytes 40
  compressedS2 : List Byte

/-! ### NTRU Equation -/

/-- The NTRU equation over `ℤ[x]/(x^n + 1)`:
  `f · G - g · F = q`
This is the fundamental algebraic relation that the Falcon secret key must satisfy.
It ensures that `[[g, -f], [G, -F]]` forms a basis of the NTRU lattice. -/
def ntruEquation (f g capF capG : IntPoly p.n) : Prop :=
  intPolyMul f capG - intPolyMul g capF = intPolyConst (modulus : ℤ)

/-- Decidable equality reduces the Falcon NTRU equation to decidable polynomial equality. -/
instance (f g capF capG : IntPoly p.n) : Decidable (ntruEquation p f g capF capG) :=
  inferInstanceAs (Decidable (_ = _))

/-- A key pair is valid when:
1. The NTRU equation holds: `fG - gF = q`.
2. The public key satisfies `h = g · f⁻¹ mod q` (i.e., `f · h = g mod q`). -/
noncomputable def validKeyPair (pk : PublicKey p) (sk : SecretKey p) : Bool :=
  decide (ntruEquation p sk.f sk.g sk.capF sk.capG) &&
  decide (negacyclicMul (IntPoly.toRq sk.f) pk.h = IntPoly.toRq sk.g)

@[simp]
theorem validKeyPair_eq_true_iff (pk : PublicKey p) (sk : SecretKey p) :
    validKeyPair p pk sk = true ↔
      ntruEquation p sk.f sk.g sk.capF sk.capG ∧
      negacyclicMul (IntPoly.toRq sk.f) pk.h = IntPoly.toRq sk.g := by
  simp [validKeyPair]

/-! ### GPV Bridge -/

/-- Convert a target `c ∈ R_q` and the secret NTRU basis to an FFT-domain target vector
for `ffSampling`.

This follows Falcon's `fpoly_apply_basis`: interpret `c` as the integer target polynomial
`hm`, take its packed FFT, and form

- `t₀ = (1/q) · FFT(hm) · FFT(-F)`
- `t₁ = (-1/q) · FFT(-f) · FFT(hm)`

where `(f, F)` come from the secret basis `[[g, -f], [G, -F]]`. -/
noncomputable def toFFTTarget (c : Rq p.n) (sk : SecretKey p) :
    FFTPair p.fftDepth :=
  let hmFFT := prims.fftTarget c
  let b01 := prims.fftInt (-sk.f)
  let b11 := prims.fftInt (-sk.capF)
  let invQ : ℝ := (1 : ℝ) / (modulus : ℝ)
  let t₀ := Primitives.scaleFFT invQ (Primitives.mulFFT hmFFT b11)
  let t₁ := Primitives.scaleFFT (-invQ) (Primitives.mulFFT b01 hmFFT)
  (t₀, t₁)

/-- Convert the ffSampling output back to a pair `(s₁, s₂) ∈ R_q × R_q`.

Given the hash target `c`, the public key, the secret basis, and the sampled FFT-domain
vector `z`, this reconstructs `s₂` from the basis (inverse-transform and round), then sets

- `s₂ = -v₁`  where  `v₁ = round(IFFT(-(f·z₀ + F·z₁)))`
- `s₁ = c - s₂ · h`

`s₁` is recomputed from `s₂` (rather than from an independently-rounded `v₀`), so the PSF
identity `s₁ + s₂ · h = c` holds **exactly**. This matches `Falcon.verify` — which stores only
`s₂` and recomputes `s₁` — and the real Falcon / FN-DSA signing flow, and is what makes
`falconPSF.eval (trapdoorSample …) = c` (see `falconPSF_eval_trapdoorSample`). Independent
rounding of a separate `v₀` would break the identity (the rounded `v₀ + v₁ · h ≢ 0 mod q`). -/
noncomputable def fromFFTPreimage (c : Rq p.n) (pk : PublicKey p) (sk : SecretKey p)
    (z : FFTPair p.fftDepth) : Rq p.n × Rq p.n :=
  let v₁FFT := -(Primitives.mulFFT z.1 (prims.fftInt sk.f) +
    Primitives.mulFFT z.2 (prims.fftInt sk.capF))
  let s₂ := -IntPoly.toRq (prims.ifftRound v₁FFT)
  let s₁ := c - negacyclicMul s₂ pk.h
  (s₁, s₂)

/-- Falcon as a `PreimageSampleableFunction`.

The PSF maps `(s₁, s₂) ↦ s₁ + s₂ · h mod q`, the "hash" in the hash-and-sign
paradigm. The trapdoor sampler uses `ffSampling` to find short preimages. The
shortness predicate checks the `ℓ₂` norm bound.

| PSF field | Falcon instantiation |
|---|---|
| `eval pk (s₁, s₂)` | `s₁ + s₂ · h mod q` |
| `trapdoorSample pk sk c` | `ffSampling(...)` producing short `(s₁, s₂)` |
| `isShort (s₁, s₂)` | `‖(s₁, s₂)‖₂² ≤ ⌊β²⌋` |

The trapdoor sampler:
1. Converts target `c` to an FFT-domain vector using the NTRU basis (`toFFTTarget`).
2. Calls `ffSampling` with the Falcon tree to sample a nearby integer lattice point.
3. Converts the result back to `(s₁, s₂) ∈ R_q²` (`fromFFTPreimage`).

The correctness obligation is that the output distribution is close (in Rényi divergence)
to the ideal discrete Gaussian over the NTRU lattice coset. -/
noncomputable def falconPSF : PreimageSampleableFunction
    (PublicKey p) (SecretKey p) (Rq p.n × Rq p.n) (Rq p.n) where
  eval pk x := x.1 + negacyclicMul x.2 pk.h
  trapdoorSample pk sk c := do
    let t := toFFTTarget p prims c sk
    let z ← Primitives.ffSampling prims p.fftDepth t sk.tree
    return fromFFTPreimage p prims c pk sk z
  isShort x := decide (pairL2NormSq x.1 x.2 ≤ p.betaSquared)

/-- The `eval`-half of `PreimageSampleableFunction.Correct` for the Falcon PSF: every output
of `trapdoorSample` is an exact preimage, `eval pk x = c`. This holds *by construction* because
`fromFFTPreimage` sets `s₁ := c - s₂ · h`, so `eval pk (s₁, s₂) = s₁ + s₂ · h = c`.

(The full `Correct` predicate also requires `isShort x = true` for every output; that half is
**not** provable for the raw sampler — `ffSampling` can occasionally produce an over-long vector,
which is why real Falcon retries. Establishing it needs a rejection/retry model for
`trapdoorSample`; see B2 in `docs/agents/falcon-review.md`.) -/
theorem falconPSF_eval_trapdoorSample (pk : PublicKey p) (sk : SecretKey p) (c : Rq p.n) :
    ∀ x ∈ support ((falconPSF p prims).trapdoorSample pk sk c),
      (falconPSF p prims).eval pk x = c := by
  -- For any `s₂`, evaluating the recomputed pair `(c - s₂·h, s₂)` returns `c`.
  have eval_pair : ∀ s₂ : Rq p.n,
      (falconPSF p prims).eval pk (c - negacyclicMul s₂ pk.h, s₂) = c := by
    intro s₂
    change (c - negacyclicMul s₂ pk.h) + negacyclicMul s₂ pk.h = c
    -- `Rq` equalities are coefficient-wise (the bespoke `Sub`/`Add` make `ring`/`abel`
    -- inapplicable on `Rq` directly); reduce to `ZMod` and cancel there.
    ext i
    simp only [LatticeCrypto.NegacyclicRing.coeff_add, LatticeCrypto.NegacyclicRing.coeff_sub]
    ring
  intro x hx
  simp only [falconPSF, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
    exists_prop] at hx
  obtain ⟨z, _, rfl⟩ := hx
  -- `fromFFTPreimage … z` is definitionally `(c - negacyclicMul s₂ pk.h, s₂)`.
  exact eval_pair _

/-! ### One-Shot Signing -/

/-- A single signing attempt (Falcon+, one-shot core).

Given a hash target `c ∈ R_q` (already computed from a salt and the message), uses
the trapdoor sampler (`falconPSF.trapdoorSample`) to produce a candidate short
preimage `(s₁, s₂)` with `s₁ + s₂ · h = c mod q`. Returns the preimage if the norm
check `‖(s₁, s₂)‖₂² ≤ ⌊β²⌋` passes, or `none` to signal retry.

This isolates the one-shot trapdoor-sampling core (with its norm-check abort) so that
proofs about sampling quality can target `falconPSF.trapdoorSample` directly, separately
from the surrounding fresh-salt retry loop. -/
noncomputable def signAttempt (pk : PublicKey p) (sk : SecretKey p) (c : Rq p.n) :
    ProbComp (Option (Rq p.n × Rq p.n)) := do
  let x ← (falconPSF p prims).trapdoorSample pk sk c
  if (falconPSF p prims).isShort x then
    return some x
  else
    return none

/-- Centered integer lift of an `R_q` element (coefficients in `[-(q-1)/2, (q-1)/2]`), the
coefficient-wise inverse of `IntPoly.toRq`. Used to feed the signature compressor, which
consumes an `IntPoly`. -/
def rqToIntPolyCentered {n : ℕ} (f : Rq n) : IntPoly n :=
  let a := f.toArray
  Vector.ofFn fun i : Fin n => centeredRepr (a.getD i.1 0)

/-- `IntPoly.toRq` is a left inverse of `rqToIntPolyCentered`: reducing the centered integer
lift of `f ∈ R_q` back mod `q` recovers `f`. Coefficient-wise, `rqToIntPolyCentered` stores the
centered representative `centeredRepr (f[i])` and `IntPoly.toRq` casts it back into `ZMod q`;
`LatticeCrypto.centeredRepr_intCast` shows this cast is the identity on `ZMod q`. This closes the
compress/decompress roundtrip in `verify_sign_correct`, where `verify` recomputes
`s₂ = IntPoly.toRq (rqToIntPolyCentered s₂)`. -/
theorem toRq_rqToIntPolyCentered {n : ℕ} (f : Rq n) :
    IntPoly.toRq (rqToIntPolyCentered f) = f := by
  apply LatticeCrypto.Poly.ext_get_eq
  intro i
  unfold IntPoly.toRq integralLift rqToIntPolyCentered
  simp only [LatticeCrypto.vectorIntegralLift, LatticeCrypto.PolyBackend.mapCoeffs,
    LatticeCrypto.vectorBackend, Vector.get_ofFn]
  have hget : f.toArray.getD i.1 0 = f.get i := by
    simp [Array.getD_eq_getD_getElem?, Vector.get]
  rw [hget]
  change (↑(LatticeCrypto.centeredRepr (f.get i)) : Coeff) = f.get i
  exact (LatticeCrypto.centeredRepr_intCast (f.get i)).symm

/-- Falcon signing (Falcon+, Algorithm 10), as a fuel-bounded rejection loop.

Mirrors `FiatShamir.WithAbort.fsAbortSignLoop` and the concrete `Concrete.Sign.concreteSign`:
on each of up to `maxAttempts` attempts, sample a fresh 40-byte salt `r`, hash
`c = HashToPoint(r, pk, message)`, and run `signAttempt`. On a short preimage `(_, s₂)` that
also compresses within `p.sbytelen`, return `some ⟨r, compress s₂⟩`; otherwise retry with a
fresh salt. Returns `none` if all `maxAttempts` attempts abort.

The `Option` result mirrors the `FiatShamirWithAbort` convention: the acceptance + compression
check cannot hold by construction (a vector can pass the `ℓ₂` `isShort` bound yet have a
coefficient too large for `compress`), so loop *productivity* is probabilistic — the `none`
branch handles exhaustion. The compression length is exactly `p.sbytelen`, matching `verify`'s
`decompress … p.sbytelen` so the `compress_decompress` roundtrip chains. -/
noncomputable def sign (pk : PublicKey p) (sk : SecretKey p) (msg : List Byte) :
    ℕ → ProbComp (Option Signature)
  | 0 => return none
  | maxAttempts + 1 => do
    let salt ← ($ᵗ (Bytes 40) : ProbComp (Bytes 40))
    let c := prims.hashToPointForPublicKey pk.h salt msg
    let r ← signAttempt p prims pk sk c
    match r with
    | some (_, s₂) =>
        match prims.compress (rqToIntPolyCentered s₂) p.sbytelen with
        | some comp => return (some ⟨salt, comp⟩)
        | none => sign pk sk msg maxAttempts
    | none => sign pk sk msg maxAttempts

/-- Falcon verification (Algorithm 16).

Given `(pk, message, signature)`:
1. Decompress `s₂` from the signature.
2. Recompute `c = HashToPoint(r, pk, message)`.
3. Compute `s₁ = c - s₂ · h mod q`.
4. Accept iff `‖(s₁, s₂)‖₂² ≤ ⌊β²⌋`. -/
noncomputable def verify (pk : PublicKey p) (msg : List Byte) (sig : Signature) : Bool :=
  match prims.decompress sig.compressedS2 p.sbytelen with
  | none => false
  | some s2Int =>
    let c := prims.hashToPointForPublicKey pk.h sig.salt msg
    let s2 := IntPoly.toRq s2Int
    let s1 := c - negacyclicMul s2 pk.h
    decide (pairL2NormSq s1 s2 ≤ p.betaSquared)

/-! ### GPV Signature Scheme -/

/-- The Falcon signature scheme as a `GPVHashAndSign` instantiation, parameterized by
a salt type `Salt`.

This connects Falcon to the generic GPV framework, enabling the generic EUF-CMA
security theorem to be applied. The message type is `List Byte` and the random oracle
maps `(salt, message)` to elements of `R_q`.

The GPV construction internally samples a fresh salt per signing query and queries
the random oracle at `(salt, message)`, matching the Falcon+ convention.

The Falcon specification uses `Salt = Bytes 40` (40 random bytes = 320 bits),
chosen as `λ + log₂(Q_s)` for `λ = 256` and `Q_s = 2^64` (Section 2.2.2). -/
noncomputable def falconSignatureAlg
    (Salt : Type) [DecidableEq Salt] [SampleableType Salt]
    [SampleableType (Rq p.n)]
    [DecidableEq (Rq p.n)]
    (hr : GenerableRelation (PublicKey p) (SecretKey p)
      (validKeyPair p)) :
    SignatureAlg (OracleComp (unifSpec + (Salt × List Byte →ₒ Rq p.n)))
      (M := List Byte) (PK := PublicKey p) (SK := SecretKey p)
      (S := Salt × (Rq p.n × Rq p.n)) :=
  GPVHashAndSign (falconPSF p prims) hr (List Byte) Salt

end Falcon
