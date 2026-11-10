/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import Extern.MLDSA.Laws

/-!
# Hypothesis-consistency certificate for `MLDSA.Primitives.Laws` (issue #228)

The ML-DSA correctness and zero-knowledge theorems — `MLDSA.idsWithAbort_complete`
(`MLDSA/Security.lean`), `MLDSA.identificationSchemeFull_perfectHVZK` (`MLDSA/SecurityHVZK.lean`),
`MLDSA.fipsSign_fipsVerify_correct` (`MLDSA/Signature.lean`), and the algebraic identity they run
on (`MLDSA.keyGenFromSeed_wApprox_eq`) — are each gated on `h_laws : Primitives.Laws prims nttOps`.
A conditional theorem asserts nothing if its hypothesis is uninhabitable, and `#print axioms`
cannot detect that. `mldsa_laws_inhabited` rules that out at the FIPS 204 primitives themselves:
`MLDSA.Concrete.concretePrimitives_laws` proves `Primitives.Laws` for `concretePrimitives` at every
approved parameter set.

**Trust surface.** `mldsa_laws_inhabited` depends only on `propext`, `Classical.choice`, and
`Quot.sound`. The structural butterfly stages in `LatticeCrypto/Ring/NTTCert.lean` have
round-trip laws proved from per-stage twiddle identities. `ntt_coeff_eq_eval`, from the residue
theorem of `LatticeCrypto/Ring/NTTSplitCert.lean`, proves that coordinate `i` of the structural NTT
is the evaluation at `ζ^(2·brv(i) + 1)`. So `ntt_negacyclicMul` holds for the pointwise
`multiplyNTTs` (FIPS 204 Algorithm 45).
The concrete `ntt`/`invNTT` are the imperative `loopNTT`/`loopInvNTT` kernels, proved equal to the
structural stages, so the laws are about the code that runs. The *abstract* `Laws`-gated theorems
(quantified over `nttOps`) do not depend on this; this certificate only shows that their `Laws`
hypothesis is met by the concrete layer.
-/

public section

open MLDSA

namespace MLDSA

/-- **The #228 non-vacuity certificate.** The concrete primitives at ML-DSA-44 satisfy
`Primitives.Laws`, so the `Laws`-gated ML-DSA theorems (`MLDSA.idsWithAbort_complete`,
`MLDSA.identificationSchemeFull_perfectHVZK`, `MLDSA.fipsSign_fipsVerify_correct`,
`MLDSA.keyGenFromSeed_wApprox_eq`) are not true-but-vacuous. -/
theorem mldsa_laws_inhabited :
    ∃ (p : Params) (prims : MLDSA.Primitives p),
      Nonempty (MLDSA.Primitives.Laws prims MLDSA.Concrete.concreteNTTRingOps) :=
  ⟨mldsa44, MLDSA.Concrete.concretePrimitives mldsa44,
    ⟨MLDSA.Concrete.concretePrimitives_laws mldsa44 (Or.inl rfl)⟩⟩

end MLDSA
