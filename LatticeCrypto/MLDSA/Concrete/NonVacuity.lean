/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/
import LatticeCrypto.MLDSA.Concrete.Laws

/-!
# Non-vacuity certificate for `MLDSA.Primitives.Laws` (issue #228)

`MLDSA.euf_cma_security_of_nma` is gated on `h_laws : Primitives.Laws prims nttOps`.  A conditional
theorem asserts nothing if its hypothesis is uninhabitable, and `#print axioms` cannot detect that.
This file rules that out with a kernel-checked witness: after the honest-sampling reformulation
(the false `expandS_honest_sampling` uniformity field is gone, its gap carried as the explicit
additive `honestSamplingSlack`/`idealGap`), `Primitives.Laws` is genuinely **inhabitable**.

The witness `idealPrims` is `concretePrimitives` with the public `ρ`-component of `expandSeed`
overridden to be the identity in the seed.  Every field consumed by the thirteen banked
`concrete_*` laws is definitionally unchanged, so those laws transfer verbatim; the only remaining
field, the determinacy assumption `keyVector_t0_determined`, holds trivially because the override
makes the published seed-component injective (matching `ρ` forces the same seed, hence the same
`t₀`).  This is the structural feature distinguishing the *satisfiable* `keyVector_t0_determined`
from the *unsatisfiable* (cardinality-false) `expandS_honest_sampling` it replaced.

**Trust surface.**  `mldsa_laws_inhabited` depends on `propext`, `Classical.choice`, `Quot.sound`,
**and** the pre-existing `native_decide` certificate for the concrete `256×256` NTT matrix inversion
(`MLDSA.Concrete.invNTTMatrix_nttMatrix_entry`, routed in through `concrete_transform`).  That
`native_decide` axiom is **not** introduced here — it is already carried by every concrete ML-DSA
fact (e.g. `concrete_transform` itself), since `concreteNTTRingOps` is the only `NTTRingLaws`
instance in the tree.  The *abstract* headline `MLDSA.euf_cma_security_of_nma` (quantified over
`nttOps`) is itself axiom-clean `[propext, Classical.choice, Quot.sound]`; this certificate only
witnesses that its `Laws` hypothesis can be met by the concrete layer (whose NTT-correctness trust
assumption it inherits).
-/

open MLDSA

set_option maxRecDepth 4000

namespace MLDSA

/-- `concretePrimitives p` with the public `ρ`-component of `expandSeed` overridden to be the
identity in the seed.  Every other field — including all fields consumed by the thirteen
`concrete_*` laws — is definitionally equal to `concretePrimitives p`, so those laws transfer
unchanged.  The override makes the published seed-component injective, which is exactly what
`keyVector_t0_determined` needs. -/
def idealPrims (p : Params) : MLDSA.Primitives p :=
  { MLDSA.Concrete.concretePrimitives p with
      expandSeed := fun s => (s, ((MLDSA.Concrete.concretePrimitives p).expandSeed s).2) }

/-- `Primitives.Laws (idealPrims p) concreteNTTRingOps` for any approved `p`.  Thirteen fields are
the banked `concrete_*` lemmas (they typecheck because every field consumed there is defeq between
`idealPrims p` and `concretePrimitives p`); `keyVector_t0_determined` needs only the hypothesis
`((idealPrims p).expandSeed s).1 = ((idealPrims p).expandSeed s').1`, which reduces to `s = s'`,
after which the two sides of the conclusion are syntactically identical. -/
theorem idealPrims_laws (p : Params) (hp : p.isApproved) :
    MLDSA.Primitives.Laws (idealPrims p) MLDSA.Concrete.concreteNTTRingOps where
  sampleInBall_norm        := MLDSA.Concrete.concrete_sampleInBall_norm p
  expandS_bound            := MLDSA.Concrete.concrete_expandS_bound p
  expandMask_bound         := MLDSA.Concrete.concrete_expandMask_bound p hp
  transform                := MLDSA.Concrete.concrete_transform
  high_low_decomp          := MLDSA.Concrete.concrete_high_low_decomp p
  lowBits_bound            := MLDSA.Concrete.concrete_lowBits_bound p hp
  hide_low                 := MLDSA.Concrete.concrete_hide_low p hp
  highBitsShift_injective  := MLDSA.Concrete.concrete_highBitsShift_injective p hp
  useHint_makeHint         := MLDSA.Concrete.concrete_useHint_makeHint p hp
  power2Round_decomp       := MLDSA.Concrete.concrete_power2Round_decomp p
  power2Round_bound        := MLDSA.Concrete.concrete_power2Round_bound p
  w1Encode_injective       := MLDSA.Concrete.concrete_w1Encode_injOn p hp
  sampleInBall_smul_bound  := MLDSA.Concrete.concrete_sampleInBall_smul_bound p
  keyVector_t0_determined  := by
    intro s s' hρ _
    -- `((idealPrims p).expandSeed s).1` reduces to `s`, so `hρ : s = s'`.
    simp only [idealPrims] at hρ
    subst hρ
    rfl

/-- **The #228 non-vacuity certificate.**  There is an approved parameter set and a primitive
bundle whose `Primitives.Laws` is inhabited — so `MLDSA.euf_cma_security_of_nma` is not
true-but-vacuous.  (See the trust-surface note in the module docstring on the inherited concrete
NTT `native_decide` axiom.) -/
theorem mldsa_laws_inhabited :
    ∃ (p : Params) (prims : MLDSA.Primitives p),
      Nonempty (MLDSA.Primitives.Laws prims MLDSA.Concrete.concreteNTTRingOps) :=
  ⟨mldsa44, idealPrims mldsa44, ⟨idealPrims_laws mldsa44 (Or.inl rfl)⟩⟩

end MLDSA
