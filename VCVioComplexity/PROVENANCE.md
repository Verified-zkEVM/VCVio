# complexitylib provenance

- Upstream: <https://github.com/SamuelSchlesinger/complexitylib>
- Revision: `b6738219a3a3c50967d6bd16cba9487887ca6b66`
- Upstream toolchain at that revision: Lean `v4.30.0`
- VCVio validation toolchain: Lean and Mathlib `v4.33.0`

The direct Git dependency is tested with VCVio as a path dependency and with the nested package's
direct Mathlib `v4.33.0` requirement taking precedence over inherited pins. The direct compatibility
canary imports:

- `Complexitylib.Models.TuringMachine`;
- `Complexitylib.Classes.P.Cobham.Defs`.

Both modules compile unchanged at Lean/Mathlib 4.33. The transitive import
`Complexitylib.Asymptotics` does not: its Lean 4.30 proofs use extensionality for `Norm ℝ` and
natural-to-real coercion conversions that no longer close under Mathlib 4.33.
Consequently, `Complexitylib.Classes.P.Defs` and the full Cobham equivalence theorem remain outside
the compiling canary because they transitively depend on that asymptotics module; the syntax-only
`Complexitylib.Classes.P.Cobham.Defs` module does compile.

`VCVioComplexity.Asymptotics.PolyBound` is therefore the sole adapted upstream module. It retains
the definition and pointwise closure API from Bolton Bailey's
`Complexitylib.Asymptotics.PolyBound`, changes the namespace to `VCVioComplexity`, and imports
Mathlib's polynomial evaluation definitions directly. It omits only `PolyBound.bigO`, because that
theorem depends on the incompatible upstream asymptotics module. No file under `.lake/packages` is
patched.

The adapted module should be deleted in favor of the direct upstream declaration once the pinned
complexitylib asymptotics closure compiles with VCVio's authoritative Lean/Mathlib toolchain. The
package must not expose both versions as competing implementations.

Any future snapshot must likewise preserve the upstream Apache-2.0 headers, live under a distinct
VCVio namespace, list every copied file and compatibility edit here, and replace rather than
coexist with the direct implementation.

## Concrete TM adapter compatibility

`Complexitylib.Models.TuringMachine` compiles unchanged on Lean and Mathlib 4.33. It supplies the
concrete deterministic TM, exact `TM.reachesIn`, delimited `Tape.HasOutput`, and
`TM.ComputesInTime` used by `VCVioComplexity.Backend.TuringMachine`.

The higher compositional stack does not currently compile. `TuringMachine.Internal` fails at
upstream lines 54 and 71 because Lean 4.33's `split` no longer selects the exposed conditional;
`TuringMachine.Combinators` fails similarly at upstream lines 328 and 341. `Hoare.Defs` imports
the failing internal module, while `Composition.Defs` and `Subroutines.CopyOutput` transitively
import the failing combinator stack. Consequently this package exposes exact per-machine
certificates and inhabited PolyFun quantitative step classes for `Code` and `PolynomialCode`, but
no exported inhabitant of its categorical or structural closure requirements, oracle-TM adequacy
theorem, or `IsPPT` alias. Given a future inhabitant, the adapters already derive PolyFun's
optional category, exact-category, product, sum, option, and distributivity mixins; this
conditional wiring does not assert that the required machines exist. The underlying qualitative
carrier admits every semantic function and therefore makes no complexity claim by itself.
Computational evidence is retained only in the Type-valued quantitative realizers.

The adapter uses closed representation syntax for words, unit, booleans, products, dependent
sigma pairs, sums, and optional values, together with unary naturals for security parameters and
packed little-endian fixed-width `BitVec`s, all with proved concrete codecs. The sigma constructor
uses PolyFun's `CodeRetract.sigma`; it is needed because a polynomial-functor answer is intrinsically
a query position paired with a value from that position's response fiber. The grammar does not
permit arbitrary hidden-state encodings that could cache noncomputable advice. A zero-step
constant-unit machine and its bundled `PolynomialCode` demonstrate that the exact and polynomial
certificate types are concretely inhabited. The pure and one-coin canaries additionally exercise
complete VCVio certificates, including one enabled oracle transition in the latter.

The base adapter also converts any proved `TM.ComputesInTime` theorem into `PolynomialCode` when
the supplied time bound has a `PolyBound` proof. Classical choice selects the halting run already
proved by complexitylib; the resulting local cost remains the selected run's actual
`TM.reachesIn` transition count.

`PolynomialClosureGate` records the direct identity/composition acceptance test. It has no
exported inhabitant. Passing it requires total exact machines on all words, represented semantic
correctness, a polynomial run certificate, and a proved inequality for connection overhead. The
currently failing upstream modules prevent reusing `copyInputToOutputTM` and `compositionTM` at
Lean 4.33; no closure witness is inferred from their source definitions alone. The gate's adapter
to `polynomialQuantitativeStepClass.HasCategory` compiles, so supplying a gate is exactly what
enables PolyFun's categorical constructors for polynomial code.

The more general `QuantitativeClosure` similarly enables categorical composition of arbitrary
exact `Code` values with a sound cost inequality. `ExactQuantitativeClosure` is a separate,
strictly stronger refinement for backends that can prove an exact cost equation. This distinction
matches PolyFun's core-versus-mixin interface and avoids making exact additive accounting a
prerequisite for sound polynomial closure.

All compatibility work remains local to VCVio and PolyFun for this phase. No PR or issue is opened
in complexitylib, CSLib, or Mathlib.
