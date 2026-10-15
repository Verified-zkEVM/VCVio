# Interop

Optional language and verification bridges. The active
[Cryptol development](Cryptol/README.md) shares VCVio's root toolchain and
manifest. The Rust/hax/aeneas bridges remain dormant and are excluded from the
default build; their source checks still run.

## Import boundaries

Core proof and test libraries, including `HashSig`, never import `Interop`,
`Hax`, or `Aeneas`. Cryptol has separate optional `CryptolModel`,
`CryptolTranslation`, `CryptolBridge`, and `CryptolTests` Lake targets.
`Interop.lean` aggregates only the dormant Rust backends.

Inside Cryptol, imports flow `Bridge → Translation → Model → PolyFun/CSLib`.
Only Bridge may use VCVio, ToMathlib, and HashSig. Model and Translation carry
no probability semantics. Rust backends do not import Cryptol, and Cryptol
does not import them. `scripts/check-interop-isolation.sh` checks ordinary,
public, meta, and `import all` forms; its negative fixtures cover each boundary.

## Layout

```
Interop/
├── README.md             ← this file
├── Rust/                 ← framework-side Rust target monad (`RustOracleComp`)
│   ├── Common.lean       ← `RustOracleComp`, mirrored `Error`, `Std.Do.WP` glue
│   └── Run.lean          ← reusable `.run.run` peel lemmas for the
│                           `ExceptT / OptionT / OracleComp` stack, used
│                           by probabilistic proofs downstream
├── Hax/                  ← bridge to `Hax.RustM` (gated on hax require)
│   ├── README.md
│   ├── Bridge.lean       ← `liftRustM`, `errorOfHax`,
│   │                       `@[spec] triple_liftRustM`, `LawfulMonadLift`
│   │                       instance, bundled `MonadHom` (`liftRustMHom`)
│   ├── Examples.lean     ← hand-crafted demo: `addOrPanicLifted`,
│   │                       oracle-composed `oracleThenAdd`, probabilistic
│   │                       `tossedAdd` with `Pr[panic] = 1/2`
│   ├── Computation.lean  ← hax-emitted `x + x + 1` (first real hax source)
│   ├── Division.lean     ← hax-emitted `/?`: `.divisionByZero` end-to-end
│   ├── Adc.lean          ← hax `lean_adc`: 32-bit ADC via
│   │                       `hax_mvcgen <;> bv_decide`, transported by
│   │                       one application of `triple_liftRustM`
│   ├── Barrett.lean      ← hax `lean_barrett`: signed 32-bit Barrett
│   │                       reduction mod 3329, proven in-range via
│   │                       `hax_bv_decide` (bit-blast, 300s timeout)
│   └── CenteredBinomial.lean
│                         ← CBD(η = 1) sampler from `third_party/hax-cbd`;
│                           first randomized hax source. Deterministic
│                           `{-1, 0, 1}` range over all `u8` by
│                           `native_decide`; exact distribution
│                           `Pr[0] = 1/2`, `Pr[±1] = 1/4` on
│                           `sampleRandomCbd1 : RustOracleComp unifSpec i32`
└── Aeneas/               ← bridge to `Aeneas.Std.Result` (currently disabled)
    └── README.md
```

`Rust/Common.lean` is **self-contained**: it builds without hax or aeneas
loaded, by mirroring their shared `Error` enum and reconstructing the
`ExceptT Error (OptionT (OracleComp spec))` stack that hax's `RustM` collapses
into. The actual `MonadLift` instances from hax/aeneas live in `Hax/` and
`Aeneas/`, where they can use the upstream definitions.

## Git-pinned Backend Requires

`lakefile.lean` carries explicit git pins for both backends. Current state:

```lean
-- Hax: disabled; upstream does not build with Lean 4.31.
-- require Hax from git
--   "https://github.com/cryspen/hax" @ "492a34e3" / "hax-lib/proof-libs/lean"

-- Aeneas: disabled, but pinned to a published Lean 4.31 nightly.
-- require aeneas from git
--   "https://github.com/AeneasVerif/aeneas" @
--   "15b968482b0dcd7aae45020b6d1bca39b5024af5" / "backends/lean"
```

### Require order matters

`require Hax` must appear **before** `require "leanprover-community" /
"mathlib"`. Hax transitively pins `Qq` at `v4.29.0-rc1`, Mathlib pins it
at the final release; Lake's conflict resolver takes the **last**
`require` of each dependency, so mathlib goes last to win. Wrong order
produces `mathlib: failed to fetch cache` on `lake update`.

We git-pin by default so reproducible builds are guaranteed. Bumping a
pin is a deliberate one-line change reviewed alongside any TCB delta.
