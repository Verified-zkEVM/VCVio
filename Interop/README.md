# Interop

Sub-projects that connect VCVio to code and tools outside Lean. Each one is a directory
`Interop/<Sub>/` with its own Lake package, its own trusted base, its own assumptions and the
implementations it covers. This page is their index and states the rules they share; each
sub-project's README states the rest.

## Stability

`Interop/` is experimental, and it changes much faster than the rest of VCVio.
- *No stable interface.* Any PR may rename a sub-project's modules, restate its theorems or move
  its pins, without deprecations.
- *It follows the tools.* The outside tools change their Lean output and libraries between
  releases, and the sub-projects change with them.
- *The core is unaffected.* Core VCVio never depends on `Interop/` (see
  [shared rules](#shared-rules)).

To build on a sub-project, pin a VCVio commit and open an issue describing what you rely on.

## Sub-projects

| Sub-project | What it connects | Trusted base | Assumptions | Implementations covered |
|---|---|---|---|---|
| [`Interop/Aeneas`](Aeneas/README.md) | Rust code extracted by hax 0.5 and Aeneas, in Aeneas's monad `RustM`, lifted into `OracleComp` | hax's frontend, Charon and Aeneas, which translate the Rust crates, and the Rust models in the Lean libraries of Aeneas and hax; the extractions are committed and checked fresh in CI | a Rust function means its extracted `RustM` program, which returns, panics or diverges; Aeneas's scalar operations panic on overflow and on division by zero | ML-KEM's centred binomial sampler (η = 1) and signed Barrett reduction, 32-bit add-with-carry, checked arithmetic and division, and a Rust step after an oracle query |
| [`Interop/Squirrel`](Squirrel/README.md) | the higher-order CCSA logic of the Squirrel prover (LICS23, CSF24, CCS26), embedded deeply on PolyFun's scoped syntax, with a semantics over VCVio's machines and the soundness of its rules | nothing beyond Lean | the modelling choices in the obligations table of its [design record](../docs/design/interop-squirrel.md) | none yet |

## Shared rules

- **Core never imports `Interop`.** `VCVio/`, `ToMathlib/`, `LatticeCrypto/`, `LatticeCryptoTest/`,
  `HashSig/`, `HashSigTest/`, `Examples/`, `Extern/` and `VCVioTest/` never import `Interop.…`,
  `Hax.…` or `Aeneas.…`, so no sub-project's trusted base reaches a routine build of the core.
  `Interop/**` may import VCVio, ToMathlib, PolyFun and its own tools, but not the libraries that
  are themselves VCVio's clients.
- **A sub-project imports another only through a declared `require`.** A module `Interop.<A>.…`
  imports `Interop.<B>.…` only when the package of `Interop/<A>/` requires that of `Interop/<B>/`
  and the pair `A B` is listed in `scripts/interop_import_allowlist.txt`. No pair is listed.
- **Generic code moves to VCVio or PolyFun first.** Code that does not depend on a sub-project's
  tools, and that another sub-project could use, belongs in VCVio, or in PolyFun when it is general
  theory of free programs.
- **Each sub-project is its own Lake package.** `Interop/<Sub>/lakefile.toml` requires VCVio by path
  (`path = "../.."`). A package that requires VCVio resolves only the root lakefile's requires, so a
  tool required here never reaches VCVio's dependents. Two tools whose Lean libraries declare the
  same names can only live in different sub-projects.
  - When its pins equal the root's (Lean, Mathlib and the transitive pins), it shares the root's
    dependency cache: `packagesDir = "../../.lake/packages"`.
  - When its requirements conflict with the root's, it keeps its own cache, under the default
    `packagesDir`.
- **Sources are read from the repository root** (`srcDir = "../.."`), so a sub-project's modules are
  `Interop.<Sub>.…`, named after their paths, and the core's import guard sees them under one prefix.
- **Tests run through the sub-project's own test driver** (`testDriver` in its lakefile), when it
  has tests.

## Adding a sub-project

A sub-project is a new directory and a row in the table above:
- `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` for its package, and a `.gitignore`
  holding `/.lake`;
- a `README.md` with the sections of the [template](#readme-template).

The libraries in its lakefile's `defaultTargets` list their `roots`, which are also the roots of
its axiom sweep. CI finds the directory by itself. A check that only one tool needs, such as
re-running an extraction, is a workflow of its own beside the generic job.

## README template

Every sub-project's `README.md` has these sections, in this order:
1. *Connects to*: the outside tools and code, with their versions and pins.
2. *Trusted base*: what is trusted, and how outside code enters the repository (for example,
   extractions committed and checked fresh in CI).
3. *Assumptions*: what the Lean statements take for granted about the outside code.
4. *Implementations covered*.
5. *What is proved*.
6. *Stability*: what changes with the tools, beyond the [stability](#stability) of `Interop/`.
7. *Build and test*.

## CI

- **Build, tests and axiom sweep.** CI's `Interop <Sub>` jobs (`.github/workflows/build.yml`) run
  once for every directory `Interop/<Sub>/` holding a `lakefile.toml`, as listed by
  `scripts/interop-subprojects.py`. Each runs `lake exe cache get` and `lake build` in that
  directory, then `lake test` when `lake check-test` finds a test driver. It then runs
  `lake exe axiomsweep` over the roots of the default libraries against
  `scripts/axiom_baseline.json`, which holds them at zero `sorry` and nonstandard-axiom debt.
- **Imports.** `scripts/check-interop-isolation.sh` checks the import rules above, and the
  `Interop TCB Isolation` workflow (`.github/workflows/interop-isolation.yml`) runs it on every PR.
- **Tool-specific checks** belong to their sub-project, such as `Interop/Aeneas`'s
  `.github/workflows/hax-extraction.yml`.
