import Lake
open Lake DSL

package VCVio where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.modulesUpperCamelCase, true⟩,
    ⟨`weak.linter.style.whitespace, true⟩,
    -- Disable the unicode allowlist linter: VCVio docstrings legitimately use
    -- FIPS-204 math notation (combining tilde `c̃`) and cited author names with
    -- diacritics (e.g. `Cătălin Hriţcu`).
    ⟨`weak.linter.unicodeLinter, false⟩
  ]

/-
Interop backends are intentionally disabled for the Lean 4.31 baseline. Their
source remains under `Interop/`, isolated from the trusted libraries by
`scripts/check-interop-isolation.sh`, but the aggregate module and CI do not
build it. Re-enable a backend only once its upstream Lean library supports the
repository's Lean version without a local compatibility layer.

Hax still targets Lean 4.29.0-rc1 and does not build with Lean 4.31.0 as of
2026-07-11. Subdirectory: `hax-lib/proof-libs/lean`.
-/
-- require Hax from git
--   "https://github.com/cryspen/hax" @
--   "492a34e3" / "hax-lib/proof-libs/lean"

/-
Loom2: foundation for the Loom-style WP / Triple program-logic
abstractions used in `VCVio/ProgramLogic/`. Tracks Volo Gladshtein's unmerged
upstream PR https://github.com/leanprover/lean4/pull/12965 in the
`Std.Internal.Do.{WPMonad,PredTrans,Triple,Assertion,ExceptPost}` namespace
(temporarily prefixed `Std.Do'` in Loom2 to avoid clashing once it merges).

Tracks the Lean 4.31 compatibility branch based on upstream revision
`876296fc`. When upstream Lean ships these foundations in a stable release,
drop this require and re-import from `Std.Do.…` directly.
-/
require loom2 from git
  "https://github.com/quangvdao/loom2" @
  "lean-4.31"

/-
Aeneas now natively pins Lean and Mathlib v4.31.0. This dormant pin follows its
published `nightly-2026.07.11-15b9684`; keep it disabled until the VCVio bridge
is tested separately and can be enabled without compatibility aliases.
Subdirectory: `backends/lean`.
-/
-- require aeneas from git
--   "https://github.com/AeneasVerif/aeneas" @
--   "15b968482b0dcd7aae45020b6d1bca39b5024af5" / "backends/lean"

require "leanprover-community" / "mathlib" @ git "v4.31.0"

require PolyFun from git
  "https://github.com/Verified-zkEVM/PolyFun.git" @
  "04a12b67fa2048c9412fdd26ed9e446f25919d37"

/-- Main library. -/
@[default_target] lean_lib VCVio

/-- Shared FFI bindings (SHA-3 / FIPS 202, etc.). -/
lean_lib FFI

/-- Lattice-based cryptography: ring arithmetic, hardness assumptions, and scheme definitions. -/
lean_lib LatticeCrypto

/-- Hash-based signatures: SLH-DSA (SPHINCS+, FIPS 205) proof-level specs and security.
Peer of `LatticeCrypto`; may depend on `VCVio`/`ToMathlib` (and Mathlib), but nothing in
`VCVio`/`ToMathlib`/`FFI`/`Interop` may import it. -/
lean_lib HashSig

/-- Example constructions of cryptographic primitives. -/
lean_lib Examples
/-- Optional proof widget experiments and visualizations. -/
lean_lib VCVioWidgets
/-- Seperate section of the project for things that should be ported. -/
lean_lib ToMathlib

/-- Dormant Interop bridges to Rust verification frontends (hax, aeneas).
Strict TCB isolation: no other `lean_lib` may import from `Interop`. See
`Interop/README.md` and `docs/agents/interop.md`. This target is intentionally
excluded from the Lean 4.31 baseline build. -/
lean_lib Interop

-- Compile the shared FIPS 202 (SHA-3/SHAKE) FFI wrapper.
-- Uses mlkem-native's FIPS 202 headers for the underlying implementation.
target hashing_ffi.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "hashing_ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "hashing" / "lean_hashing_ffi.c"
  let mlkemDir := pkg.dir / "third_party" / "mlkem-native" / "mlkem"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
    "-I", mlkemDir.toString,
    "-I", (mlkemDir / "src").toString,
    "-std=c99", "-O2"]
  buildO oFile srcJob weakArgs #["-fPIC"] "cc" getLeanTrace

extern_lib leanhashing pkg := do
  let hashO ← hashing_ffi.o.fetch
  let name := nameToStaticLib "leanhashing"
  buildStaticLib (pkg.staticLibDir / name) #[hashO]

-- Compile mlkem-native core and Lean FFI wrappers.
-- Supports multiple parameter sets (512, 768, 1024) via separate TUs.
private def mlkemCFlagsForSet (pkg : NPackage __name__) (paramSet : Nat) :
    FetchM (Array String × Array String) := do
  let mlkemDir := pkg.dir / "third_party" / "mlkem-native" / "mlkem"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
    "-I", mlkemDir.toString,
    "-I", (mlkemDir / "src").toString,
    "-DMLK_CONFIG_NO_RANDOMIZED_API",
    s!"-DMLK_CONFIG_PARAMETER_SET={paramSet}",
    "-std=c99", "-O2"]
  return (weakArgs, #["-fPIC"])

target mlkem_native.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mlkem_native.o"
  let mlkemDir := pkg.dir / "third_party" / "mlkem-native" / "mlkem"
  let srcJob ← inputTextFile <| mlkemDir / "mlkem_native.c"
  let (weakArgs, traceArgs) ← mlkemCFlagsForSet pkg 768
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target mlkem_ffi.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mlkem_ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "mlkem" / "lean_mlkem_ffi.c"
  let (weakArgs, traceArgs) ← mlkemCFlagsForSet pkg 768
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target mlkem_native_512.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mlkem_native_512.o"
  let mlkemDir := pkg.dir / "third_party" / "mlkem-native" / "mlkem"
  let srcJob ← inputTextFile <| mlkemDir / "mlkem_native.c"
  let (weakArgs, traceArgs) ← mlkemCFlagsForSet pkg 512
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target mlkem512_ffi.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mlkem512_ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "mlkem" / "lean_mlkem512_ffi.c"
  let (weakArgs, traceArgs) ← mlkemCFlagsForSet pkg 512
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target mlkem_native_1024.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mlkem_native_1024.o"
  let mlkemDir := pkg.dir / "third_party" / "mlkem-native" / "mlkem"
  let srcJob ← inputTextFile <| mlkemDir / "mlkem_native.c"
  let (weakArgs, traceArgs) ← mlkemCFlagsForSet pkg 1024
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target mlkem1024_ffi.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mlkem1024_ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "mlkem" / "lean_mlkem1024_ffi.c"
  let (weakArgs, traceArgs) ← mlkemCFlagsForSet pkg 1024
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

extern_lib leanmlkem pkg := do
  let nativeO ← mlkem_native.o.fetch
  let ffiO ← mlkem_ffi.o.fetch
  let native512 ← mlkem_native_512.o.fetch
  let ffi512 ← mlkem512_ffi.o.fetch
  let native1024 ← mlkem_native_1024.o.fetch
  let ffi1024 ← mlkem1024_ffi.o.fetch
  let name := nameToStaticLib "leanmlkem"
  buildStaticLib (pkg.staticLibDir / name)
    #[nativeO, ffiO, native512, ffi512, native1024, ffi1024]

-- Compile mldsa-native core and Lean FFI wrappers.
-- Supports multiple parameter sets (44, 65, 87) via separate TUs.
private def mldsaCFlagsForSet (pkg : NPackage __name__) (paramSet : Nat) :
    FetchM (Array String × Array String) := do
  let mldsaDir := pkg.dir / "third_party" / "mldsa-native" / "mldsa"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
    "-I", mldsaDir.toString,
    "-I", (mldsaDir / "src").toString,
    s!"-DMLD_CONFIG_PARAMETER_SET={paramSet}",
    -- Exclude the randomized signing API (mirrors mlkem's `MLK_CONFIG_NO_RANDOMIZED_API`):
    -- it pulls in an undefined `randombytes` symbol that fails to link on Linux, and the
    -- FFI tests only exercise the internal deterministic API.
    "-DMLD_CONFIG_NO_RANDOMIZED_API",
    "-std=c99", "-O2"]
  return (weakArgs, #["-fPIC"])

target mldsa_native.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mldsa_native.o"
  let mldsaDir := pkg.dir / "third_party" / "mldsa-native" / "mldsa"
  let srcJob ← inputTextFile <| mldsaDir / "mldsa_native.c"
  let (weakArgs, traceArgs) ← mldsaCFlagsForSet pkg 65
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target mldsa_ffi.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mldsa_ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "mldsa" / "lean_mldsa_ffi.c"
  let (weakArgs, traceArgs) ← mldsaCFlagsForSet pkg 65
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target mldsa_native_44.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mldsa_native_44.o"
  let mldsaDir := pkg.dir / "third_party" / "mldsa-native" / "mldsa"
  let srcJob ← inputTextFile <| mldsaDir / "mldsa_native.c"
  let (weakArgs, traceArgs) ← mldsaCFlagsForSet pkg 44
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target mldsa44_ffi.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mldsa44_ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "mldsa" / "lean_mldsa44_ffi.c"
  let (weakArgs, traceArgs) ← mldsaCFlagsForSet pkg 44
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target mldsa_native_87.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mldsa_native_87.o"
  let mldsaDir := pkg.dir / "third_party" / "mldsa-native" / "mldsa"
  let srcJob ← inputTextFile <| mldsaDir / "mldsa_native.c"
  let (weakArgs, traceArgs) ← mldsaCFlagsForSet pkg 87
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target mldsa87_ffi.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "mldsa87_ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "mldsa" / "lean_mldsa87_ffi.c"
  let (weakArgs, traceArgs) ← mldsaCFlagsForSet pkg 87
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

extern_lib leanmldsa pkg := do
  let nativeO ← mldsa_native.o.fetch
  let ffiO ← mldsa_ffi.o.fetch
  let native44 ← mldsa_native_44.o.fetch
  let ffi44 ← mldsa44_ffi.o.fetch
  let native87 ← mldsa_native_87.o.fetch
  let ffi87 ← mldsa87_ffi.o.fetch
  let name := nameToStaticLib "leanmldsa"
  buildStaticLib (pkg.staticLibDir / name)
    #[nativeO, ffiO, native44, ffi44, native87, ffi87]

-- Compile c-fn-dsa (Falcon / FN-DSA) core and Lean FFI wrapper.
private def falconCFlags (pkg : NPackage __name__) :
    FetchM (Array String × Array String) := do
  let fndsaDir := pkg.dir / "third_party" / "c-fn-dsa"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
    "-I", fndsaDir.toString,
    -- `_GNU_SOURCE` is required on glibc: under `-std=c99` it otherwise hides
    -- `getentropy` / `O_CLOEXEC`, which `third_party/c-fn-dsa/sysrng.c` uses, so
    -- the Falcon RNG fails to compile on Linux (macOS exposes them regardless).
    "-D_GNU_SOURCE", "-std=c99", "-O2"]
  return (weakArgs, #["-fPIC"])

target fndsa.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "fndsa.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "falcon" / "fndsa.c"
  let (weakArgs, traceArgs) ← falconCFlags pkg
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

target fndsa_ffi.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "c" / "fndsa_ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "csrc" / "falcon" / "lean_falcon_ffi.c"
  let (weakArgs, traceArgs) ← falconCFlags pkg
  buildO oFile srcJob weakArgs traceArgs "cc" getLeanTrace

extern_lib leanfalcon pkg := do
  let nativeO ← fndsa.o.fetch
  let ffiO ← fndsa_ffi.o.fetch
  let name := nameToStaticLib "leanfalcon"
  buildStaticLib (pkg.staticLibDir / name) #[nativeO, ffiO]

/-- Test support modules (helpers, vectors). -/
lean_lib VCVioTest

/-- Lattice crypto test support modules (helpers, ACVP vectors). -/
lean_lib LatticeCryptoTest

/-- SLH-DSA known-answer test executables (differential tests vs external reference signers).
Test-only and deliberately kept out of the `HashSig` library aggregate: each KAT module carries a
root-level `main`, and a `submodules` glob builds them independently so the entry points never
collide. -/
lean_lib HashSigTest where
  globs := #[.submodules `HashSigTest]

/-- Smoke test: imports VCVio and prints OK. -/
lean_exe smoke_test where
  root := `VCVioTest.Smoke

/-- ML-KEM test executable (links against mlkem-native FFI). -/
lean_exe mlkem_test where
  root := `LatticeCryptoTest.MLKEM.Main

/-- ML-DSA test executable (links against mldsa-native FFI). -/
lean_exe mldsa_test where
  root := `LatticeCryptoTest.MLDSA.Main

/-- Falcon test executable (links against c-fn-dsa FFI). -/
lean_exe falcon_test where
  root := `LatticeCryptoTest.Falcon.Main

/-- SLH-DSA-SHA2-128-24 known-answer test: pure-Lean concrete verify vs the C reference vector. -/
lean_exe slhdsa_kat where
  root := `HashSigTest.SLHDSA.Sha2KAT

/-- C13 known-answer test: pure-Lean keccak256 concrete verify vs the reference signer vector. -/
lean_exe slhdsa_c13_kat where
  root := `HashSigTest.SLHDSA.C13KAT
