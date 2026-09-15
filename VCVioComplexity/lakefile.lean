import Lake

open Lake DSL

package VCVioComplexity where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.modulesUpperCamelCase, true⟩,
    ⟨`weak.linter.style.whitespace, true⟩,
    ⟨`weak.linter.unicodeLinter, false⟩
  ]

/-
Keep the direct Mathlib requirement last. Lake resolves requirements in reverse
declaration order, so VCVio's Lean/Mathlib baseline remains authoritative over
the older pins inherited from complexitylib.
-/
require complexitylib from git
  "https://github.com/SamuelSchlesinger/complexitylib.git" @
  "6c248df7859f2f245e731c1e07057bf69d165fe2"

require VCVio from ".."

/- Use the exact PolyFun source against which the root VCVio checkout is being developed. -/
require PolyFun from "../.lake/packages/PolyFun"

require "leanprover-community" / "mathlib" @ git "e06eff5f95374108acfaf19f1ff7473aa7771df2"

@[default_target] lean_lib VCVioComplexity

/-- Compile-time canaries and guarded trust probes for the optional backend package. -/
lean_lib VCVioComplexityTest
