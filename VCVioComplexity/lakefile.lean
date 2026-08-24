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
  "b6738219a3a3c50967d6bd16cba9487887ca6b66"

require VCVio from ".."

/- Use the exact PolyFun source against which the root VCVio checkout is being developed. -/
require PolyFun from "../.lake/packages/PolyFun"

require "leanprover-community" / "mathlib" @ git "v4.33.0"

@[default_target] lean_lib VCVioComplexity
