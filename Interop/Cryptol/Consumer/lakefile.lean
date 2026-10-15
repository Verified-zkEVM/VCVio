import Lake
open Lake DSL
package CryptolConsumer where
  packagesDir := "../../../.lake/packages"
  leanOptions := #[⟨`autoImplicit, false⟩]
require VCVio from "../../.." with
  match get_config? polyfunPath with
  | some p => ({} : Lean.NameMap String).insert `polyfunPath p
  | none => {}
@[default_target] lean_lib Consumer
@[default_target] lean_lib Foundation
