/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.SourceBundle

/-!
# Retained Foundation imperative utilities

Exact constructor quotation of the complete `Imperative` module in
`artifacts/modules/list.json`. The module has no external value dependencies.
`Interop/Cryptol/scripts/import_imperative.py` reproduces every retained field
from the pinned official frontend export.
-/

public section

namespace Cryptol.Bridge.ImperativeSource

open Translation

/-- Complete source module, including both exported bodies and their source identities. -/
@[expose] def source : ModuleDefinition :=
  (ModuleDefinition.mk (SourceModule.mk "shared::common::utils::Imperative"
  "shared/common/utils/Imperative.cry"
  "d4ac74fe6b4e4439d2b6d9a44770f2e8805c99d582a3dbf360fbc307fb9b148b" []) [] [] []
  [(Reference.Name.mk 4683 "while" "shared::common::utils::Imperative::while" ),
  (Reference.Name.mk 4684 "dowhile" "shared::common::utils::Imperative::dowhile" )] [] [] [] []
  [(.recursive [(Reference.Decl.mk (Reference.Name.mk 4683 "while"
  "shared::common::utils::Imperative::while" ) (Reference.Schema.mk [(Reference.Parameter.mk 895
  .value)] [] (.constructor "TC TCFun" [(.constructor "TC TCFun" [(.var (Reference.Parameter.mk
  895 .value)), (.constructor "TC TCBit" [])]), (.constructor "TC TCFun" [(.constructor
  "TC TCFun" [(.var (Reference.Parameter.mk 895 .value)), (.var (Reference.Parameter.mk 895
  .value))]), (.constructor "TC TCFun" [(.var (Reference.Parameter.mk 895 .value)), (.var
  (Reference.Parameter.mk 895 .value))])])])) (.expression (.typeAbs (Reference.Parameter.mk 895
  .value) (.abs (Reference.Name.mk 4686 "condition" "condition" ) (.constructor "TC TCFun" [(.var
  (Reference.Parameter.mk 895 .value)), (.constructor "TC TCBit" [])]) (.abs (Reference.Name.mk
  4687 "body" "body" ) (.constructor "TC TCFun" [(.var (Reference.Parameter.mk 895 .value)),
  (.var (Reference.Parameter.mk 895 .value))]) (.abs (Reference.Name.mk 4688 "initial_state"
  "initial_state" ) (.var (Reference.Parameter.mk 895 .value)) (.ite (.app (.var
  (Reference.Name.mk 4686 "condition" "condition" )) (.var (Reference.Name.mk 4688
  "initial_state" "initial_state" ))) (.app (.app (.app (.typeApp (.var (Reference.Name.mk 4683
  "while" "shared::common::utils::Imperative::while" )) (.var (Reference.Parameter.mk 895
  .value))) (.var (Reference.Name.mk 4686 "condition" "condition" ))) (.var (Reference.Name.mk
  4687 "body" "body" ))) (.app (.var (Reference.Name.mk 4687 "body" "body" )) (.var
  (Reference.Name.mk 4688 "initial_state" "initial_state" )))) (.var (Reference.Name.mk 4688
  "initial_state" "initial_state" )))))))))]), (.nonrecursive (Reference.Decl.mk
  (Reference.Name.mk 4684 "dowhile" "shared::common::utils::Imperative::dowhile" )
  (Reference.Schema.mk [(Reference.Parameter.mk 905 .value)] [] (.constructor "TC TCFun"
  [(.constructor "TC TCFun" [(.var (Reference.Parameter.mk 905 .value)), (.constructor "TC TCBit"
  [])]), (.constructor "TC TCFun" [(.constructor "TC TCFun" [(.var (Reference.Parameter.mk 905
  .value)), (.var (Reference.Parameter.mk 905 .value))]), (.constructor "TC TCFun" [(.var
  (Reference.Parameter.mk 905 .value)), (.var (Reference.Parameter.mk 905 .value))])])]))
  (.expression (.typeAbs (Reference.Parameter.mk 905 .value) (.abs (Reference.Name.mk 4690
  "condition" "condition" ) (.constructor "TC TCFun" [(.var (Reference.Parameter.mk 905 .value)),
  (.constructor "TC TCBit" [])]) (.abs (Reference.Name.mk 4691 "body" "body" ) (.constructor
  "TC TCFun" [(.var (Reference.Parameter.mk 905 .value)), (.var (Reference.Parameter.mk 905
  .value))]) (.abs (Reference.Name.mk 4692 "initial_state" "initial_state" ) (.var
  (Reference.Parameter.mk 905 .value)) (.whereE (.ite (.app (.var (Reference.Name.mk 4690
  "condition" "condition" )) (.var (Reference.Name.mk 4693 "next_state" "next_state" ))) (.app
  (.app (.app (.typeApp (.var (Reference.Name.mk 4683 "while"
  "shared::common::utils::Imperative::while" )) (.var (Reference.Parameter.mk 905 .value))) (.var
  (Reference.Name.mk 4690 "condition" "condition" ))) (.var (Reference.Name.mk 4691 "body" "body"
  ))) (.var (Reference.Name.mk 4693 "next_state" "next_state" ))) (.var (Reference.Name.mk 4693
  "next_state" "next_state" ))) [(.nonrecursive (Reference.Decl.mk (Reference.Name.mk 4693
  "next_state" "next_state" ) (Reference.Schema.mk [] [] (.var (Reference.Parameter.mk 905
  .value))) (.expression (.app (.var (Reference.Name.mk 4691 "body" "body" )) (.var
  (Reference.Name.mk 4692 "initial_state" "initial_state" ))))))]))))))))] [(DeclarationInfo.mk
  (Reference.Name.mk 4683 "while" "shared::common::utils::Imperative::while" ) (SourceIdentity.mk
  (.some "shared::common::utils::Imperative" ) "while" (SourceLocation.mk "Imperative.cry"
  (Prod.mk 12 1) (Prod.mk 12 6))) [(Reference.Name.mk 4683 "while"
  "shared::common::utils::Imperative::while" )] false), (DeclarationInfo.mk (Reference.Name.mk
  4684 "dowhile" "shared::common::utils::Imperative::dowhile" ) (SourceIdentity.mk (.some
  "shared::common::utils::Imperative" ) "dowhile" (SourceLocation.mk "Imperative.cry" (Prod.mk 21
  1) (Prod.mk 21 8))) [(Reference.Name.mk 4683 "while" "shared::common::utils::Imperative::while"
  )] false)] [] [])

/-- The dependency-closed module bundle used by the checked open importer. -/
@[expose] def bundle : ModuleBundle :=
  ⟨SourceBundle.expectedCryptolRevision, [source], [], [],
    ["cffd4082d3347aba60c131d2e7d33f8b8fdfaf6afa4aedd52d8d2fff7bb30a2e"]⟩

end Cryptol.Bridge.ImperativeSource
