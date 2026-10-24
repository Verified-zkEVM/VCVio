/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFunCryptol.Translation.SourceBundle

/-!
# Quoted Foundation scalar source

Raw constructor data from `artifacts/references/scalar-bundle.json`, including
source identities, schemes and annotations. `Interop/Cryptol/scripts/export_references.py`
checks byte-for-byte reproduction from the pinned official frontend.
-/

public section

namespace Cryptol.Bridge.ImportedScalarSource

open Cryptol Translation

/-- Source declaration 1 in dependency order. -/
@[expose] def declaration0 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4226 ">>>" "(Cryptol::>>>)" ) (Reference.Schema.mk
  [(Reference.Parameter.mk 331 .number), (Reference.Parameter.mk 332 .value),
  (Reference.Parameter.mk 333 .value)] [(.constructor "PC PFin" [(.var (Reference.Parameter.mk
  331 .number))]), (.constructor "PC PIntegral" [(.var (Reference.Parameter.mk 332 .value))])]
  (.constructor "TC TCFun" [(.constructor "TC TCSeq" [(.var (Reference.Parameter.mk 331
  .number)), (.var (Reference.Parameter.mk 333 .value))]), (.constructor "TC TCFun" [(.var
  (Reference.Parameter.mk 332 .value)), (.constructor "TC TCSeq" [(.var (Reference.Parameter.mk
  331 .number)), (.var (Reference.Parameter.mk 333 .value))])])])) .primitive)

/-- Source declaration 2 in dependency order. -/
@[expose] def declaration1 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4224 ">>" "(Cryptol::>>)" ) (Reference.Schema.mk
  [(Reference.Parameter.mk 325 .number), (Reference.Parameter.mk 326 .value),
  (Reference.Parameter.mk 327 .value)] [(.constructor "PC PIntegral" [(.var
  (Reference.Parameter.mk 326 .value))]), (.constructor "PC PZero" [(.var (Reference.Parameter.mk
  327 .value))])] (.constructor "TC TCFun" [(.constructor "TC TCSeq" [(.var
  (Reference.Parameter.mk 325 .number)), (.var (Reference.Parameter.mk 327 .value))]),
  (.constructor "TC TCFun" [(.var (Reference.Parameter.mk 326 .value)), (.constructor "TC TCSeq"
  [(.var (Reference.Parameter.mk 325 .number)), (.var (Reference.Parameter.mk 327 .value))])])]))
  .primitive)

/-- Source declaration 3 in dependency order. -/
@[expose] def declaration2 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4146 "^" "(Cryptol::^)" ) (Reference.Schema.mk
  [(Reference.Parameter.mk 77 .value)] [(.constructor "PC PLogic" [(.var (Reference.Parameter.mk
  77 .value))])] (.constructor "TC TCFun" [(.var (Reference.Parameter.mk 77 .value)),
  (.constructor "TC TCFun" [(.var (Reference.Parameter.mk 77 .value)), (.var
  (Reference.Parameter.mk 77 .value))])])) .primitive)

/-- Source declaration 4 in dependency order. -/
@[expose] def declaration3 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4129 "number" "Cryptol::number" ) (Reference.Schema.mk
  [(Reference.Parameter.mk 33 .number), (Reference.Parameter.mk 34 .value)] [(.constructor
  "PC PLiteral" [(.var (Reference.Parameter.mk 33 .number)), (.var (Reference.Parameter.mk 34
  .value))])] (.var (Reference.Parameter.mk 34 .value))) .primitive)

/-- Source declaration 5 in dependency order. -/
@[expose] def declaration4 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4786 "SHR" "algorithms::SHA2::Notation::SHR" )
  (Reference.Schema.mk [(Reference.Parameter.mk 1282 .number), (Reference.Parameter.mk 1283
  .number)] [(.constructor "PC PFin" [(.var (Reference.Parameter.mk 1283 .number))]), (.synonym
  (Reference.Name.mk 4126 "<" "(Cryptol::<)" ) [(.var (Reference.Parameter.mk 1282 .number)),
  (.var (Reference.Parameter.mk 1283 .number))] (.constructor "PC PGeq" [(.var
  (Reference.Parameter.mk 1283 .number)), (.constructor "TF TCAdd" [(.number 1), (.var
  (Reference.Parameter.mk 1282 .number))])]))] (.constructor "TC TCFun" [(.synonym
  (Reference.Name.mk 4101 "Word" "Cryptol::Word" ) [(.var (Reference.Parameter.mk 1283 .number))]
  (.constructor "TC TCSeq" [(.var (Reference.Parameter.mk 1283 .number)), (.constructor
  "TC TCBit" [])])), (.synonym (Reference.Name.mk 4101 "Word" "Cryptol::Word" ) [(.var
  (Reference.Parameter.mk 1283 .number))] (.constructor "TC TCSeq" [(.var (Reference.Parameter.mk
  1283 .number)), (.constructor "TC TCBit" [])]))])) (.expression (.typeAbs
  (Reference.Parameter.mk 1282 .number) (.typeAbs (Reference.Parameter.mk 1283 .number)
  (.proofAbs (.constructor "PC PFin" [(.var (Reference.Parameter.mk 1283 .number))]) (.proofAbs
  (.synonym (Reference.Name.mk 4126 "<" "(Cryptol::<)" ) [(.var (Reference.Parameter.mk 1282
  .number)), (.var (Reference.Parameter.mk 1283 .number))] (.constructor "PC PGeq" [(.var
  (Reference.Parameter.mk 1283 .number)), (.constructor "TF TCAdd" [(.number 1), (.var
  (Reference.Parameter.mk 1282 .number))])])) (.abs (Reference.Name.mk 4796 "x" "x" ) (.synonym
  (Reference.Name.mk 4101 "Word" "Cryptol::Word" ) [(.var (Reference.Parameter.mk 1283 .number))]
  (.constructor "TC TCSeq" [(.var (Reference.Parameter.mk 1283 .number)), (.constructor
  "TC TCBit" [])])) (.app (.app (.proofApp (.proofApp (.typeApp (.typeApp (.typeApp (.var
  (Reference.Name.mk 4224 ">>" "(Cryptol::>>)" )) (.var (Reference.Parameter.mk 1283 .number)))
  (.constructor "TC TCInteger" [])) (.constructor "TC TCBit" [])))) (.var (Reference.Name.mk 4796
  "x" "x" ))) (.proofApp (.typeApp (.typeApp (.var (Reference.Name.mk 4129 "number"
  "Cryptol::number" )) (.var (Reference.Parameter.mk 1282 .number))) (.constructor "TC TCInteger"
  [])))))))))))

/-- Source declaration 6 in dependency order. -/
@[expose] def declaration5 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4787 "ROTR" "algorithms::SHA2::Notation::ROTR" )
  (Reference.Schema.mk [(Reference.Parameter.mk 1291 .number), (Reference.Parameter.mk 1292
  .number)] [(.constructor "PC PFin" [(.var (Reference.Parameter.mk 1292 .number))]), (.synonym
  (Reference.Name.mk 4126 "<" "(Cryptol::<)" ) [(.var (Reference.Parameter.mk 1291 .number)),
  (.var (Reference.Parameter.mk 1292 .number))] (.constructor "PC PGeq" [(.var
  (Reference.Parameter.mk 1292 .number)), (.constructor "TF TCAdd" [(.number 1), (.var
  (Reference.Parameter.mk 1291 .number))])]))] (.constructor "TC TCFun" [(.synonym
  (Reference.Name.mk 4101 "Word" "Cryptol::Word" ) [(.var (Reference.Parameter.mk 1292 .number))]
  (.constructor "TC TCSeq" [(.var (Reference.Parameter.mk 1292 .number)), (.constructor
  "TC TCBit" [])])), (.synonym (Reference.Name.mk 4101 "Word" "Cryptol::Word" ) [(.var
  (Reference.Parameter.mk 1292 .number))] (.constructor "TC TCSeq" [(.var (Reference.Parameter.mk
  1292 .number)), (.constructor "TC TCBit" [])]))])) (.expression (.typeAbs
  (Reference.Parameter.mk 1291 .number) (.typeAbs (Reference.Parameter.mk 1292 .number)
  (.proofAbs (.constructor "PC PFin" [(.var (Reference.Parameter.mk 1292 .number))]) (.proofAbs
  (.synonym (Reference.Name.mk 4126 "<" "(Cryptol::<)" ) [(.var (Reference.Parameter.mk 1291
  .number)), (.var (Reference.Parameter.mk 1292 .number))] (.constructor "PC PGeq" [(.var
  (Reference.Parameter.mk 1292 .number)), (.constructor "TF TCAdd" [(.number 1), (.var
  (Reference.Parameter.mk 1291 .number))])])) (.abs (Reference.Name.mk 4799 "x" "x" ) (.synonym
  (Reference.Name.mk 4101 "Word" "Cryptol::Word" ) [(.var (Reference.Parameter.mk 1292 .number))]
  (.constructor "TC TCSeq" [(.var (Reference.Parameter.mk 1292 .number)), (.constructor
  "TC TCBit" [])])) (.app (.app (.proofApp (.proofApp (.typeApp (.typeApp (.typeApp (.var
  (Reference.Name.mk 4226 ">>>" "(Cryptol::>>>)" )) (.var (Reference.Parameter.mk 1292 .number)))
  (.constructor "TC TCInteger" [])) (.constructor "TC TCBit" [])))) (.var (Reference.Name.mk 4799
  "x" "x" ))) (.proofApp (.typeApp (.typeApp (.var (Reference.Name.mk 4129 "number"
  "Cryptol::number" )) (.var (Reference.Parameter.mk 1291 .number))) (.constructor "TC TCInteger"
  [])))))))))))

/-- Source declaration 7 in dependency order. -/
@[expose] def declaration6 : Reference.Decl :=
  (Reference.Decl.mk (Reference.Name.mk 4839 "sigma_256_0"
  "algorithms::SHA2::Functions::sigma_256_0" ) (Reference.Schema.mk [(Reference.Parameter.mk 1571
  .number)] [(.synonym (Reference.Name.mk 4126 "<" "(Cryptol::<)" ) [(.number 18), (.var
  (Reference.Parameter.mk 1571 .number))] (.constructor "PC PGeq" [(.var (Reference.Parameter.mk
  1571 .number)), (.number 19)])), (.synonym (Reference.Name.mk 4126 "<" "(Cryptol::<)" )
  [(.number 7), (.var (Reference.Parameter.mk 1571 .number))] (.constructor "PC PGeq" [(.var
  (Reference.Parameter.mk 1571 .number)), (.number 8)])), (.synonym (Reference.Name.mk 4126 "<"
  "(Cryptol::<)" ) [(.number 3), (.var (Reference.Parameter.mk 1571 .number))] (.constructor
  "PC PGeq" [(.var (Reference.Parameter.mk 1571 .number)), (.number 4)])), (.constructor
  "PC PFin" [(.var (Reference.Parameter.mk 1571 .number))])] (.constructor "TC TCFun" [(.synonym
  (Reference.Name.mk 4101 "Word" "Cryptol::Word" ) [(.var (Reference.Parameter.mk 1571 .number))]
  (.constructor "TC TCSeq" [(.var (Reference.Parameter.mk 1571 .number)), (.constructor
  "TC TCBit" [])])), (.synonym (Reference.Name.mk 4101 "Word" "Cryptol::Word" ) [(.var
  (Reference.Parameter.mk 1571 .number))] (.constructor "TC TCSeq" [(.var (Reference.Parameter.mk
  1571 .number)), (.constructor "TC TCBit" [])]))])) (.expression (.typeAbs
  (Reference.Parameter.mk 1571 .number) (.proofAbs (.synonym (Reference.Name.mk 4126 "<"
  "(Cryptol::<)" ) [(.number 18), (.var (Reference.Parameter.mk 1571 .number))] (.constructor
  "PC PGeq" [(.var (Reference.Parameter.mk 1571 .number)), (.number 19)])) (.proofAbs (.synonym
  (Reference.Name.mk 4126 "<" "(Cryptol::<)" ) [(.number 7), (.var (Reference.Parameter.mk 1571
  .number))] (.constructor "PC PGeq" [(.var (Reference.Parameter.mk 1571 .number)), (.number
  8)])) (.proofAbs (.synonym (Reference.Name.mk 4126 "<" "(Cryptol::<)" ) [(.number 3), (.var
  (Reference.Parameter.mk 1571 .number))] (.constructor "PC PGeq" [(.var (Reference.Parameter.mk
  1571 .number)), (.number 4)])) (.proofAbs (.constructor "PC PFin" [(.var
  (Reference.Parameter.mk 1571 .number))]) (.abs (Reference.Name.mk 4863 "x" "x" ) (.synonym
  (Reference.Name.mk 4101 "Word" "Cryptol::Word" ) [(.var (Reference.Parameter.mk 1571 .number))]
  (.constructor "TC TCSeq" [(.var (Reference.Parameter.mk 1571 .number)), (.constructor
  "TC TCBit" [])])) (.app (.app (.proofApp (.typeApp (.var (Reference.Name.mk 4146 "^"
  "(Cryptol::^)" )) (.synonym (Reference.Name.mk 4101 "Word" "Cryptol::Word" ) [(.var
  (Reference.Parameter.mk 1571 .number))] (.constructor "TC TCSeq" [(.var (Reference.Parameter.mk
  1571 .number)), (.constructor "TC TCBit" [])])))) (.app (.app (.proofApp (.typeApp (.var
  (Reference.Name.mk 4146 "^" "(Cryptol::^)" )) (.synonym (Reference.Name.mk 4101 "Word"
  "Cryptol::Word" ) [(.var (Reference.Parameter.mk 1571 .number))] (.constructor "TC TCSeq"
  [(.var (Reference.Parameter.mk 1571 .number)), (.constructor "TC TCBit" [])])))) (.app
  (.proofApp (.proofApp (.typeApp (.typeApp (.var (Reference.Name.mk 4787 "ROTR"
  "algorithms::SHA2::Notation::ROTR" )) (.number 7)) (.var (Reference.Parameter.mk 1571
  .number))))) (.var (Reference.Name.mk 4863 "x" "x" )))) (.app (.proofApp (.proofApp (.typeApp
  (.typeApp (.var (Reference.Name.mk 4787 "ROTR" "algorithms::SHA2::Notation::ROTR" )) (.number
  18)) (.var (Reference.Parameter.mk 1571 .number))))) (.var (Reference.Name.mk 4863 "x" "x"
  ))))) (.app (.proofApp (.proofApp (.typeApp (.typeApp (.var (Reference.Name.mk 4786 "SHR"
  "algorithms::SHA2::Notation::SHR" )) (.number 3)) (.var (Reference.Parameter.mk 1571
  .number))))) (.var (Reference.Name.mk 4863 "x" "x" ))))))))))))

/-- The official frontend's fully instantiated entry point. -/
@[expose] def root : SourceRoot :=
  (SourceRoot.mk "(sigma_256_0 : [32] -> [32])" (.proofApp (.proofApp (.proofApp (.proofApp
  (.typeApp (.var (Reference.Name.mk 4839 "sigma_256_0"
  "algorithms::SHA2::Functions::sigma_256_0" )) (.number 32)))))) (Reference.Schema.mk [] []
  (.constructor "TC TCFun" [(.constructor "TC TCSeq" [(.number 32), (.constructor "TC TCBit"
  [])]), (.constructor "TC TCSeq" [(.number 32), (.constructor "TC TCBit" [])])])))

/-- The exact exported scalar bundle, retaining its provenance metadata. -/
@[expose] def bundle : SourceBundle :=
  (SourceBundle.mk "61dd17b0c45ddf8c5c1e952afd5e789c4dc4ec4b" [root] [(.nonrecursive
  declaration0), (.nonrecursive declaration1), (.nonrecursive declaration2), (.nonrecursive
  declaration3), (.nonrecursive declaration4), (.nonrecursive declaration5), (.nonrecursive
  declaration6)] [(SourceModule.mk "shared::CRC::Main" "shared/CRC/Main.cry"
  "56b314861a7e7537b8a72fcfc864c808f1836d94dd98fec1abcb5ed9f825f258" []), (SourceModule.mk
  "packaging::Hash" "packaging/Hash.cry"
  "f2ff656ec1cc63b3ad86ed2c8208baafa5c22814ecd60c8fcaa4c183ef4f9406" []), (SourceModule.mk
  "algorithms::SHA2::Main" "algorithms/SHA2/Main.cry"
  "dfbe7d0b4b401cb9141989dd38e35aad8d873c47c3e0bca6a00b3a21abb9906e" []), (SourceModule.mk
  "Cryptol" "$builtin/Cryptol" "8ace6e6308a863e17355e0b8289ea52eb16c12e36b51e76f7ac668bf03a7f59e"
  []), (SourceModule.mk "Cryptol::Reference" "$builtin/Cryptol::Reference"
  "381f85753adcb40b599f271116e3cf2b52003f25f801d2817f6ccef86ef19bab" []), (SourceModule.mk
  "algorithms::SHA2::Notation" "algorithms/SHA2/Notation.cry"
  "6475ab9e4bdb6245533642378be6f554eab368078fc4cdda5ba147a2bd2fd865" []), (SourceModule.mk
  "algorithms::SHA2::Preprocessing" "algorithms/SHA2/Preprocessing.cry"
  "953df0b7fea1ef5f7252d9860a17b925ebfc5a675042ad873f49a0ce1fdbd01e" []), (SourceModule.mk
  "algorithms::SHA2::Functions" "algorithms/SHA2/Functions.cry"
  "e0f507136dbe9bcc0a38c5a8e76b1b6a80626c0c3cd392c3d3fa305d30278867" []), (SourceModule.mk
  "algorithms::SHA2::SHA224__where" "algorithms/SHA2/SHA224.cry"
  "0670352e83ed097a08809d536e5617e9d37eb52ff3e16c8d1f9db6e225942e5d" []), (SourceModule.mk
  "algorithms::HMAC::Main" "algorithms/HMAC/Main.cry"
  "b853e76b721f5abe70e0764c2b1548b6fc37d85bb05cd10d95b285f19a4f4cbe" []), (SourceModule.mk
  "algorithms::PBKDF::Main" "algorithms/PBKDF/Main.cry"
  "528f05bb80868f4666da40b24e95a5cb2cc0795a36f65c8aa4f91f0b098dfff5" []), (SourceModule.mk
  "algorithms::SHA2::SHA224" "algorithms/SHA2/SHA224.cry"
  "0670352e83ed097a08809d536e5617e9d37eb52ff3e16c8d1f9db6e225942e5d" []), (SourceModule.mk
  "algorithms::SHA2::SHA256__where" "algorithms/SHA2/SHA256.cry"
  "261721ba3eee4b4c23c9af174a4ca078c05d37c627df788f3b25c10cbc1fb846" []), (SourceModule.mk
  "algorithms::SHA2::SHA256" "algorithms/SHA2/SHA256.cry"
  "261721ba3eee4b4c23c9af174a4ca078c05d37c627df788f3b25c10cbc1fb846" []), (SourceModule.mk
  "algorithms::SHA2::SHA384__where" "algorithms/SHA2/SHA384.cry"
  "c68d3db323b5e1e7cf5e344cfcff887a3642f84ba78a6b5837b42f189bf4da0d" []), (SourceModule.mk
  "algorithms::SHA2::SHA384" "algorithms/SHA2/SHA384.cry"
  "c68d3db323b5e1e7cf5e344cfcff887a3642f84ba78a6b5837b42f189bf4da0d" []), (SourceModule.mk
  "algorithms::SHA2::SHA512__where" "algorithms/SHA2/SHA512.cry"
  "406bd80c188bc699a97451b94dea8168dd0c5bb4a6735f862df47debc2184979" []), (SourceModule.mk
  "algorithms::SHA2::SHA512" "algorithms/SHA2/SHA512.cry"
  "406bd80c188bc699a97451b94dea8168dd0c5bb4a6735f862df47debc2184979" []), (SourceModule.mk
  "algorithms::SHA2::SHA512_224__where" "algorithms/SHA2/SHA512_224.cry"
  "1c6491ee06fafba4ac8cae15814ccfb60896baf7bb302d4b30e4fc2e30a0e3e9" []), (SourceModule.mk
  "algorithms::SHA2::SHA512_224" "algorithms/SHA2/SHA512_224.cry"
  "1c6491ee06fafba4ac8cae15814ccfb60896baf7bb302d4b30e4fc2e30a0e3e9" []), (SourceModule.mk
  "algorithms::SHA2::SHA512_256__where" "algorithms/SHA2/SHA512_256.cry"
  "86ed1e643c1215838611e20365ff210940ef4a194b8a04871776a99b766414a1" []), (SourceModule.mk
  "algorithms::SHA2::SHA512_256" "algorithms/SHA2/SHA512_256.cry"
  "86ed1e643c1215838611e20365ff210940ef4a194b8a04871776a99b766414a1" []), (SourceModule.mk
  "algorithms::Keccak::Types" "algorithms/Keccak/Types.cry"
  "d54d46d853ab3510886a28d9785f65e90d08b4e0923d109f07c818067920d7e8" []), (SourceModule.mk
  "algorithms::Keccak::StateConversions" "algorithms/Keccak/StateConversions.cry"
  "44d90d9709262d59c0eb2f98beb871522bbba6d20f4a5851276e65525b064153" []), (SourceModule.mk
  "shared::LFSR::Main" "shared/LFSR/Main.cry"
  "b7780dbf58e7d8c6dfbabf4379f6b2596ec99e022a7f760da845e3d056868090" []), (SourceModule.mk
  "shared::common::utils::BitVector" "shared/common/utils/BitVector.cry"
  "57fef1d359b74d6eb987acde32533796e92082e2b8830ba5965febef3c6397b6" []), (SourceModule.mk
  "algorithms::Keccak::StepMappings" "algorithms/Keccak/StepMappings.cry"
  "df3593838198ebeaacf5cbe9c013272a868886b5e1708f978e1c2bc1b3c861d8" []), (SourceModule.mk
  "shared::sponge::Main" "shared/sponge/Main.cry"
  "ccc5b439840eef394c2ae8eff4ba54d4edd75346c42418c7d4e795c17aa14947" []), (SourceModule.mk
  "algorithms::Keccak::Main" "algorithms/Keccak/Main.cry"
  "8ce5d7498fa929f71af881e68224f8ffd73b3b3bc51858e5c4c87db86febd60d" []), (SourceModule.mk
  "algorithms::SHA3::SHA3_224__where" "algorithms/SHA3/SHA3_224.cry"
  "66661a73347b334d20e82c7f024dacbfeff0d970fd8c2637b21cf345bda642b2" []), (SourceModule.mk
  "algorithms::SHA3::SHA3_224" "algorithms/SHA3/SHA3_224.cry"
  "66661a73347b334d20e82c7f024dacbfeff0d970fd8c2637b21cf345bda642b2" []), (SourceModule.mk
  "algorithms::SHA3::SHA3_256__where" "algorithms/SHA3/SHA3_256.cry"
  "14076be6ca363cf5d5c500f87db67e336e839f71f55e4d983ead3e68882c8af1" []), (SourceModule.mk
  "algorithms::SHA3::SHA3_256" "algorithms/SHA3/SHA3_256.cry"
  "14076be6ca363cf5d5c500f87db67e336e839f71f55e4d983ead3e68882c8af1" []), (SourceModule.mk
  "algorithms::SHA3::SHA3_384__where" "algorithms/SHA3/SHA3_384.cry"
  "d2d9e0d817c6a6662a51c79f9e19f5720e145d3cda059ad3a8114a0db405dbfb" []), (SourceModule.mk
  "algorithms::SHA3::SHA3_384" "algorithms/SHA3/SHA3_384.cry"
  "d2d9e0d817c6a6662a51c79f9e19f5720e145d3cda059ad3a8114a0db405dbfb" []), (SourceModule.mk
  "algorithms::SHA3::SHA3_512__where" "algorithms/SHA3/SHA3_512.cry"
  "5db178aa522ac800f4eaf6ae2d8a6bc1146385de049ece8b22887febc13aae0a" []), (SourceModule.mk
  "algorithms::SHA3::SHA3_512" "algorithms/SHA3/SHA3_512.cry"
  "5db178aa522ac800f4eaf6ae2d8a6bc1146385de049ece8b22887febc13aae0a" []), (SourceModule.mk
  "algorithms::SHAKE::Main" "algorithms/SHAKE/Main.cry"
  "74472c53273cbe1683eff5c0daeb71dcec300b5daab5ea67611659a80a1bebcd" []), (SourceModule.mk
  "algorithms::AES::Types" "algorithms/AES/Types.cry"
  "20ed6d7a14f2f28d75e5df1a6d8706b769735fd5005fb3e4828eeeea72de333c" []), (SourceModule.mk
  "algorithms::AES::GF28" "algorithms/AES/GF28.cry"
  "89f0446b8d30f47ce0fa7e324fe70da58bce50de64801717d97b6f3f20ebc782" []), (SourceModule.mk
  "shared::common::utils::Prime" "shared/common/utils/Prime.cry"
  "f032a0ec6880ddc5ae1b43c4c9d4108b0046f0f86e644c7301cef7014554e4ba" []), (SourceModule.mk
  "shared::algebra::Polynomial::GF2" "shared/algebra/Polynomial/GF2.cry"
  "36502a979d119733f40fc2f028d9e653fb087b0b18b2b945ae694d95a028d7d0" []), (SourceModule.mk
  "algorithms::AES::SBox" "algorithms/AES/SBox.cry"
  "f7cc6310c9985104306976c8f5ac89316c044d2dbf27b23d111e492f5b5dca73" []), (SourceModule.mk
  "algorithms::AES::Cipher" "algorithms/AES/Cipher.cry"
  "230be98f59f225712bae2e31fb81d8a2054ed5befb6e7cd99ced4080e9e676ff" []), (SourceModule.mk
  "algorithms::AES::KeyExpansion" "algorithms/AES/KeyExpansion.cry"
  "3981c3c444969ba09adda5c520a169e8071d231b605f7139ac13810cc30c6e19" []), (SourceModule.mk
  "algorithms::AES::Main" "algorithms/AES/Main.cry"
  "663f3502a04fcd677ce8f28af820350c64d1c4d32619b6a0c9ae087291e58906" []), (SourceModule.mk
  "shared::CRC::CRC32_IEEE_802_3_Ethernet__where" "shared/CRC/CRC32_IEEE_802_3_Ethernet.cry"
  "5e300f97248dd498af0f01a7ea1905ee2042a9b380b3775cf1b552e786b1d68f" []), (SourceModule.mk
  "shared::CRC::CRC32_IEEE_802_3_Ethernet" "shared/CRC/CRC32_IEEE_802_3_Ethernet.cry"
  "5e300f97248dd498af0f01a7ea1905ee2042a9b380b3775cf1b552e786b1d68f" []), (SourceModule.mk
  "FoundationReferences" "$entry/FoundationReferences.cry"
  "caf0e9fae38d70d0cdc915cd45b8be918e0ba9b95b95b0fada22d5c8941c9a40" [])] [] [
  "cffd4082d3347aba60c131d2e7d33f8b8fdfaf6afa4aedd52d8d2fff7bb30a2e" ])

end Cryptol.Bridge.ImportedScalarSource
