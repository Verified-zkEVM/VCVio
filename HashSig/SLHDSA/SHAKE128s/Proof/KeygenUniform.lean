/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.KeygenFresh

/-! Distribution of the actual public key under the initially empty shared oracle. -/

@[expose] public section

open OracleComp OracleSpec ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SlhDsaSecurity.KeygenUniform

def splitOutput (output : HashOutput) : Digest × BitVec 112 :=
  (Hashing.truncate output, output.extractLsb' 0 112)

theorem splitOutput_bijective : Function.Bijective splitOutput := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro left right h
    have hleft : Hashing.truncate left ++ left.extractLsb' 0 112 = left :=
      BitVec.extractLsb'_append_extractLsb'
    have hright : Hashing.truncate right ++ right.extractLsb' 0 112 = right :=
      BitVec.extractLsb'_append_extractLsb'
    rw [← hleft, ← hright]
    exact congrArg₂ HAppend.hAppend (congrArg Prod.fst h) (congrArg Prod.snd h)
  · norm_num [HashOutput, Digest, messageDigestBytes, n, Fintype.card_prod, card_bitVec]

theorem truncate_uniform :
    𝒟[Hashing.truncate <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒟[($ᵗ Digest : ProbComp Digest)] := by
  have hmap : Hashing.truncate <$> ($ᵗ HashOutput : ProbComp HashOutput) =
      Prod.fst <$> (splitOutput <$> ($ᵗ HashOutput : ProbComp HashOutput)) := by
    simp [Functor.map_map, splitOutput]
  have hsplit := evalDist_map_bijective_uniform_cross (α := HashOutput)
    (β := Digest × BitVec 112) splitOutput splitOutput_bijective
  rw [hmap, evalDist_map, hsplit, ← evalDist_map]
  exact evalDist_map_fst_uniformSample_prod

attribute [local irreducible] Scheme.keygenInternal

end SlhDsaSecurity.KeygenUniform
