/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.MerkleCollision

/-!
# Ordinary public Merkle witness and obstruction applications

This consumer uses the named actual adversary and native mass bound through public imports only.
-/

public section
namespace GXMSS.MerkleObstructionProbe
open GXMSS.IntervalMerkle GXMSS.Interval.Unforgeability GXMSS.Reductions
open IncomparableEncoding OracleSpec

/-- The registered interval reduction supplies the named Merkle obstruction bound. -/
theorem bound {PP T X H M R : Type} {h w v : ℕ}
    [SampleableType H] [SampleableType R]
    [DecidableEq T] [DecidableEq X] [DecidableEq H] [DecidableEq M]
    [DecidableEq (GXMSS.Signature R H h v)]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (I : Interval h) (hv : 0 < v)
    (A : SyncSignatureUnforgeability.Adversary unifSpec (GXMSS.PublicKey PP H)
      (Epoch h) M (GXMSS.Signature R H h v)) : MerkleObstructionBound P enc K I hv A :=
  merkleObstructionMass_le_advantage P enc K I hv A

/-- The public finder detects every different complete opening against an honest root. -/
theorem honest_difference {PP T X H : Type} {h w v : ℕ} [DecidableEq H]
    (P : HashInstance PP T X H h w v) (pp : PP)
    (leaves : Fin (2 ^ h) → Fin v → H) (e : Fin (2 ^ h))
    (ys : Fin v → H) (path : Fin h → H)
    (hne : (leaves e, P.authPath pp leaves e) ≠ (ys, path))
    (hroot : P.recoverRoot pp e ys path = P.merkleRoot pp leaves) :
    (P.findMerkleCollision pp e (leaves e) ys (P.authPath pp leaves e) path).isSome :=
  P.findMerkleCollision_isSome_of_honest pp leaves e ys path hne hroot

end GXMSS.MerkleObstructionProbe
