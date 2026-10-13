/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Unforgeability.MerkleCollision
public import HashSig.GXMSS.Security.Unforgeability.FirstChainCollision
public import HashSig.GXMSS.Security.Unforgeability.SecondChainCollision
public import HashSig.GXMSS.Security.Unforgeability.ReductionBound

/-!
# GXMSS strong-unforgeability bounds

Merkle and chain collision bounds and their composition into the concrete reduction inequality
for an incomparable encoding with at least two distinct global codewords.
-/
