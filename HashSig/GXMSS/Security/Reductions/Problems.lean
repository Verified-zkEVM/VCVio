/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Completeness
import all HashSig.GXMSS.Completeness
public import HashSig.GXMSS.Security.Auxiliary.ChainSelection
import all HashSig.GXMSS.Security.Auxiliary.ChainSelection
public import HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
import all HashSig.GXMSS.Security.Auxiliary.ChainWitnesses
public import HashSig.GXMSS.Security.Auxiliary.Encoding
import all HashSig.GXMSS.Security.Auxiliary.Encoding
public import HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
import all HashSig.GXMSS.Security.Auxiliary.MerkleWitnesses
public import HashSig.GXMSS.Security.Auxiliary.SourceGames
import all HashSig.GXMSS.Security.Auxiliary.SourceGames
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTPRE
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCR
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTUD
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Monadic
public import VCVio.CryptoFoundations.SyncSignatureAlg
import all VCVio.CryptoFoundations.SyncSignatureAlg
public import VCVio.EvalDist.Monad.UniformTable
public import VCVio.OracleComp.EvalDist.Sum

/-!
# Authoritative hash reduction problems

The Merkle, chain and encoding reductions use their fixed standalone target capacities and
original input embeddings.
-/

public section
namespace GXMSS.Reductions
open Encoding ENNReal OracleComp OracleSpec GXMSS.Security TweakableHash
variable {PP T X H M R E S : Type} {h w v n radix : ℕ}
/-- Standalone Merkle target-collision problem with the complete registration capacity. -/
@[expose] def merkleTCRProblem (hash : HashInstance PP T X H h w v) :=
  SM_DT_TCR_Problem.standalone hash.thf (2 * (2 ^ h) * v * (2 ^ w))
/-- Standalone chain target-collision problem with the complete positive-step capacity. -/
@[expose] def chainTCRProblem (hash : HashInstance PP T X H h w v) :=
  SM_DT_TCR_Problem.standalone hash.thf ((2 ^ h) * v * (2 ^ w))
/-- Encoding target-collision problem with the all-request record and retry budgets. -/
@[expose] def encodingTCRProblem [SampleableType R] (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (qs K : ℕ) :=
  Encoding.TargetCollisionResistance.Problem.mk enc
    (HashInstance.thf hash).seedGen ($ᵗ R) qs K
/-- One-target chain undetectability problem on the original digest input domain. -/
@[expose] noncomputable def chainUDProblem [SampleableType H]
    (hash : HashInstance PP T X H h w v) :=
  SM_DT_UD_Problem.standalone hash.thf hash.digestInput (HashInstance.digestInput hash).injective
    ($ᵗ H) ($ᵗ H) 1
/-- One-target chain preimage problem on the original digest input domain. -/
@[expose] def chainPREProblem (hash : HashInstance PP T X H h w v) :=
  SM_DT_PRE_Problem.standalone hash.thf hash.digestInput (HashInstance.digestInput hash).injective 1

end GXMSS.Reductions
