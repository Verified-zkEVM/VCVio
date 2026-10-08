/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.LabScheme
public import HashSig.SLHDSA.Concrete.FIPS

/-!
# The lab scheme at the shipped bundles

At every SHAKE bundle the lab scheme, the lab forger and the lab experiment elaborate at the
derivation-world types the secret-free run uses, and the lifted transcript experiment of the
secret-free scheme runs the lab forger's program. At SLH-DSA-SHAKE-128s a lab callback at the key
of a ledger address reads that address's node, a lab FORS leaf of a reachable FORS tree touches
its secret and reads the leaf, and a lab WOTS+ chain at a reachable instance makes no public hash
query.
-/

public section

open OracleComp OracleSpec SignatureAlg

namespace SLHDSA.LabSchemeTest

open Security

/-- The core of the SHAKE bundle at validated parameters `vp`. -/
abbrev shakeCore (vp : ValidatedParams) : CorePrimitives vp.params :=
  (Concrete.shakePrimitives vp.params).core

/-- At every SHAKE bundle the lab experiment is a program over the lab oracles returning the
transcript of the secret-free scheme. -/
noncomputable example (vp : ValidatedParams) (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeed : (shakeCore vp).PkSeed)
    (adv : UnforgeableAdversary (romScheme (shakeCore vp) e optRand (pure pkSeed))) :
    OracleComp (labSpec (shakeCore vp)) (DeriveOutcome (shakeCore vp)) :=
  labExperiment (shakeCore vp) adv pkSeed

/-- At every SHAKE bundle the lab experiment is the transcript experiment of the lab scheme
against the lab forger. -/
example (vp : ValidatedParams) (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeed : (shakeCore vp).PkSeed)
    (adv : UnforgeableAdversary (romScheme (shakeCore vp) e optRand (pure pkSeed))) :
    labExperiment (shakeCore vp) adv pkSeed =
      unforgeableTranscriptExperiment (sigAlg := labScheme (shakeCore vp) optRand pkSeed)
        (labAdversary (shakeCore vp) adv pkSeed) :=
  rfl

/-- At every SHAKE bundle the lifted secret-free experiment runs the lab forger's program. -/
example (vp : ValidatedParams) (e : (shakeCore vp).SkSeed ≃ (shakeCore vp).Y)
    (optRand : PublicKeyCore (shakeCore vp) → ProbComp (shakeCore vp).Y)
    (pkSeed : (shakeCore vp).PkSeed)
    (adv : UnforgeableAdversary (romScheme (shakeCore vp) e optRand (pure pkSeed))) :
    liftComp (unforgeableTranscriptExperiment (deriveAdversary (shakeCore vp) adv pkSeed))
        (labSpec (shakeCore vp)) =
      unforgeableTranscriptExperiment
        (sigAlg := (deriveScheme (shakeCore vp) optRand pkSeed).map
          (labLiftHom (shakeCore vp)).toMonadHom)
        ⟨(labAdversary (shakeCore vp) adv pkSeed).main⟩ :=
  liftComp_unforgeableTranscriptExperiment_deriveAdversary (shakeCore vp) adv pkSeed

/-- The validated parameters of SLH-DSA-SHAKE-128s. -/
abbrev vp128s : ValidatedParams := FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams

/-- At SLH-DSA-SHAKE-128s the lab key generation is the lab XMSS root of the top-layer tree. -/
example (pkSeed : (shakeCore vp128s).PkSeed) :
    labKeygen (shakeCore vp128s) pkSeed =
      labXmssNode (shakeCore vp128s) pkSeed (GeneralHypertree.layerAdrs (7 - 1) 0) 9 0 :=
  rfl

/-- At SLH-DSA-SHAKE-128s the lab `F` at the first hash step of a reachable WOTS+ chain reads the
label of the step's node. -/
example (pkSeed : (shakeCore vp128s).PkSeed) (pos : LayerPosition vp128s)
    (i : Fin vp128s.params.len) (y : (shakeCore vp128s).Y) :
    labF (shakeCore vp128s) pkSeed ((wotsChainAdrs (wotsInstanceAdrs pos) i.val).setHashAddress 0)
      y = labRead (shakeCore vp128s) ⟨_, _,
        wotsChainAdrs_setHashAddress_mem_constructionAddresses (t := 0) pos i (by decide), rfl⟩ :=
  labNode_of_mem _ (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i (by decide)) _

/-- At SLH-DSA-SHAKE-128s a lab FORS leaf of a reachable FORS tree touches its secret and reads
the leaf. -/
example (pkSeed : (shakeCore vp128s).PkSeed) (pos : BottomPosition vp128s)
    (tree : Fin vp128s.params.k) {t : ℕ} (ht : t / 2 ^ vp128s.params.a = tree.val) :
    labForsLeaf (shakeCore vp128s) pkSeed pos.forsAdrs t = (do
      labTouch (shakeCore vp128s)
        (.inl (.inl ⟨_, _, Adrs.isSecretKey_forsSkAdrs pos.forsAdrs t, rfl⟩))
      labRead (shakeCore vp128s) ⟨_, _, forsLeafAdrs_mem_constructionAddresses pos tree ht, rfl⟩) :=
  labForsLeaf_of_mem _ _ (forsLeafAdrs_mem_constructionAddresses pos tree ht)

open Classical in
/-- At SLH-DSA-SHAKE-128s a lab WOTS+ chain of at most `w - 1` steps at a reachable instance makes
no public hash query. -/
example (pkSeed : (shakeCore vp128s).PkSeed) (pos : LayerPosition vp128s)
    (i : Fin vp128s.params.len) {s : ℕ} (hs : s ≤ vp128s.params.w - 1) :
    IsQueryBoundP (labChain (shakeCore vp128s) pkSeed (wotsInstanceAdrs pos) i s)
      (fun t => ∃ q, t = .inl (.inl (.inr q))) 0 :=
  isQueryBoundP_labChain_wotsInstanceAdrs _ pkSeed pos i hs _ fun _ h => h

end SLHDSA.LabSchemeTest
