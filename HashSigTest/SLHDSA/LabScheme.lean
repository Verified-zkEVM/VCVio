/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.LabScheme
public import HashSig.SLHDSA.Security.KeyDiscipline
public import HashSig.SLHDSA.Concrete.FIPS

/-!
# The lab scheme at the shipped bundles

At every SHAKE bundle the lab experiment elaborates at the derivation-world types the secret-free
run uses, the lifted transcript experiment of the secret-free scheme runs the lab forger's
program, lab key generation makes no hash query, and lab signing makes no tweakable-hash query.
At SLH-DSA-SHAKE-128s lab key generation is the lab root of the top-layer tree, a lab callback at
a ledger address reads that address's node, a lab FORS leaf of a reachable FORS tree touches its
secret and reads the leaf, and in the canonical graph the only child of a later hash step of a
reachable WOTS+ chain is the chain cell before it.
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

/-- A query of the hash oracles. -/
def IsHashQuery {vp : ValidatedParams} (core : CorePrimitives vp.params) :
    (labSpec core).Domain → Prop :=
  fun t => ∃ q, t = .inl (.inl (.inr q))

/-- A tweakable-hash query. -/
def IsThashQuery {vp : ValidatedParams} (core : CorePrimitives vp.params) :
    (labSpec core).Domain → Prop :=
  fun t => ∃ s k xs, t = .inl (.inl (.inr (.inl (.thash s k xs))))

open Classical in
/-- At every SHAKE bundle lab key generation makes no hash query. -/
example (vp : ValidatedParams) :
    IsQueryBoundP (labKeygen (shakeCore vp)) (IsHashQuery (shakeCore vp)) 0 :=
  labKeygen_pred _ (Q := fun oa => IsQueryBoundP oa _ 0) (fun x => isQueryBoundP_pure _ x 0)
    (fun _ _ h h' => isQueryBoundP_bind h fun x _ => h' x)
    (fun _ => (isQueryBoundP_query_iff _ _ 0).2 fun ⟨_, h⟩ => nomatch h)
    (fun c => by
      rcases c with _ | _ <;> exact (isQueryBoundP_query_iff _ _ 0).2 fun ⟨_, h⟩ => nomatch h)

open Classical in
/-- At every SHAKE bundle lab signing makes no tweakable-hash query: its one hash query is
`H_msg`. -/
example (vp : ValidatedParams) (pkSeed : (shakeCore vp).PkSeed) (msg : List Byte)
    (pkRoot R : (shakeCore vp).Y) :
    IsQueryBoundP (labSignInternal (shakeCore vp) pkSeed msg pkRoot R)
      (IsThashQuery (shakeCore vp)) 0 := by
  refine labSignInternal_pred _ (Q := fun oa => IsQueryBoundP oa _ 0)
    (fun x => isQueryBoundP_pure _ x 0) (fun _ _ h h' => isQueryBoundP_bind h fun x _ => h' x)
    (fun _ => (isQueryBoundP_query_iff _ _ 0).2 fun ⟨_, _, _, h⟩ => nomatch h)
    (fun c => by
      rcases c with _ | _ <;>
        exact (isQueryBoundP_query_iff _ _ 0).2 fun ⟨_, _, _, h⟩ => nomatch h) _ _ _ _ ?_
  simp only [PublicHash.hmsg, HasQuery.instOfMonadLift_query]
  exact (isQueryBoundP_query_iff (spec := labSpec _) _
    (.inl (.inl (.inr (.inl (.hmsg R pkSeed pkRoot msg))))) 0).2 fun ⟨_, _, _, h⟩ => nomatch h

/-- The validated parameters of SLH-DSA-SHAKE-128s. -/
abbrev vp128s : ValidatedParams := FipsParameterSet.SLHDSA_SHAKE_128s.validatedParams

/-- At SLH-DSA-SHAKE-128s the lab key generation is the lab XMSS root of the top-layer tree. -/
example : labKeygen (shakeCore vp128s) =
    labXmssNode (shakeCore vp128s) (GeneralHypertree.layerAdrs (7 - 1) 0) 9 0 :=
  rfl

/-- At SLH-DSA-SHAKE-128s the lab `F` at the first hash step of a reachable WOTS+ chain reads the
label of the step's node, whatever its input. -/
example (pos : LayerPosition vp128s) (i : Fin vp128s.params.len) (y : (shakeCore vp128s).Y) :
    labF (shakeCore vp128s) ((wotsChainAdrs (wotsInstanceAdrs pos) i.val).setHashAddress 0) y =
      readCell (some (.inr ⟨_, _,
        wotsChainAdrs_setHashAddress_mem_constructionAddresses (t := 0) pos i (by decide), rfl⟩)) :=
  labNode_of_mem _ (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i (by decide))

/-- At SLH-DSA-SHAKE-128s a lab FORS leaf of a reachable FORS tree touches its secret and reads
the leaf. -/
example (pos : BottomPosition vp128s) (tree : Fin vp128s.params.k) {t : ℕ}
    (ht : t / 2 ^ vp128s.params.a = tree.val) :
    labForsLeaf (shakeCore vp128s) pos.forsAdrs t = (do
      touchCell (some (.inl (.inl ⟨_, _, Adrs.isSecretKey_forsSkAdrs pos.forsAdrs t, rfl⟩)))
      readCell (some (.inr ⟨_, _, forsLeafAdrs_mem_constructionAddresses pos tree ht, rfl⟩))) :=
  labForsLeaf_of_mem _ (forsLeafAdrs_mem_constructionAddresses pos tree ht)

/-- At SLH-DSA-SHAKE-128s, in the canonical graph, the only child of hash step `1` of a reachable
WOTS+ chain is the label of step `0`, cell `1` of the chain. -/
example (pkSeed : (shakeCore vp128s).PkSeed) (pos : LayerPosition vp128s)
    (i : Fin vp128s.params.len) :
    (slhGraph (shakeCore vp128s) pkSeed).ch ⟨_, _,
        wotsChainAdrs_setHashAddress_mem_constructionAddresses (t := 1) pos i (by decide), rfl⟩ =
      [.inr ⟨_, _,
        wotsChainAdrs_setHashAddress_mem_constructionAddresses (t := 0) pos i (by decide), rfl⟩] := by
  rw [slhGraph_ch_wotsChainAdrs_setHashAddress _
      (Concrete.keyDiscipline_shakePrimitives _
        (fipsApprovedAddressBounds .SLHDSA_SHAKE_128s).toCanonicalAddressBounds) pkSeed
      (wotsChainAdrs_setHashAddress_mem_constructionAddresses (t := 1) pos i (by decide)),
    pathCell_succ_of_mem _ _
      (wotsChainAdrs_setHashAddress_mem_constructionAddresses (t := 0) pos i (by decide))]
  rfl

end SLHDSA.LabSchemeTest
