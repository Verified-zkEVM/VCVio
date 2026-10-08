/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.HiddenUndrawn
public import HashSig.SLHDSA.Security.LabelReaders
public import HashSig.SLHDSA.Security.LabScheme
public import HashSig.SLHDSA.Security.RomSchemeUnion
public import VCVio.OracleComp.QueryTracking.RandomOracle.JointPotential
public import VCVio.OracleComp.QueryTracking.RandomOracle.Settled
import HashSig.SLHDSA.Security.CacheDecomposition
import HashSig.SLHDSA.Security.ComponentTraces

/-!
# Events of the deferred lab experiment on its final public cache

The lab experiment `labExperiment core adv pkSeed` runs in the deferred game of the canonical graph
`slhGraph core pkSeed`; the end fill then draws the touched cells, and secret seeds `s` are drawn
independently (`CanonicalGraph.deferredFillDraw`). The events of the run of SLH-DSA are read on the
transcript rebuilt with `s` (`DeriveOutcome.fill`) and on the cache that the filled state `st`
stands for at `s`, `((secretEncoding core e pkSeed).merge s ((slhGraph core pkSeed).toSplitCache
st)).fst`. This module carries those events to the final public cache `st.1`, where the joint
potential charges them.

* **Seed.** Under key separation no encoded derivation is a node point, so the split state reads
  the public cache at every encoded point
  (`exists_isSome_toSplitCache_fst_secretEncoding_enc_iff`); off such a point, the merged cache of
  the state is below the rebuilt cache (`merge_le_merge_toSplitCache`).
* **Target collisions.** A target collision of the rebuilt transcript is a target collision at a
  node key of the filled state (`tcHazard_of_runTargetCollision_fill`), since the transcript's
  public seed is the graph's.
* **Completed public misses.** A node point held by the cache of a state in which a child of the
  node is undrawn is a public entry; once a state with a larger public cache draws the children at
  that point's values, it is a conflict (`conflict_of_isSome_merge_fst_thash`). This applies to
  the WOTS+ chain step that the honest chain from a settled secret reaches
  (`conflict_of_chain?_of_cell_eq_none`) and to the FORS leaf of a settled secret
  (`conflict_of_forsSkAdrs_of_cell_eq_none`).
* **The verifier's queries.** A settled verification hashes the forgery's WOTS+ value at the step
  its message selects, at every layer the replay enters (`isSome_thash_of_forgerLayer`), and the
  revealed secret of every FORS leaf its digest selects (`isSome_thash_of_forgerDigest`).
* **Hidden values are undrawn before the fill.** In a state whose hidden cells for a transcript's
  log are undrawn (`HiddenUndrawn`), the cell of a WOTS+ chain value that the forgery's replay
  finds hidden, and of a FORS secret it finds unopened, is undrawn
  (`exists_cell_chainChild_eq_none_of_hiddenChainValue`,
  `exists_cell_forsSkAdrs_eq_none_of_unopenedCoord`). If verification settles before the fill, the
  verifier hashed that value while its cell was undrawn, so a hidden-value hit after the fill is a
  conflict (`conflict_of_hiddenHit`).
* **The settled verification.** On a run of the lab experiment in the deferred game, verification
  of the forgery in the rebuilt transcript is replayed to the transcript's verdict by the rebuilt
  cache of every conflict-free state extending the run's final state, off the seed hazard
  (`simulateQ_toPartialImpl_verifyInternalM_of_mem_support_deferredImpl_labExperiment`). The
  final state of every such run has its hidden cells undrawn
  (`hiddenUndrawn_of_mem_support_deferredImpl_labExperiment`).
* **The transport.** A target collision or hidden-value hit of the rebuilt transcript, a seed
  hazard of the split state, or a conflict, is a conflict, a target collision at a node key, or a
  seed hazard of the final public cache
  (`conflict_or_tcHazard_or_exists_isSome_of_mem_support_deferredFillDraw`).

## Scope

* Nothing here is probabilistic: the statements hold on every point of the support.
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec SignatureAlg
open scoped MergedCache

variable {vp : ValidatedParams} {core : CorePrimitives vp.params} {e : core.SkSeed ≃ core.Y}
  {pkSeed : core.PkSeed} {s : core.SkSeed × core.SkPrf} {st₀ st : LabState core}

/-! ## Encoded points of the split state -/

/-- **The seed hazard of the split state is the seed hazard of the public cache.** Under key
separation, the public part of the split state of a relabelled state holds a point encoding a
derivation under `s` exactly when the public cache does: no encoded derivation is a node point. -/
theorem exists_isSome_toSplitCache_fst_secretEncoding_enc_iff (hsep : core.KeySeparated) :
    (∃ x, (((slhGraph core pkSeed).toSplitCache st).1
      ((secretEncoding core e pkSeed).enc s x)).isSome) ↔
      ∃ x, (st.1 ((secretEncoding core e pkSeed).enc s x)).isSome :=
  exists_congr fun x ↦ by
    rw [show ((slhGraph core pkSeed).toSplitCache st).1 _ = _ from
      (slhGraph core pkSeed).merge_apply_of_not_exists fun ⟨κ, vs, _, h⟩ ↦
        secretEncoding_enc_ne_slhGraph_pt core hsep e pkSeed pkSeed s x κ vs h.symm]

/-- Under key separation, when the public cache holds no point encoding a derivation under `s`,
the merged cache of a relabelled state is below the real cache rebuilt from its split state. -/
theorem merge_le_merge_toSplitCache (hsep : core.KeySeparated)
    (h : ¬∃ x, (st.1 ((secretEncoding core e pkSeed).enc s x)).isSome) :
    (slhGraph core pkSeed).merge st ≤
      (secretEncoding core e pkSeed).merge s ((slhGraph core pkSeed).toSplitCache st) :=
  (secretEncoding core e pkSeed).le_merge_of_not_exists_isSome _
    ((exists_isSome_toSplitCache_fst_secretEncoding_enc_iff hsep).not.2 h)

/-! ## Target collisions -/

/-- **Target collisions of a rebuilt transcript are target collisions at node keys.** A target
collision of the transcript rebuilt with the secret seeds `s`, read on the cache that a relabelled
state `st` stands for at `s`, is a public entry of `st` at a node's key equal to the node's drawn
label, when the transcript's public seed is the graph's. -/
theorem tcHazard_of_runTargetCollision_fill (hd : core.KeyDiscipline vp) {z : DeriveOutcome core}
    (hpk : z.pk.pkSeed = pkSeed)
    (h : RunTargetCollision core e (DeriveOutcome.fill core s z,
      (secretEncoding core e pkSeed).merge s ((slhGraph core pkSeed).toSplitCache st))) :
    (slhNodeKeys core pkSeed).TCHazard st := by
  have h := h.1
  simp only [DeriveOutcome.fill, UnforgeableTranscript.mapSk_pk, UnforgeableTranscript.mapSk_sk,
    fillSecretKey, hpk] at h
  exact tcHazard_of_targetCollision hd h

/-! ## Completed public misses -/

/-- **A completed public miss is a conflict.** Under key separation, let a child `c` of the node
`κ` be undrawn in `st₀`, so that the cache `st₀` stands for reads the public cache at every point
of `κ`. If it holds the point of `κ` at `vs`, then every state `st` whose public cache extends that
of `st₀` and which draws the children of `κ` at `vs` is a conflict. -/
theorem conflict_of_isSome_merge_fst_thash (hsep : core.KeySeparated) (hfst : st₀.1 ≤ st.1)
    {κ : NodeKey core} {c : DeriveQuery core ⊕ NodeKey core}
    (hc : c ∈ (slhGraph core pkSeed).ch κ) (h₀ : st₀.2 c = none) {vs : List core.Y}
    (h : (slhGraph core pkSeed).childVals st κ = some vs)
    (hq : (𝒞[e, pkSeed, s, st₀] (.thash pkSeed κ.1 vs)).isSome) :
    (slhGraph core pkSeed).Conflict st := by
  refine ⟨κ, vs, h, QueryCache.isSome_mono hfst ?_⟩
  rwa [merge_fst_thash_of_childVals_ne hsep fun h' ↦ by
    simpa [h₀] using (slhGraph core pkSeed).isSome_childVals_iff.1 (Option.isSome_of_eq_some h')
      c hc] at hq

/-- **A hidden WOTS+ chain value met by the verifier is a conflict.** Let the cell of step `t` of
WOTS+ chain `i` be undrawn in `st₀`, and let the cache that `st₀` stands for hold the `F` point of
hash step `t` at the input `[g]`. If, in a state `st` with a larger public cache, the honest chain
from the settled secret reaches `g` at step `t`, then `st` is a conflict: the step's cell is drawn
at `g` in `st`, so its node's point at `[g]` is the point of a node with drawn children, which the
public cache holds. -/
theorem conflict_of_chain?_of_cell_eq_none (hd : core.KeyDiscipline vp) (hfst : st₀.1 ≤ st.1)
    {adrs : Adrs} {i t : ℕ} {x g : core.Y}
    (hmem : (wotsChainAdrs adrs i).setHashAddress t ∈ constructionAddresses vp)
    {c : DeriveQuery core ⊕ NodeKey core}
    (hcell : pathCell core (wotsSkAdrs adrs i) ((wotsChainAdrs adrs i).setHashAddress ·) t =
      some c)
    (h₀ : st₀.2 c = none)
    (hq : (𝒞[e, pkSeed, s, st₀]
      (.thash pkSeed (core.adrsToKey ((wotsChainAdrs adrs i).setHashAddress t)) [g])).isSome)
    (hx : simulateQ 𝒞[e, pkSeed, s, st].toPartialImpl
      (𝒮[e, pkSeed, s] (wotsSkAdrs adrs i)) = some x)
    (hg : chain? core 𝒞[e, pkSeed, s, st] pkSeed (wotsChainAdrs adrs i) x 0 t = some g) :
    (slhGraph core pkSeed).Conflict st :=
  conflict_of_isSome_merge_fst_thash hd.keySeparated hfst (by
      rw [slhGraph_ch_wotsChainAdrs_setHashAddress core hd pkSeed hmem, hcell]
      exact List.mem_singleton_self c) h₀ (childVals_eq_some_of_chain? hd hmem hx hg) hq

/-- **An unopened FORS secret met by the verifier is a conflict.** Let the cell of the secret of
the FORS leaf `t` be undrawn in `st₀`, and let the cache that `st₀` stands for hold the `F` point of
the leaf at the input `[x]`. If, in a state `st` with a larger public cache, the settled secret is
`x`, then `st` is a conflict. -/
theorem conflict_of_forsSkAdrs_of_cell_eq_none (hd : core.KeyDiscipline vp)
    (hfst : st₀.1 ≤ st.1) {adrs : Adrs} {t : ℕ} {x : core.Y}
    (hmem : forsNodeAdrs adrs 0 t ∈ constructionAddresses vp)
    {c : DeriveQuery core ⊕ NodeKey core}
    (hcell : childCell core (.inl (forsSkAdrs adrs t)) = some c) (h₀ : st₀.2 c = none)
    (hq : (𝒞[e, pkSeed, s, st₀]
      (.thash pkSeed (core.adrsToKey (forsNodeAdrs adrs 0 t)) [x])).isSome)
    (hx : simulateQ 𝒞[e, pkSeed, s, st].toPartialImpl
      (𝒮[e, pkSeed, s] (forsSkAdrs adrs t)) = some x) :
    (slhGraph core pkSeed).Conflict st :=
  conflict_of_isSome_merge_fst_thash hd.keySeparated hfst (by
      rw [slhGraph_ch_forsNodeAdrs_zero core hd pkSeed hmem]
      change c ∈ (childCell core (.inl (forsSkAdrs adrs t))).toList
      rw [hcell]
      exact List.mem_singleton_self c) h₀ (childVals_eq_some_of_forsSkAdrs hd hmem hx) hq

/-! ## The verifier's queries -/

section Replay

variable [DecidableEq core.Y]

/-- **The verifier queries the forger's chain value.** Let verification of the forgery settle on
a cache `c₀ ≤ c`, and let the replay on `c` enter layer `j` at `pos` with message `m`. Below the top
of chain `i`, `c₀` holds the `F` point of the step that `m` selects at the forgery's WOTS+ value:
verification recovers layer `j`, so it hashes that value once more. -/
theorem isSome_thash_of_forgerLayer {c₀ c : PublicHash.Cache core} (hle : c₀ ≤ c)
    {o : RomOutcome vp core} {b : Bool}
    (hv : simulateQ c₀.toPartialImpl (GeneralScheme.verifyInternalM
      (m := OracleComp (publicHashSpec core)) vp core o.msg o.sig o.pk) = some b)
    {j : Fin vp.params.d} {pos : LayerPosition vp} {m : core.Y} (hFL : ForgerLayer o c j pos m)
    (i : Fin vp.params.len) (ht : chainStepsCore core m i.val < vp.params.w - 1) :
    (c₀ (.thash o.pk.pkSeed (core.adrsToKey ((wotsChainAdrs (wotsLeafAdrs pos.toAdrs
      pos.leaf.val) i.val).setHashAddress (chainStepsCore core m i.val)))
        [(o.sig.hypertree[j]).wots[i]])).isSome := by
  obtain ⟨d₀, f₀, root, hd₀, hf₀, hr⟩ :=
    exists_of_simulateQ_toPartialImpl_verifyInternalM_eq_some hv
  obtain ⟨d, f, hd, hf, rfl, hm⟩ := hFL
  obtain rfl : d₀ = d := Option.some_inj.1 ((hle hd₀).symm.trans hd)
  obtain rfl : f₀ = f :=
    Option.some_inj.1 ((QueryCache.simulateQ_toPartialImpl_mono hle _ hf₀).symm.trans hf)
  rw [simulateQ_toPartialImpl_pkFromSigM_eq] at hr
  obtain ⟨m₀, r, hm₀, hx, -⟩ := forgerLayers_of_recoverFromPositionM c₀ o.pk.pkSeed
    (splitDigest vp.params d₀) o.sig.hypertree f₀ vp.params.d 0 (by simp) vp.valid.d_pos f₀
    o.sig.hypertree rfl (fun k hk => by simp) hr j (Nat.zero_le _)
  obtain rfl : m₀ = m :=
    Option.some_inj.1 ((forgerMessage?_mono hle _ _ _ _ _ _ hm₀).symm.trans hm)
  obtain ⟨-, ⟨tops, htops, -⟩, -⟩ :=
    (simulateQ_toPartialImpl_xmssPkFromSigM_eq_some_iff core c₀ _ _ _ _ _).1 hx
  have hch := (simulateQ_toPartialImpl_wotsPkFromSigTopsM_eq_some_iff core c₀ _ _ _ _).1 htops i
  rw [show vp.params.w - 1 - chainStepsCore core m₀ i.val =
      0 + 1 + (vp.params.w - 1 - chainStepsCore core m₀ i.val - 1) by omega,
    simulateQ_toPartialImpl_chainM_add_eq_some_iff] at hch
  obtain ⟨y, hy, -⟩ := hch
  obtain ⟨x, hx, hq⟩ := (simulateQ_toPartialImpl_chainM_succ_eq_some_iff core c₀ _ _ _ _ _).1 hy
  obtain rfl : o.sig.hypertree[j].wots[i.val] = x := by simpa [chainM, chainWith] using hx
  rw [Nat.add_zero] at hq
  rw [Fin.getElem_fin]
  exact Option.isSome_of_eq_some hq

/-- **The verifier queries the forger's FORS secrets.** Let verification of the forgery settle on
a cache `c₀ ≤ c`, and let `c` hold the forger's digest. For every FORS tree `i`, `c₀` holds the `F`
point of the leaf the digest selects in tree `i` at the forgery's revealed secret. -/
theorem isSome_thash_of_forgerDigest {c₀ c : PublicHash.Cache core} (hle : c₀ ≤ c)
    {o : RomOutcome vp core} {b : Bool}
    (hv : simulateQ c₀.toPartialImpl (GeneralScheme.verifyInternalM
      (m := OracleComp (publicHashSpec core)) vp core o.msg o.sig o.pk) = some b)
    {digest : Bytes vp.params.m} (hD : ForgerDigest o c digest) (i : Fin vp.params.k) :
    (c₀ (.thash o.pk.pkSeed (core.adrsToKey (forsNodeAdrs (splitDigest vp.params digest).forsAdrs 0
      (forsSigLeafIndex vp.params (splitDigest vp.params digest).md.toList i.val)))
        [(o.sig.fors[i]).sk])).isSome := by
  obtain ⟨d₀, f₀, -, hd₀, hf₀, -⟩ := exists_of_simulateQ_toPartialImpl_verifyInternalM_eq_some hv
  obtain rfl : d₀ = digest := Option.some_inj.1 ((hle hd₀).symm.trans hD)
  obtain ⟨roots, hroots, -⟩ :=
    (simulateQ_toPartialImpl_forsPkFromSigM_eq_some_iff core c₀ _ _ _ _).1 hf₀
  obtain ⟨leaf, hleaf, -⟩ := hroots i
  rw [Fin.getElem_fin, forsSigLeafIndex_eq]
  exact Option.isSome_of_eq_some hleaf

end Replay

/-! ## The forgery's hidden values -/

/-- A WOTS+ chain value that the replay of a forgery on the cache of `st` finds hidden has an
undrawn cell in a state `st₀ ≤ st` with the same public cache whose hidden cells, for the
transcript's log, are undrawn. -/
theorem exists_cell_chainChild_eq_none_of_hiddenChainValue (hd : core.KeyDiscipline vp)
    (hle : st₀ ≤ st) (hfst : st.1 = st₀.1)
    {o : RomOutcome vp core} (hpk : o.pk.pkSeed = pkSeed) (hsk : o.sk.skSeed = s.1)
    (h5 : HiddenUndrawn core o.pk o.log st₀)
    {j : Fin vp.params.d} {pos : LayerPosition vp} {m : core.Y} {i : Fin vp.params.len}
    (hFL : ForgerLayer o 𝒞[e, pkSeed, s, st] j pos m)
    (hHCV : HiddenChainValue (oracleSecret core e o.pk.pkSeed o.sk.skSeed) o 𝒞[e, pkSeed, s, st]
      j pos i.val (chainStepsCore core m i.val))
    (ht : chainStepsCore core m i.val < vp.params.w - 1) :
    ∃ c, childCell core (chainChild pos i.val (chainStepsCore core m i.val)) = some c ∧
      st₀.2 c = none := by
  obtain ⟨c, hcell⟩ := Option.isSome_iff_exists.1
    (isSome_childCell_chainChild (core := core) pos i (le_of_lt ht))
  refine ⟨c, hcell, h5 c (mem_hiddenCells_of_hiddenChainStep ?_ hcell)⟩
  refine hiddenChainStep_of_le hle ht fun hpos ↦ ?_
  have hUL := usedLeaf_of_usedPosition
    (merge_fst_hmsg_of_fst_eq (e := e) (pkSeed := pkSeed) (s := s) hfst) hpos
  rw [layer_eq_of_forgerLayer hFL] at hUL
  obtain ⟨m', hm', hlt⟩ := hHCV hUL
  rw [hpk, hsk] at hm'
  exact ⟨m', label_of_honestMessage? hd pos hm', hlt⟩

/-- A FORS secret that the replay of a forgery on the cache of `st` finds unopened has an undrawn
cell in a state `st₀` with the same public cache whose hidden cells, for the transcript's log, are
undrawn. -/
theorem exists_cell_forsSkAdrs_eq_none_of_unopenedCoord (hfst : st.1 = st₀.1)
    {o : RomOutcome vp core} (h5 : HiddenUndrawn core o.pk o.log st₀)
    {digest : Bytes vp.params.m} {i : Fin vp.params.k}
    (hUC : UnopenedCoord o 𝒞[e, pkSeed, s, st] (splitDigest vp.params digest).forsAdrs
      (forsSigLeafIndex vp.params (splitDigest vp.params digest).md.toList i.val)) :
    ∃ c, childCell core (.inl (forsSkAdrs (splitDigest vp.params digest).forsAdrs
        (forsSigLeafIndex vp.params (splitDigest vp.params digest).md.toList i.val))) = some c ∧
      st₀.2 c = none := by
  refine ⟨_, childCell_inl core (Adrs.isSecretKey_forsSkAdrs _ _), h5 _ ?_⟩
  simpa using mem_hiddenCells_forsSkAdrs (core := core) (st := st₀)
    (BottomPosition.ofDigestParts vp (splitDigest vp.params digest))
    (forsSigLeafIndex_lt _ _ i.isLt)
    (not_openedCoord_of_unopenedCoord (o := o)
      (merge_fst_hmsg_of_fst_eq (e := e) (pkSeed := pkSeed) (s := s) hfst) (by simpa using hUC))
    (childCell_inl core (Adrs.isSecretKey_forsSkAdrs _ _))

/-- **A hidden-value hit after the fill is a conflict.** Let `st₀ ≤ st` have the same public
cache, let the hidden cells of `st₀` for a transcript's log be undrawn, and let verification of
its forgery settle on the cache that `st₀` stands for. A hidden-value hit of the transcript, at its
own provider and read on the cache that `st` stands for, makes `st` a conflict: the verifier
hashed the hidden value while its cell was undrawn, so the public cache holds that point, and in
`st` the cell is drawn at that value. -/
theorem conflict_of_hiddenHit [DecidableEq core.Y] (hd : core.KeyDiscipline vp) (hle : st₀ ≤ st)
    (hfst : st.1 = st₀.1) {o : RomOutcome vp core} (hpk : o.pk.pkSeed = pkSeed)
    (hsk : o.sk.skSeed = s.1) (h5 : HiddenUndrawn core o.pk o.log st₀) {b : Bool}
    (hv : simulateQ 𝒞[e, pkSeed, s, st₀].toPartialImpl (GeneralScheme.verifyInternalM
      (m := OracleComp (publicHashSpec core)) vp core o.msg o.sig o.pk) = some b)
    (h : HiddenHit (oracleSecret core e o.pk.pkSeed o.sk.skSeed) o 𝒞[e, pkSeed, s, st]) :
    (slhGraph core pkSeed).Conflict st := by
  subst hpk
  by_contra hc
  have hle' := QueryCache.fst_mono
    ((secretEncoding core e o.pk.pkSeed).merge_toSplitCache_mono (slhGraph core _) s hle hc)
  rcases h with ⟨j, pos, m, i, x, hFL, hHCV, ht, hx, hg⟩ | ⟨digest, i, hD, hUC, hx⟩
  · obtain ⟨c, hcell, h₀⟩ :=
      exists_cell_chainChild_eq_none_of_hiddenChainValue hd hle hfst rfl hsk h5 hFL hHCV ht
    rw [hsk] at hx
    exact hc (conflict_of_chain?_of_cell_eq_none hd hle.1
      (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i ht)
      ((pathCell_wotsInstanceAdrs core pos i.val _).trans hcell) h₀
      (isSome_thash_of_forgerLayer hle' hv hFL i ht) hx hg)
  · obtain ⟨c, hcell, h₀⟩ := exists_cell_forsSkAdrs_eq_none_of_unopenedCoord hfst h5 hUC
    rw [hsk] at hx
    refine hc (conflict_of_forsSkAdrs_of_cell_eq_none hd hle.1 ?_ hcell h₀
      (isSome_thash_of_forgerDigest hle' hv hD i) hx)
    rw [← BottomPosition.forsAdrs_ofDigestParts]
    exact forsLeafAdrs_mem_constructionAddresses _ i (forsSigLeafIndex_div_pow_a _ _ _)

/-! ## The settled verification -/

section Verify

/-- Verification over `labSpec` is verification over the public hash pushed through the query
capability. -/
theorem verifyInternalM_labSpec_eq [DecidableEq core.Y] (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp core) (pk : PublicKeyCore core) :
    (GeneralScheme.verifyInternalM vp core msg sig pk : OracleComp (labSpec core) Bool) =
      simulateQ (HasQuery.toQueryImpl (spec := publicHashSpec core)
        (m := OracleComp (labSpec core)))
        (GeneralScheme.verifyInternalM vp core msg sig pk :
          OracleComp (publicHashSpec core) Bool) :=
  (GeneralScheme.verifyInternalM_natural vp core
    (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec core)
      (m := OracleComp (labSpec core))) msg sig pk).symm

variable [SampleableType core.Y] [DecidableEq core.Y] [SampleableType (Bytes vp.params.m)]
  [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.SkPrf]
  [SampleableType core.SkSeed] [SampleableType core.SkPrf]
  {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}

/-- **The deferred verification is settled on the rebuilt cache.** On a run of the lab
experiment in the deferred game, verification of the forgery in the transcript rebuilt with secret
seeds `s` is replayed to the transcript's verdict by the cache that any conflict-free state `st`
extending the final state stands for at `s`, when the public cache of `st` holds no point
encoding a derivation under `s`. -/
theorem simulateQ_toPartialImpl_verifyInternalM_of_mem_support_deferredImpl_labExperiment
    (hsep : core.KeySeparated) (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist))
    {s₀ : LabState core × List (DeriveQuery core ⊕ NodeKey core)} {z}
    (hz : z ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl
      (labExperiment core adv pkSeed)).run s₀))
    (hle : z.2.1 ≤ st) (hc : ¬(slhGraph core pkSeed).Conflict st) (s : core.SkSeed × core.SkPrf)
    (hseed : ¬∃ x, (st.1 ((secretEncoding core e pkSeed).enc s x)).isSome) :
    simulateQ 𝒞[e, pkSeed, s, st].toPartialImpl
      (GeneralScheme.verifyInternalM vp core (DeriveOutcome.fill core s z.1).msg
        (DeriveOutcome.fill core s z.1).sig (DeriveOutcome.fill core s z.1).pk :
          OracleComp (publicHashSpec core) Bool) =
        some (DeriveOutcome.fill core s z.1).verified := by
  obtain ⟨-, s₂, -, -, hv⟩ :=
    exists_mem_support_run_of_mem_support_run_unforgeableTranscriptExperiment _
      (labAdversary core adv pkSeed) hz
  simp only [DeriveOutcome.fill, UnforgeableTranscript.mapSk_msg, UnforgeableTranscript.mapSk_sig,
    UnforgeableTranscript.mapSk_pk, UnforgeableTranscript.mapSk_verified]
  exact QueryCache.simulateQ_toPartialImpl_mono
    (QueryCache.fst_mono (merge_le_merge_toSplitCache hsep hseed)) _
    ((slhGraph core pkSeed).simulateQ_toPartialImpl_merge_fst_of_mem_support_deferredImpl
      (GeneralScheme.verifyInternalM vp core z.1.msg z.1.sig z.1.pk)
      (by rw [← verifyInternalM_labSpec_eq]; exact hv) hle hc)

/-! ## The events after the end fill -/

/-- **The event transport.** On the deferred run of the lab experiment, its end fill and a draw
of secret seeds, a target collision or a hidden-value hit of the rebuilt transcript read on the
cache that the filled state stands for, a point of its split state encoding a derivation under
the drawn seeds, or a conflict, is a conflict of the filled state, a target collision at one of
its node keys, or a point of its public cache encoding a derivation under the drawn seeds. -/
theorem conflict_or_tcHazard_or_exists_isSome_of_mem_support_deferredFillDraw
    (hd : core.KeyDiscipline vp) {adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)}
    {w : (DeriveOutcome core × LabState core × List (DeriveQuery core ⊕ NodeKey core)) ×
      LabState core × (core.SkSeed × core.SkPrf)}
    (hw : w ∈ support ((slhGraph core pkSeed).deferredFillDraw ($ᵗ (core.SkSeed × core.SkPrf))
      (labExperiment core adv pkSeed)))
    (h : ((RunTargetCollision core e (DeriveOutcome.fill core w.2.2 w.1.1,
          (secretEncoding core e pkSeed).merge w.2.2 ((slhGraph core pkSeed).toSplitCache w.2.1)) ∨
        RunHiddenHit core e (DeriveOutcome.fill core w.2.2 w.1.1,
          (secretEncoding core e pkSeed).merge w.2.2
            ((slhGraph core pkSeed).toSplitCache w.2.1))) ∨
      ∃ x, (((slhGraph core pkSeed).toSplitCache w.2.1).1
        ((secretEncoding core e pkSeed).enc w.2.2 x)).isSome) ∨
      (slhGraph core pkSeed).Conflict w.2.1) :
    (slhGraph core pkSeed).Conflict w.2.1 ∨ (slhNodeKeys core pkSeed).TCHazard w.2.1 ∨
      ∃ x, (w.2.1.1 ((secretEncoding core e pkSeed).enc w.2.2 x)).isSome := by
  obtain ⟨hz, hst, -⟩ := (CanonicalGraph.mem_support_deferredFillDraw_iff _).1 hw
  obtain ⟨hpk, h5⟩ := hiddenUndrawn_of_mem_support_deferredImpl_labExperiment pkSeed hd adv hz
  have hle := RelabelState.le_of_mem_support_endFill hst
  have hfst := RelabelState.fst_eq_of_mem_support_endFill hst
  rcases h with ((htc | hhh) | hseed) | hc
  · exact Or.inr (Or.inl (tcHazard_of_runTargetCollision_fill hd hpk htc))
  · by_cases hc : (slhGraph core pkSeed).Conflict w.2.1
    · exact Or.inl hc
    by_cases hseed : ∃ x, (w.2.1.1 ((secretEncoding core e pkSeed).enc w.2.2 x)).isSome
    · exact Or.inr (Or.inr hseed)
    have hv := simulateQ_toPartialImpl_verifyInternalM_of_mem_support_deferredImpl_labExperiment
      hd.keySeparated adv hz le_rfl (fun h ↦ hc (CanonicalGraph.Conflict.mono _ hle h)) w.2.2
      (by rwa [← hfst])
    exact Or.inl (conflict_of_hiddenHit hd hle hfst (o := DeriveOutcome.fill core w.2.2 w.1.1)
      (by simpa [DeriveOutcome.fill] using hpk) (by simp [DeriveOutcome.fill, fillSecretKey])
      (by simpa [DeriveOutcome.fill] using h5) hv hhh.1)
  · exact Or.inr (Or.inr
      ((exists_isSome_toSplitCache_fst_secretEncoding_enc_iff hd.keySeparated).1 hseed))
  · exact Or.inl hc

end Verify

end SLHDSA.Security
