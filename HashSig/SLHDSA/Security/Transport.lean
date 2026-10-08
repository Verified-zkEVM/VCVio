/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import HashSig.SLHDSA.Security.LabelReaders
public import HashSig.SLHDSA.Security.LabScheme
public import HashSig.SLHDSA.Security.RomSchemeUnion
public import VCVio.OracleComp.QueryTracking.RandomOracle.JointPotential
public import VCVio.OracleComp.QueryTracking.RandomOracle.Settled
import HashSig.SLHDSA.Security.CacheDecomposition
import HashSig.SLHDSA.Security.ComponentTraces
import all VCVio.CryptoFoundations.SignatureAlg.Transcript

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
  node key of the filled state (`tcHazard_of_runTargetCollision_fill`,
  `tcHazard_of_mem_support_deferredFillDraw`), since the transcript's public seed is the graph's.
* **The settled verification.** Verification run in the deferred game is replayed to its verdict
  by the rebuilt cache of every conflict-free state extending its final state, off the seed
  hazard (`simulateQ_toPartialImpl_verifyInternalM_of_mem_support_deferredImpl`); on the lab
  experiment this is the verification of the rebuilt transcript, before the fill and after it
  (`simulateQ_toPartialImpl_verifyInternalM_of_mem_support_deferredImpl_labExperiment`,
  `simulateQ_toPartialImpl_verifyInternalM_of_mem_support_deferredFillDraw`).
* **The verifier's queries.** A settled verification hashes the forgery's WOTS+ value at the step
  its message selects, at every layer the replay enters (`isSome_thash_of_forgerLayer`), and the
  revealed secret of every FORS leaf its digest selects (`isSome_thash_of_forgerDigest`).
* **Hidden values.** A node point held by the cache of a state in which a child of the node is
  undrawn is a public entry; once a larger state draws the children at that point's values, it is
  a conflict (`CanonicalGraph.conflict_of_isSome_merge_pt`). At SLH-DSA: if a forgery's WOTS+
  value is the honest chain value at the step that the replay's message selects, or a revealed
  FORS secret is the honest one, read after the fill, while that cell was undrawn when
  verification ran, the filled state is a conflict (`conflict_of_forgerLayer_of_cell_eq_none`,
  `conflict_of_forgerDigest_of_cell_eq_none`).

## Scope

* That the hidden cells are undrawn before the fill is a hypothesis here.
* Nothing here is probabilistic: the statements hold on every point of the support.
-/

public section

namespace SLHDSA.Security

open OracleComp OracleSpec SignatureAlg

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-- The public-hash cache that the relabelled state `st` stands for at the secret seeds `s`, under
the secret encoding of `e` at the public seed `pkSeed`. -/
local notation "𝒞[" e ", " pkSeed ", " s ", " st "]" =>
  QueryCache.fst (SecretEncoding.merge (secretEncoding _ e pkSeed) s
    (CanonicalGraph.toSplitCache (slhGraph _ pkSeed) st))

/-- The oracle-backed secret provider at the first secret seed of `s`. -/
local notation "𝒮[" e ", " pkSeed ", " s "]" => oracleSecret _ e pkSeed (Prod.fst s)

/-! ## The rebuilt transcript -/

section Fill

variable (s : core.SkSeed × core.SkPrf) (z : DeriveOutcome core)

/-- Rebuilding keeps the public key. -/
private theorem fill_pk : (DeriveOutcome.fill core s z).pk = z.pk := rfl

/-- The rebuilt secret key carries the first secret seed. -/
private theorem fill_sk_skSeed : (DeriveOutcome.fill core s z).sk.skSeed = s.1 := rfl

/-- Rebuilding keeps the forged message. -/
private theorem fill_msg : (DeriveOutcome.fill core s z).msg = z.msg := rfl

/-- Rebuilding keeps the forgery. -/
private theorem fill_sig : (DeriveOutcome.fill core s z).sig = z.sig := rfl

/-- Rebuilding keeps the verdict. -/
private theorem fill_verified : (DeriveOutcome.fill core s z).verified = z.verified := rfl

end Fill

/-! ## Encoded points of the split state -/

section Seed

variable {e : core.SkSeed ≃ core.Y} {pkSeed : core.PkSeed} {s : core.SkSeed × core.SkPrf}
  {st : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y}

/-- Under key separation, the public part of the split state of a relabelled state reads the
public cache at every encoded derivation: no encoded derivation is a node point. -/
theorem toSplitCache_fst_secretEncoding_enc (hsep : core.KeySeparated) (x : DeriveQuery core) :
    ((slhGraph core pkSeed).toSplitCache st).1 ((secretEncoding core e pkSeed).enc s x) =
      st.1 ((secretEncoding core e pkSeed).enc s x) :=
  (slhGraph core pkSeed).merge_apply_of_not_exists fun ⟨κ, vs, _, h⟩ ↦
    secretEncoding_enc_ne_slhGraph_pt core hsep e pkSeed pkSeed s x κ vs h.symm

/-- **The seed hazard of the split state is the seed hazard of the public cache.** Under key
separation, the public part of the split state of a relabelled state holds a point encoding a
derivation under `s` exactly when the public cache does. -/
theorem exists_isSome_toSplitCache_fst_secretEncoding_enc_iff (hsep : core.KeySeparated) :
    (∃ x, (((slhGraph core pkSeed).toSplitCache st).1
      ((secretEncoding core e pkSeed).enc s x)).isSome) ↔
      ∃ x, (st.1 ((secretEncoding core e pkSeed).enc s x)).isSome := by
  simp only [toSplitCache_fst_secretEncoding_enc hsep]

/-- Under key separation, when the public cache holds no point encoding a derivation under `s`,
the merged cache of a relabelled state is below the real cache rebuilt from its split state. -/
theorem merge_le_merge_toSplitCache (hsep : core.KeySeparated)
    (h : ¬∃ x, (st.1 ((secretEncoding core e pkSeed).enc s x)).isSome) :
    (slhGraph core pkSeed).merge st ≤
      (secretEncoding core e pkSeed).merge s ((slhGraph core pkSeed).toSplitCache st) :=
  (secretEncoding core e pkSeed).le_merge_of_not_exists_isSome _
    ((exists_isSome_toSplitCache_fst_secretEncoding_enc_iff hsep).not.2 h)

end Seed

/-! ## Target collisions -/

/-- **Target collisions of a rebuilt transcript are target collisions at node keys.** A target
collision of the transcript rebuilt with the secret seeds `s`, read on the cache that a relabelled
state `st` stands for at `s`, is a public entry of `st` at a node's key equal to the node's drawn
label, when the transcript's public seed is the graph's. -/
theorem tcHazard_of_runTargetCollision_fill (hd : core.KeyDiscipline vp) {e : core.SkSeed ≃ core.Y}
    {pkSeed : core.PkSeed} {s : core.SkSeed × core.SkPrf}
    {st : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y}
    {z : DeriveOutcome core} (hpk : z.pk.pkSeed = pkSeed)
    (h : RunTargetCollision core e (DeriveOutcome.fill core s z,
      (secretEncoding core e pkSeed).merge s ((slhGraph core pkSeed).toSplitCache st))) :
    (slhNodeKeys core pkSeed).TCHazard st := by
  have h := h.1
  dsimp only at h
  rw [fill_pk, fill_sk_skSeed, hpk] at h
  exact tcHazard_of_targetCollision hd h

/-! ## Completed public misses -/

section Miss

variable {e : core.SkSeed ≃ core.Y} {pkSeed : core.PkSeed} {s : core.SkSeed × core.SkPrf}
  {st₀ st : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y}

/-- Under key separation, the cache a relabelled state stands for reads the merged cache of the
state at every node point. -/
theorem merge_fst_thash_eq_merge (hsep : core.KeySeparated) (κ : NodeKey core)
    (vs : List core.Y) :
    𝒞[e, pkSeed, s, st] (.thash pkSeed κ.1 vs) =
      (slhGraph core pkSeed).merge st ((slhGraph core pkSeed).pt κ vs) :=
  (secretEncoding core e pkSeed).merge_apply_of_not_exists s _ fun ⟨x, hx⟩ ↦
    secretEncoding_enc_ne_slhGraph_pt core hsep e pkSeed pkSeed s x κ vs hx

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
    (slhGraph core pkSeed).Conflict st := by
  refine (slhGraph core pkSeed).conflict_of_isSome_merge_pt hfst ?_ h₀
    (childVals_eq_some_of_chain? hd hmem hx hg) ?_
  · rw [slhGraph_ch_wotsChainAdrs_setHashAddress core hd pkSeed hmem, hcell]
    exact List.mem_singleton_self c
  · rw [← merge_fst_thash_eq_merge hd.keySeparated (e := e) (s := s)]
    exact hq

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
    (slhGraph core pkSeed).Conflict st := by
  refine (slhGraph core pkSeed).conflict_of_isSome_merge_pt hfst ?_ h₀
    (childVals_eq_some_of_forsSkAdrs hd hmem hx) ?_
  · rw [slhGraph_ch_forsNodeAdrs_zero core hd pkSeed hmem]
    change c ∈ (childCell core (.inl (forsSkAdrs adrs t))).toList
    rw [hcell]
    exact List.mem_singleton_self c
  · rw [← merge_fst_thash_eq_merge hd.keySeparated (e := e) (s := s)]
    exact hq

end Miss

/-! ## The verifier's queries -/

section Replay

/-- The message the verification replay presents to a layer only grows with the cache. -/
theorem forgerMessage?_mono {c c' : PublicHash.Cache core} (hle : c ≤ c') (pk : core.PkSeed)
    (parts : DigestParts vp.params) (sig : GeneralHypertree.Signature vp core) (forsPk : core.Y) :
    ∀ (j : ℕ) (hj : j < vp.params.d) {m : core.Y},
      forgerMessage? c pk parts sig forsPk j hj = some m →
        forgerMessage? c' pk parts sig forsPk j hj = some m
  | 0, _, _, h => h
  | j + 1, hj, m, h => by
    obtain ⟨m', hm', hx⟩ := Option.bind_eq_some_iff.1 h
    exact Option.bind_eq_some_iff.2 ⟨m', forgerMessage?_mono hle pk parts sig forsPk j _ hm',
      QueryCache.simulateQ_toPartialImpl_mono hle _ hx⟩

variable [DecidableEq core.Y]

/-- Algorithm 20 settled at any verdict has its `H_msg` digest, its FORS public key and its
hypertree recovery settled. -/
theorem exists_of_simulateQ_toPartialImpl_verifyInternalM_eq_some {c : PublicHash.Cache core}
    {msg : List Byte} {sig : GeneralScheme.SignatureCore vp core} {pk : PublicKeyCore core}
    {b : Bool} (h : simulateQ c.toPartialImpl
      (GeneralScheme.verifyInternalM (m := OracleComp (publicHashSpec core)) vp core msg sig pk) =
        some b) :
    ∃ digest forsPk root, c (.hmsg sig.randomness pk.pkSeed pk.pkRoot msg) = some digest ∧
      forsPkFromSig? core c sig.fors (splitDigest vp.params digest).md.toList pk.pkSeed
        (splitDigest vp.params digest).forsAdrs = some forsPk ∧
      simulateQ c.toPartialImpl (GeneralHypertree.pkFromSigM vp core forsPk sig.hypertree
        pk.pkSeed (splitDigest vp.params digest)) = some root := by
  simp only [GeneralScheme.verifyInternalM, GeneralHypertree.verifyM, simulateQ_bind_eq_some_iff,
    simulateQ_toPartialImpl_hmsg] at h
  obtain ⟨digest, hd, forsPk, hf, root, hr, -⟩ := h
  exact ⟨digest, forsPk, root, hd, hf, hr⟩

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

/-! ## Hidden values met by the verifier -/

section Hidden

variable [DecidableEq core.Y] {e : core.SkSeed ≃ core.Y} {pkSeed : core.PkSeed}
  {s : core.SkSeed × core.SkPrf}
  {st₀ st : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y}

/-- **A hidden WOTS+ chain value of the forgery is a conflict after the fill.** Let `st₀ ≤ st`,
let verification of a forgery at public seed `pkSeed` settle on the cache that `st₀` stands for,
and let the replay on the cache that `st` stands for enter layer `j` at `pos` with message `m`.
If the forgery's value on chain `i` is the honest chain value at the step `t < w - 1` that `m`
selects, read on the cache of `st`, and the cell of step `t` is undrawn in `st₀`, then `st` is a
conflict: verification hashed that value at step `t` while the cell was undrawn, so the public
cache holds the point, and in `st` the step's only child is drawn at that value. -/
theorem conflict_of_forgerLayer_of_cell_eq_none (hd : core.KeyDiscipline vp) (hle : st₀ ≤ st)
    {o : RomOutcome vp core} (hpk : o.pk.pkSeed = pkSeed) {b : Bool}
    (hv : simulateQ 𝒞[e, pkSeed, s, st₀].toPartialImpl (GeneralScheme.verifyInternalM
      (m := OracleComp (publicHashSpec core)) vp core o.msg o.sig o.pk) = some b)
    {j : Fin vp.params.d} {pos : LayerPosition vp} {m : core.Y}
    (hFL : ForgerLayer o 𝒞[e, pkSeed, s, st] j pos m) (i : Fin vp.params.len)
    (ht : chainStepsCore core m i.val < vp.params.w - 1) {x : core.Y}
    (hx : simulateQ 𝒞[e, pkSeed, s, st].toPartialImpl
      (𝒮[e, pkSeed, s] (wotsSkAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) i.val)) = some x)
    (hg : chain? core 𝒞[e, pkSeed, s, st] pkSeed
      (wotsChainAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) i.val) x 0
        (chainStepsCore core m i.val) = some (o.sig.hypertree[j]).wots[i])
    {c : DeriveQuery core ⊕ NodeKey core}
    (hcell : pathCell core (wotsSkAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) i.val)
      ((wotsChainAdrs (wotsLeafAdrs pos.toAdrs pos.leaf.val) i.val).setHashAddress ·)
        (chainStepsCore core m i.val) = some c)
    (h₀ : st₀.2 c = none) :
    (slhGraph core pkSeed).Conflict st := by
  by_contra hc
  subst hpk
  exact hc (conflict_of_chain?_of_cell_eq_none hd hle.1
    (wotsChainAdrs_setHashAddress_mem_constructionAddresses pos i ht) hcell h₀
    (isSome_thash_of_forgerLayer (QueryCache.fst_mono
      ((secretEncoding core e _).merge_toSplitCache_le_merge_toSplitCache (slhGraph core _) s hle
        hc)) hv hFL i ht) hx hg)

/-- **An unopened FORS secret of the forgery is a conflict after the fill.** Let `st₀ ≤ st`, let
verification of a forgery at public seed `pkSeed` settle on the cache that `st₀` stands for, and
let the cache that `st` stands for hold the forger's digest. If the forgery reveals, in tree `i`,
the secret of the leaf the digest selects, read on the cache of `st`, and that secret's cell is
undrawn in `st₀`, then `st` is a conflict. -/
theorem conflict_of_forgerDigest_of_cell_eq_none (hd : core.KeyDiscipline vp) (hle : st₀ ≤ st)
    {o : RomOutcome vp core} (hpk : o.pk.pkSeed = pkSeed) {b : Bool}
    (hv : simulateQ 𝒞[e, pkSeed, s, st₀].toPartialImpl (GeneralScheme.verifyInternalM
      (m := OracleComp (publicHashSpec core)) vp core o.msg o.sig o.pk) = some b)
    {digest : Bytes vp.params.m} (hD : ForgerDigest o 𝒞[e, pkSeed, s, st] digest)
    (i : Fin vp.params.k)
    (hx : simulateQ 𝒞[e, pkSeed, s, st].toPartialImpl (𝒮[e, pkSeed, s]
      (forsSkAdrs (splitDigest vp.params digest).forsAdrs
        (forsSigLeafIndex vp.params (splitDigest vp.params digest).md.toList i.val))) =
          some (o.sig.fors[i]).sk)
    {c : DeriveQuery core ⊕ NodeKey core}
    (hcell : childCell core (.inl (forsSkAdrs (splitDigest vp.params digest).forsAdrs
      (forsSigLeafIndex vp.params (splitDigest vp.params digest).md.toList i.val))) = some c)
    (h₀ : st₀.2 c = none) :
    (slhGraph core pkSeed).Conflict st := by
  by_contra hc
  subst hpk
  have hmem : forsNodeAdrs (splitDigest vp.params digest).forsAdrs 0
      (forsSigLeafIndex vp.params (splitDigest vp.params digest).md.toList i.val) ∈
        constructionAddresses vp := by
    rw [← BottomPosition.forsAdrs_ofDigestParts]
    exact forsLeafAdrs_mem_constructionAddresses _ i (forsSigLeafIndex_div_pow_a _ _ _)
  exact hc (conflict_of_forsSkAdrs_of_cell_eq_none hd hle.1 hmem hcell h₀
    (isSome_thash_of_forgerDigest (QueryCache.fst_mono
      ((secretEncoding core e _).merge_toSplitCache_le_merge_toSplitCache (slhGraph core _) s hle
        hc)) hv hD i) hx)

end Hidden

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

/-- **Verification is settled on the rebuilt cache.** Verification run in the deferred game is
replayed to its output by the cache that any conflict-free state `st` extending its final state
stands for at secret seeds `s`, when the public cache of `st` holds no point encoding a derivation
under `s`. -/
theorem simulateQ_toPartialImpl_verifyInternalM_of_mem_support_deferredImpl
    (hsep : core.KeySeparated) {e : core.SkSeed ≃ core.Y} {pkSeed : core.PkSeed}
    {msg : List Byte} {sig : GeneralScheme.SignatureCore vp core} {pk : PublicKeyCore core}
    {s₀ : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y ×
      List (DeriveQuery core ⊕ NodeKey core)} {z}
    (hz : z ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl
      (GeneralScheme.verifyInternalM vp core msg sig pk : OracleComp (labSpec core) Bool)).run s₀))
    {st : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y}
    (hle : z.2.1 ≤ st) (hc : ¬(slhGraph core pkSeed).Conflict st) (s : core.SkSeed × core.SkPrf)
    (hseed : ¬∃ x, (st.1 ((secretEncoding core e pkSeed).enc s x)).isSome) :
    simulateQ 𝒞[e, pkSeed, s, st].toPartialImpl
      (GeneralScheme.verifyInternalM vp core msg sig pk : OracleComp (publicHashSpec core) Bool) =
        some z.1 := by
  rw [verifyInternalM_labSpec_eq] at hz
  exact QueryCache.simulateQ_toPartialImpl_mono
    (QueryCache.fst_mono (merge_le_merge_toSplitCache hsep hseed)) _
    ((slhGraph core pkSeed).simulateQ_toPartialImpl_merge_fst_of_mem_support_deferredImpl _ hz
      hle hc)

variable [SampleableType core.SkSeed] [SampleableType core.SkPrf]

/-- On a run of the lab experiment in the deferred game, the transcript's public key has the
graph's public seed. -/
private theorem pkSeed_eq_of_mem_support_deferredImpl_labExperiment {pkSeed : core.PkSeed}
    {e : core.SkSeed ≃ core.Y} {optRand : PublicKeyCore core → ProbComp core.Y}
    {pkSeedDist : ProbComp core.PkSeed}
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist))
    {s₀ : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y ×
      List (DeriveQuery core ⊕ NodeKey core)} {z}
    (hz : z ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl
      (labExperiment core adv pkSeed)).run s₀)) :
    z.1.pk.pkSeed = pkSeed := by
  obtain ⟨_, -, hk, -, -⟩ :=
    exists_mem_support_run_of_mem_support_run_unforgeableTranscriptExperiment _
      (labAdversary core adv pkSeed) hz
  simp only [labScheme, simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hk
  obtain ⟨w, -, hw⟩ := hk
  exact congrArg (fun p ↦ p.1.1.pkSeed) hw

/-- **The deferred verification is settled on the rebuilt cache.** On a run of the lab
experiment in the deferred game, verification of the forgery in the transcript rebuilt with secret
seeds `s` is replayed to the transcript's verdict by the cache that any conflict-free state `st`
extending the final state stands for at `s`, when the public cache of `st` holds no point
encoding a derivation under `s`. -/
theorem simulateQ_toPartialImpl_verifyInternalM_of_mem_support_deferredImpl_labExperiment
    (hsep : core.KeySeparated) {pkSeed : core.PkSeed} {e : core.SkSeed ≃ core.Y}
    {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
    (adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist))
    {s₀ : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y ×
      List (DeriveQuery core ⊕ NodeKey core)} {z}
    (hz : z ∈ support ((simulateQ (slhGraph core pkSeed).deferredImpl
      (labExperiment core adv pkSeed)).run s₀))
    {st : RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y}
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
  rw [fill_msg, fill_sig, fill_pk, fill_verified]
  exact simulateQ_toPartialImpl_verifyInternalM_of_mem_support_deferredImpl hsep hv hle hc s hseed

/-! ## The events after the end fill -/

section Run

variable {pkSeed : core.PkSeed} {e : core.SkSeed ≃ core.Y}
  {optRand : PublicKeyCore core → ProbComp core.Y} {pkSeedDist : ProbComp core.PkSeed}
  {adv : UnforgeableAdversary (romScheme core e optRand pkSeedDist)}
  {w : (DeriveOutcome core × RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y ×
      List (DeriveQuery core ⊕ NodeKey core)) ×
    RelabelState (hashSpec core) (DeriveQuery core) (NodeKey core) core.Y ×
      (core.SkSeed × core.SkPrf)}

/-- **Target collisions after the end fill.** On the deferred run of the lab experiment, its end
fill and a draw of secret seeds, a target collision of the rebuilt transcript on the cache that the
filled state stands for is a target collision at a node key of the filled state. -/
theorem tcHazard_of_mem_support_deferredFillDraw (hd : core.KeyDiscipline vp)
    (hw : w ∈ support ((slhGraph core pkSeed).deferredFillDraw ($ᵗ (core.SkSeed × core.SkPrf))
      (labExperiment core adv pkSeed)))
    (h : RunTargetCollision core e (DeriveOutcome.fill core w.2.2 w.1.1,
      (secretEncoding core e pkSeed).merge w.2.2 ((slhGraph core pkSeed).toSplitCache w.2.1))) :
    (slhNodeKeys core pkSeed).TCHazard w.2.1 :=
  tcHazard_of_runTargetCollision_fill hd (pkSeed_eq_of_mem_support_deferredImpl_labExperiment adv
    ((CanonicalGraph.mem_support_deferredFillDraw_iff _).1 hw).1) h

/-- **The verification after the end fill.** On the deferred run of the lab experiment, its end
fill and a draw of secret seeds `s`, off a conflict of the filled state and off a point of its
public cache encoding a derivation under `s`, verification of the forgery in the rebuilt transcript
is replayed to the transcript's verdict by the cache that the filled state stands for. -/
theorem simulateQ_toPartialImpl_verifyInternalM_of_mem_support_deferredFillDraw
    (hsep : core.KeySeparated)
    (hw : w ∈ support ((slhGraph core pkSeed).deferredFillDraw ($ᵗ (core.SkSeed × core.SkPrf))
      (labExperiment core adv pkSeed)))
    (hc : ¬(slhGraph core pkSeed).Conflict w.2.1)
    (hseed : ¬∃ x, (w.2.1.1 ((secretEncoding core e pkSeed).enc w.2.2 x)).isSome) :
    simulateQ 𝒞[e, pkSeed, w.2.2, w.2.1].toPartialImpl
      (GeneralScheme.verifyInternalM vp core (DeriveOutcome.fill core w.2.2 w.1.1).msg
        (DeriveOutcome.fill core w.2.2 w.1.1).sig (DeriveOutcome.fill core w.2.2 w.1.1).pk :
          OracleComp (publicHashSpec core) Bool) =
        some (DeriveOutcome.fill core w.2.2 w.1.1).verified := by
  obtain ⟨hz, hst, -⟩ := (CanonicalGraph.mem_support_deferredFillDraw_iff _).1 hw
  exact simulateQ_toPartialImpl_verifyInternalM_of_mem_support_deferredImpl_labExperiment hsep adv
    hz (RelabelState.le_of_mem_support_endFill hst) hc _ hseed

end Run

end Verify

end SLHDSA.Security
