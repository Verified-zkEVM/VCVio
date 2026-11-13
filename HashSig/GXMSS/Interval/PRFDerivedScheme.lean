/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Interval.Scheme
public import HashSig.GXMSS.PRFDerivedScheme

/-!
# Shared-response PRF-derived interval GXMSS

Active chain starts and maximal inactive frontier digests use disjoint query coordinates.
The interval is captured before key generation, and verification remains defined at every epoch.
-/

public section

namespace GXMSS.Interval.PRFDerived

open IncomparableEncoding GXMSS GXMSS.IntervalMerkle VCVio.Algorithms

variable {Key PP T X H M R Response : Type} {h w v : ℕ}

/-- Complete-tree inputs together with the disjoint inactive-frontier family. -/
inductive Query (PP M : Type) (h v : ℕ) where
  /-- One of the three complete-tree query families. -/
  | complete (query : GXMSS.PRFDerived.Query PP M h v)
  /-- A maximal inactive subtree root at its raw tree coordinates. -/
  | filler (pp : PP) (level : Fin (h + 1)) (index : Fin (2 ^ h))

/-- The distinguished complete-tree public-parameter coordinate. -/
@[match_pattern] abbrev Query.publicSeed : Query PP M h v := .complete .publicSeed

/-- A complete-tree chain-start coordinate in the extended domain. -/
@[match_pattern] abbrev Query.start (pp : PP) (epoch : Fin (2 ^ h)) (chain : Fin v) :
    Query PP M h v := .complete (.start pp epoch chain)

/-- A complete-tree retry coordinate in the extended domain. -/
@[match_pattern] abbrev Query.retry (pp : PP) (epoch : Fin (2 ^ h)) (message : M)
    (attempt : ℕ) : Query PP M h v := .complete (.retry pp epoch message attempt)

/-- A shared keyed evaluator on all four query families. -/
abbrev Evaluator (Key PP M Response : Type) (h v : ℕ) :=
  Key → Query PP M h v → Response

/-- Complete-tree response projections with an additional inactive-frontier digest. -/
structure Interpretation (PP H R Response : Type) extends
    toComplete : GXMSS.PRFDerived.Interpretation PP H R Response where
  /-- Interpret an inactive-frontier response as its committed digest. -/
  fillerDigest : Response → H

/-- Embed the complete three-family query domain without changing any coordinates. -/
@[expose] def Query.ofComplete : GXMSS.PRFDerived.Query PP M h v → Query PP M h v :=
  Query.complete

/-- The complete-query embedding is injective. -/
theorem Query.ofComplete_injective : Function.Injective
    (Query.ofComplete : GXMSS.PRFDerived.Query PP M h v → Query PP M h v) := by
  intro a b hab
  exact Query.complete.inj hab

/-- Position in the finite active interval selects its ordinary full-tree epoch. -/
@[expose] def activeEpoch (I : Interval h)
    (i : Fin (I.last.val - I.first.val + 1)) : Fin (2 ^ h) :=
  ⟨I.first.val + i.val, by have := I.last.isLt; have := I.ordered; omega⟩

/-- Every enumerated setup epoch belongs to the captured interval. -/
theorem activeEpoch_isActive (I : Interval h)
    (i : Fin (I.last.val - I.first.val + 1)) : Epoch.IsActive I (activeEpoch I i) := by
  have := I.ordered
  simp only [Epoch.IsActive, activeEpoch, Fin.le_def]
  omega

/-- Active enumeration does not duplicate an epoch. -/
theorem activeEpoch_injective (I : Interval h) : Function.Injective (activeEpoch I) := by
  intro i j hij
  have := congrArg Fin.val hij
  apply Fin.ext
  dsimp [activeEpoch] at this
  omega

/-- Extend active starts deterministically; inactive epochs copy the first active epoch. -/
@[expose] def extendStarts (I : Interval h)
    (active : Fin (I.last.val - I.first.val + 1) → Fin v → H) :
    Fin (2 ^ h) → Fin v → H := fun ep chain =>
  if he : Epoch.IsActive I ep then
    active ⟨ep.val - I.first.val, by
      have := I.ordered
      rcases he with ⟨ha, hb⟩
      simp only [Fin.le_def] at ha hb
      omega⟩ chain
  else active ⟨0, by omega⟩ chain

/-- Active setup data are recovered exactly from the deterministic extension. -/
theorem extendStarts_activeEpoch (I : Interval h)
    (active : Fin (I.last.val - I.first.val + 1) → Fin v → H)
    (i : Fin (I.last.val - I.first.val + 1)) (chain : Fin v) :
    extendStarts I active (activeEpoch I i) chain = active i chain := by
  rw [extendStarts, dite_eq_left (activeEpoch_isActive I i)]
  simp [activeEpoch]

/-- Restrict any complete array to its active rows. -/
@[expose] def restrictStarts (I : Interval h) (full : Fin (2 ^ h) → Fin v → H) :
    Fin (I.last.val - I.first.val + 1) → Fin v → H := fun i => full (activeEpoch I i)

/-- Replacing inactive entries leaves every active start unchanged. -/
theorem extendStarts_restrictStarts_active (I : Interval h)
    (full : Fin (2 ^ h) → Fin v → H) (ep : Fin (2 ^ h)) (he : Epoch.IsActive I ep) :
    extendStarts I (restrictStarts I full) ep = full ep := by
  funext chain
  unfold extendStarts
  rw [dite_eq_left he]
  unfold restrictStarts
  congr 2
  apply Fin.ext
  rcases he with ⟨ha, hb⟩
  simp only [activeEpoch] at *
  omega

/-- Equal active starts yield equal active endpoint vectors under the same public seed. -/
theorem endpoints_eq_of_active_starts_eq (hash : HashInstance PP T X H h w v)
    (I : Interval h) (pp : PP) (xs ys : Fin (2 ^ h) → Fin v → H)
    (hactive : ∀ ep, Epoch.IsActive I ep → xs ep = ys ep) :
    ∀ ep, Epoch.IsActive I ep → GXMSS.endpoints hash pp xs ep = GXMSS.endpoints hash pp ys ep := by
  intro ep he
  funext chain
  simp only [GXMSS.endpoints]
  rw [hactive ep he]

/-- The mixed public key cannot observe inactive starts. -/
theorem publicKey_eq_of_active_starts_eq (hash : HashInstance PP T X H h w v)
    (I : Interval h) (pp : PP) (xs ys : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (hactive : ∀ ep, Epoch.IsActive I ep → xs ep = ys ep) :
    (GXMSS.Interval.keys hash I pp xs fillers).1 =
      (GXMSS.Interval.keys hash I pp ys fillers).1 := by
  have hroot := GXMSS.IntervalMerkle.root_eq_of_active_endpoints_eq hash I pp _ _ fillers
    (endpoints_eq_of_active_starts_eq hash I pp xs ys hactive)
  exact congrArg (fun root => GXMSS.PublicKey.mk root pp) hroot

/-- Honest active signatures cannot observe inactive starts, including through their paths. -/
theorem signatureOfWord_eq_of_active_starts_eq (hash : HashInstance PP T X H h w v)
    (I : Interval h) (pp : PP) (xs ys : Fin (2 ^ h) → Fin v → H) (fillers : Fillers I H)
    (hactive : ∀ ep, Epoch.IsActive I ep → xs ep = ys ep)
    (ep : Fin (2 ^ h)) (he : Epoch.IsActive I ep) (wr : Codeword v (2 ^ w) × R) :
    GXMSS.Interval.signatureOfWord hash I (GXMSS.Interval.keys hash I pp xs fillers).2 ep wr =
      GXMSS.Interval.signatureOfWord hash I (GXMSS.Interval.keys hash I pp ys fillers).2 ep wr := by
  have hpath := GXMSS.IntervalMerkle.authPath_eq_of_active_endpoints_eq hash I pp _ _ fillers
    (endpoints_eq_of_active_starts_eq hash I pp xs ys hactive) ep he
  simp only [GXMSS.Interval.signatureOfWord, GXMSS.Interval.keys, GXMSS.keys,
    GXMSS.signatureOfWord]
  rw [hactive ep he, hpath]

/-- The public seed uses the distinguished query. -/
@[expose] def publicSeed (evaluate : Evaluator Key PP M Response h v)
    (p : Interpretation PP H R Response) (key : Key) : PP :=
  p.publicParameter (evaluate key .publicSeed)

/-- Evaluate exactly the active start coordinates and copy their deterministic extension. -/
@[expose] def starts (I : Interval h) (evaluate : Evaluator Key PP M Response h v)
    (p : Interpretation PP H R Response) (key : Key) (pp : PP) :
    Fin (2 ^ h) → Fin v → H :=
  extendStarts I fun i chain => p.chainStart (evaluate key (.start pp (activeEpoch I i) chain))

/-- Each maximal inactive root uses its raw level/index query under the derived parameter. -/
@[expose] def fillers (I : Interval h) (evaluate : Evaluator Key PP M Response h v)
    (p : Interpretation PP H R Response) (key : Key) (pp : PP) : Fillers I H :=
  fun node =>
    let (level, index) := node.val
    p.fillerDigest (evaluate key (.filler pp level index))

/-- Transient material is recomputed from the one retained evaluator key. -/
@[expose] def transientCore (hash : HashInstance PP T X H h w v) (I : Interval h)
    (evaluate : Evaluator Key PP M Response h v) (p : Interpretation PP H R Response)
    (key : Key) : GXMSS.Interval.SecretKey PP H h v I :=
  let pp := publicSeed evaluate p key
  (GXMSS.Interval.keys hash I pp (starts I evaluate p key pp) (fillers I evaluate p key pp)).2

/-- Assemble the mixed root and retain only the evaluator key. -/
@[expose] def keys (hash : HashInstance PP T X H h w v) (I : Interval h)
    (evaluate : Evaluator Key PP M Response h v) (p : Interpretation PP H R Response)
    (key : Key) : PublicKey PP H × Key :=
  let pp := publicSeed evaluate p key
  ((GXMSS.Interval.keys hash I pp (starts I evaluate p key pp)
    (fillers I evaluate p key pp)).1, key)

/-- Parameterless key generation uses the captured evaluator-key sampler. -/
@[expose] def keygen (sampleKey : ProbComp Key) (hash : HashInstance PP T X H h w v)
    (I : Interval h) (evaluate : Evaluator Key PP M Response h v)
    (p : Interpretation PP H R Response) : ProbComp (PublicKey PP H × Key) := do
  let key ← sampleKey
  pure (keys hash I evaluate p key)

/-- The whole bounded list is queried eagerly; consumed prefixes remain a separate observation. -/
@[expose] def retryRandomizers (K : ℕ) (evaluate : Evaluator Key PP M Response h v)
    (p : Interpretation PP H R Response) (key : Key) (pp : PP)
    (ep : Fin (2 ^ h)) (msg : M) : List R :=
  GXMSS.PRFDerived.retryRandomizers K (fun k q => evaluate k (Query.ofComplete q))
    p.toComplete key pp ep msg

/-- The interval construction evaluates the same ordered retry coordinates through its embedding. -/
theorem retryRandomizers_eq_map (K : ℕ) (evaluate : Evaluator Key PP M Response h v)
    (p : Interpretation PP H R Response) (key : Key) (pp : PP)
    (ep : Fin (2 ^ h)) (msg : M) :
    retryRandomizers K evaluate p key pp ep msg =
      (GXMSS.PRFDerived.retryCoordinates K pp ep msg).map
        (fun q => p.retryRandomizer (evaluate key (Query.ofComplete q))) :=
  GXMSS.PRFDerived.retryRandomizers_eq_map K _ p.toComplete key pp ep msg

/-- Replace the complete-tree path in a first-success result, retaining its consumption evidence. -/
@[expose] def replacePath (path : Fin h → H) :
    GXMSS.PRFDerived.SignResult R H h v → GXMSS.PRFDerived.SignResult R H h v :=
  FirstSuccess.Result.map (fun sig => {sig with path := path})

/-- First-success signing retains the original attempt and exact consumed prefix. -/
@[expose] def signResult (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (I : Interval h) (sk : GXMSS.Interval.SecretKey PP H h v I)
    (ep : Fin (2 ^ h)) (msg : M) (randomizers : List R) :
    GXMSS.PRFDerived.SignResult R H h v :=
  let complete := sk.complete
  replacePath (GXMSS.IntervalMerkle.authPath hash I complete.seed complete.endpoints sk.fillers ep)
    (GXMSS.PRFDerived.signResult hash enc complete ep msg randomizers)

/-- Inactive signing fails before deriving any randomizer. -/
@[expose] def run (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (evaluate : Evaluator Key PP M Response h v) (p : Interpretation PP H R Response)
    (K : ℕ) (I : Interval h) (key : Key) (ep : Fin (2 ^ h)) (msg : M) :
    GXMSS.PRFDerived.SigningTransition M R H h v :=
  ⟨ep, msg, if Epoch.IsActive I ep then
    let pp := publicSeed evaluate p key
    signResult hash enc I (transientCore hash I evaluate p key) ep msg
      (retryRandomizers K evaluate p key pp ep msg)
  else .exhausted []⟩

/-- Observe optional signatures while retaining exhaustion as returned failure. -/
@[expose] def sign (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (evaluate : Evaluator Key PP M Response h v) (p : Interpretation PP H R Response)
    (K : ℕ) (I : Interval h) (key : Key) (ep : Fin (2 ^ h)) (msg : M) :
    ProbComp (Option (Signature R H h v)) :=
  pure (run hash enc evaluate p K I key ep msg).output

/-- An inactive request returns failure and consumes no retry prefix. -/
theorem run_inactive (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (evaluate : Evaluator Key PP M Response h v) (p : Interpretation PP H R Response)
    (K : ℕ) (I : Interval h) (key : Key) (ep : Fin (2 ^ h)) (msg : M)
    (he : ¬ Epoch.IsActive I ep) :
    run hash enc evaluate p K I key ep msg = ⟨ep, msg, .exhausted []⟩ := by
  simp [run, he]

/-- A zero budget exhausts without consumption at every epoch. -/
theorem run_zero (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (evaluate : Evaluator Key PP M Response h v) (p : Interpretation PP H R Response)
    (I : Interval h) (key : Key) (ep : Fin (2 ^ h)) (msg : M) :
    run hash enc evaluate p 0 I key ep msg = ⟨ep, msg, .exhausted []⟩ := by
  simp [run, retryRandomizers, GXMSS.PRFDerived.retryRandomizers, signResult,
    GXMSS.PRFDerived.signResult_nil, replacePath, FirstSuccess.Result.map]

/-- Captured configuration defines the one-key scheme; verification covers all epochs. -/
@[expose] def scheme [DecidableEq H]
    (sampleKey : ProbComp Key)
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (evaluate : Evaluator Key PP M Response h v) (p : Interpretation PP H R Response)
    (K : ℕ) (I : Interval h) :
    SyncSignatureAlg ProbComp M (PublicKey PP H) Key (Signature R H h v) (Fin (2 ^ h)) where
  keygen := keygen sampleKey hash I evaluate p
  sign := sign hash enc evaluate p K I
  verify := GXMSS.verify hash enc

/-- The full interval evaluates every start at its original three-family coordinate. -/
theorem starts_full (evaluate : Evaluator Key PP M Response h v)
    (p : Interpretation PP H R Response) (key : Key) (pp : PP) :
    starts (Interval.full h) evaluate p key pp = GXMSS.PRFDerived.starts
      (fun k q => evaluate k (Query.ofComplete q)) p.toComplete key pp := by
  funext ep chain
  unfold starts extendStarts
  rw [dite_eq_left (Epoch.isActive_full ep)]
  simp [activeEpoch, Interval.full, GXMSS.PRFDerived.starts,
    Query.ofComplete]

/-- At full range, the public root and the retained evaluator key are the complete scheme's. -/
theorem keys_full (hash : HashInstance PP T X H h w v)
    (evaluate : Evaluator Key PP M Response h v) (p : Interpretation PP H R Response)
    (key : Key) : keys hash (Interval.full h) evaluate p key =
      GXMSS.PRFDerived.keys hash (fun k q => evaluate k (Query.ofComplete q)) p.toComplete key := by
  simp [keys, GXMSS.PRFDerived.keys, GXMSS.Interval.keys, GXMSS.keys,
    GXMSS.IntervalMerkle.root_full, starts_full, publicSeed, GXMSS.PRFDerived.publicSeed,
    Query.ofComplete]

/-- The full-range path replacement retains the original first-success result and prefix. -/
theorem signResult_full (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (sk : GXMSS.Interval.SecretKey PP H h v (Interval.full h))
    (ep : Fin (2 ^ h)) (msg : M) (randomizers : List R) :
    signResult hash enc (Interval.full h) sk ep msg randomizers =
      GXMSS.PRFDerived.signResult hash enc sk.complete ep msg randomizers := by
  let complete := sk.complete
  unfold signResult GXMSS.PRFDerived.signResult
  dsimp only
  simp only [List.get_eq_getElem]
  cases hretry : enc.retryIndexed (m := Id) complete.seed msg ep randomizers.length
      (fun i => (randomizers[i.val] : Id R)) <;>
    simp [replacePath, FirstSuccess.Result.map,
      GXMSS.IntervalMerkle.authPath_full, GXMSS.signatureOfWord]

/-- Full-range signing retains the exact first-success attempt and consumed prefix. -/
theorem run_full (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (evaluate : Evaluator Key PP M Response h v) (p : Interpretation PP H R Response)
    (K : ℕ) (key : Key) (ep : Fin (2 ^ h)) (msg : M) :
    run hash enc evaluate p K (Interval.full h) key ep msg =
      GXMSS.PRFDerived.run K (fun k q => evaluate k (Query.ofComplete q)) p.toComplete
        hash enc key ep msg := by
  unfold run
  rw [ite_eq_left (Epoch.isActive_full ep), signResult_full]
  simp [GXMSS.PRFDerived.run, transientCore, GXMSS.Interval.keys, GXMSS.keys,
    GXMSS.PRFDerived.transientCore, starts_full, publicSeed, GXMSS.PRFDerived.publicSeed,
    retryRandomizers, GXMSS.PRFDerived.retryRandomizers,
    Query.ofComplete]

/-- Full-range schemes agree exactly, independently of any filler response sampling law. -/
theorem scheme_full [DecidableEq H]
    (sampleKey : ProbComp Key)
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Fin (2 ^ h)) v (2 ^ w))
    (evaluate : Evaluator Key PP M Response h v) (p : Interpretation PP H R Response) (K : ℕ) :
    scheme sampleKey hash enc evaluate p K (Interval.full h) =
      GXMSS.PRFDerived.scheme sampleKey hash enc (fun k q => evaluate k (Query.ofComplete q))
        p.toComplete K := by
  unfold scheme GXMSS.PRFDerived.scheme
  congr 1
  · unfold keygen GXMSS.PRFDerived.keygen
    apply bind_congr
    intro key
    exact congrArg pure (keys_full hash evaluate p key)
  · funext key ep msg
    unfold sign GXMSS.PRFDerived.sign
    rw [run_full]

end GXMSS.Interval.PRFDerived
