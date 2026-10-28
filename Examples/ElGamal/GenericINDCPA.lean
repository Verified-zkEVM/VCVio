/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Examples.ElGamal.Generic
public import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA.GenericLift

/-! # Generic adversaries in the multi-query ElGamal game

Group elements are represented by handles. The left/right interface reads message handles
with a zero default and appends both ciphertext components to the adversary's table.
-/

public section

open OracleComp OracleSpec GroupModel
open scoped ENNReal

namespace elGamalAsymmEnc

variable {F G : Type}

/-- A generic group computation with private coins and a left/right oracle on message handles. -/
abbrev GenericAdversary (F : Type) :=
  OracleComp (spec F groupSig + (unifSpec + (Handle × Handle →ₒ Handle × Handle))) Bool

namespace GenericAdversary

/-- Forward private coins and left/right queries, appending the returned ciphertext components
in order. Each response receives fresh handles, including responses served by the game's cache. -/
@[expose] def queryImpl [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G] [Module F G] [SampleableType G] (gen : G) :
    QueryImpl (unifSpec + (Handle × Handle →ₒ Handle × Handle))
      (StateT (Tbl (fun _ : Unit => G))
        (OracleComp (elGamalAsymmEnc F G gen).IND_CPA_oracleSpec))
  | .inl n => fun tbl => do
      let u ← (elGamalAsymmEnc F G gen).IND_CPA_oracleSpec.query (.inl n)
      pure (u, tbl)
  | .inr mm => fun tbl => do
      let c ← (elGamalAsymmEnc F G gen).IND_CPA_oracleSpec.query
        (.inr (lookup tbl () mm.1, lookup tbl () mm.2))
      pure (((tbl ()).length, (tbl ()).length + 1), append (append tbl () c.1) () c.2)

/-- Interpret a generic computation on `[gen, pk]` as the IND-CPA adversary of `elGamalAsymmEnc`. -/
@[expose] def toAdversary [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
    (gen : G) (A : GenericAdversary F) : (elGamalAsymmEnc F G gen).IND_CPA_Adversary :=
  fun pk => Prod.fst <$> run (Model.group G) (fun _ => id) (queryImpl gen) A
    (fun _ => [gen, pk])

/-- Interpreting handles preserves the number of left/right calls, even for repeated or
out-of-range message handles. -/
theorem makesAtMostQueries_toAdversary [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
    (gen : G) (A : GenericAdversary F) (q : ℕ)
    (hq : IsQueryBoundP A (· matches .inr (.inr _)) q) :
    (A.toAdversary gen).MakesAtMostQueries q := by
  intro pk
  rw [toAdversary, isQueryBoundP_map_iff]
  apply hq.simulateQ_run_of_step
  · rintro (t | (n | mm)) ht tbl
    · simp at ht
    · simp at ht
    · simp [QueryImpl.add_apply_inr, queryImpl, StateT.run]
  · rintro (t | (n | mm)) ht tbl
    · cases t <;> exact isQueryBoundP_pure _ _ _
    · simp [QueryImpl.add_apply_inr, queryImpl, StateT.run]
    · simp at ht

/-! ## Pausing at a fresh left/right query -/

private abbrev HandlePair := Handle × Handle

private structure SimState where
  translation : Tbl (fun _ : Unit => Handle)
  cache : List (HandlePair × HandlePair)
  count : ℕ

private def translate (z : Handle) (st : SimState) (mm : HandlePair) : HandlePair :=
  ((st.translation ()).getD mm.1 z, (st.translation ()).getD mm.2 z)

private def record (st : SimState) (c : HandlePair) : HandlePair × SimState :=
  (((st.translation ()).length, (st.translation ()).length + 1),
    { st with translation := append (append st.translation () c.1) () c.2 })

private def cacheFind (F : Type) (mm : HandlePair) :
    List (HandlePair × HandlePair) → OracleComp (genSpec F groupSig) (Option HandlePair)
  | [] => pure none
  | (nn, c) :: cs => do
      let e₁ ← (genSpec F groupSig).query (.inl (.eq () mm.1 nn.1))
      let e₂ ← (genSpec F groupSig).query (.inl (.eq () mm.2 nn.2))
      if e₁ && e₂ then pure (some c) else cacheFind F mm cs

private def encrypt [SampleableType F] (m : Handle) :
    OracleComp (genSpec F groupSig) HandlePair := do
  let r ← simulateQ (fun n => liftM ((genSpec F groupSig).query (.inr n))) ($ᵗ F)
  let c₁ ← (genSpec F groupSig).query (.inl (.smul () r 0))
  let pad ← (genSpec F groupSig).query (.inl (.smul () r 1))
  let c₂ ← (genSpec F groupSig).query (.inl (.add () m pad))
  pure (c₁, c₂)

private def groupStep (z : Handle) (t : Query F groupSig) :
    StateT SimState (OracleComp (genSpec F groupSig)) ((spec F groupSig).Range t) :=
  fun st => do
    let (u, τ) ← (virtualizeImpl (fun _ => z) (.inl t)).run st.translation
    pure (u, { st with translation := τ })

private def suffixImpl [SampleableType F] (z : Handle) :
    QueryImpl (spec F groupSig + (unifSpec + (HandlePair →ₒ HandlePair)))
      (StateT SimState (OracleComp (genSpec F groupSig)))
  | .inl t => groupStep z t
  | .inr (.inl n) => fun st => do
      let u ← (genSpec F groupSig).query (.inr n)
      pure (u, st)
  | .inr (.inr mm) => fun st => do
      let nn := translate z st mm
      match ← cacheFind F nn st.cache with
      | some c => pure (record st c)
      | none =>
          let c ← encrypt (F := F) nn.2
          pure (record { st with cache := (nn, c) :: st.cache, count := st.count + 1 } c)

private inductive PrefixResult (F : Type)
  | done (b : Bool)
  | paused (mm : HandlePair) (cont : HandlePair → GenericAdversary F)

private def runPrefix [SampleableType F] (z : Handle) (k : ℕ) :
    GenericAdversary F → StateT SimState (OracleComp (genSpec F groupSig)) (PrefixResult F) :=
  OracleComp.construct
    (C := fun _ => StateT SimState (OracleComp (genSpec F groupSig)) (PrefixResult F))
    (fun b => pure (.done b))
    (fun t cont rec => match t with
      | .inl t => do rec (← groupStep z t)
      | .inr (.inl n) => do
          let u ← (genSpec F groupSig).query (.inr n)
          rec u
      | .inr (.inr mm) => fun st => do
          let nn := translate z st mm
          match ← cacheFind F nn st.cache with
          | some c =>
              let (cc, st') := record st c
              rec cc st'
          | none =>
              if st.count < k then
                let c ← encrypt (F := F) nn.1
                let (cc, st') := record
                  { st with cache := (nn, c) :: st.cache, count := st.count + 1 } c
                rec cc st'
              else
                pure (.paused nn cont, st))

private inductive StepState (F : Type)
  | done (b : Bool)
  | paused (z : Handle) (mm : HandlePair) (st : SimState)
      (cont : HandlePair → GenericAdversary F)

/-- Extract a generic one-time adversary at the `k`-th fresh message pair. The prefix encrypts
left messages, the suffix encrypts right messages, and equality queries identify cache hits.
A private handle translation hides intermediate encryption values and supplies zero for invalid
handles. The paused continuation receives fresh virtual ciphertext handles. -/
def step [Zero F] [SampleableType F] (A : GenericAdversary F) (k : ℕ) :
    GenericOneTimeAdversary F where
  State := StepState F
  chooseMessages := do
    let z ← (genSpec F groupSig).query (.inl (.smul () 0 0))
    let (res, st) ← (runPrefix z k A).run ⟨fun _ => [0, 1], [], 0⟩
    match res with
    | .done b => pure (0, 0, .done b)
    | .paused mm cont => pure (mm.1, mm.2, .paused z mm st cont)
  distinguish state a b := do
    match state with
    | .done guess => pure guess
    | .paused z mm st cont =>
        let (cc, st') := record
          { st with cache := (mm, (a, b)) :: st.cache, count := st.count + 1 } (a, b)
        (simulateQ (suffixImpl z) (cont cc)).run' st'

private theorem cacheFind_bound (mm : HandlePair) (cs : List (HandlePair × HandlePair)) :
    IsQueryBoundP (cacheFind F mm cs) (fun i => isGroupOp i = true) 0 := by
  induction cs with
  | nil => exact isQueryBoundP_pure _ _ _
  | cons c cs ih =>
    rw [cacheFind]
    erw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp [isGroupOp]), fun a => ?_⟩
    erw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp [isGroupOp]), fun b => ?_⟩
    split
    · exact isQueryBoundP_pure _ _ _
    · exact ih

private theorem encrypt_bound [SampleableType F] (m : Handle) :
    IsQueryBoundP (encrypt (F := F) m) (fun i => isGroupOp i = true) 3 := by
  have hc : IsQueryBoundP
      (simulateQ (fun n => liftM ((genSpec F groupSig).query (.inr n))) ($ᵗ F))
      (fun i => isGroupOp i = true) 0 :=
    isQueryBoundP_simulateQ_zero _ (fun n => by
      erw [isQueryBoundP_query_iff]; simp [isGroupOp])
  unfold encrypt
  apply isQueryBoundP_bind (m := 3) hc
  intro r _
  erw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr (by simp), fun a => ?_⟩
  erw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr (by simp [isGroupOp]), fun b => ?_⟩
  erw [isQueryBoundP_query_bind_iff]
  exact ⟨Or.inr (by simp [isGroupOp]), fun _ => isQueryBoundP_pure _ _ _⟩

private theorem groupStep_bound (z : Handle) (t : Query F groupSig) (st : SimState) :
    IsQueryBoundP ((groupStep z t).run st) (fun i => isGroupOp i = true)
      (if t.isOp then 1 else 0) := by
  cases t <;> simp [groupStep, virtualizeImpl, StateT.run, isGroupOp, Query.isOp]

private theorem suffix_bound [SampleableType F] (z : Handle) (A : GenericAdversary F)
    (qₒ q : ℕ) (hₒ : IsQueryBoundP A (fun i => isGroupOp i = true) qₒ)
    (hq : IsQueryBoundP A (· matches .inr (.inr _)) q) (st : SimState) :
    IsQueryBoundP ((simulateQ (suffixImpl z) A).run st)
      (fun i => isGroupOp i = true) (qₒ + 3 * q) := by
  induction A using OracleComp.inductionOn generalizing qₒ q st with
  | pure b => simp
  | query_bind t cont ih =>
    rw [isQueryBoundP_query_bind_iff] at hₒ hq
    rw [simulateQ_query_bind, StateT.run_bind]
    rcases t with t | (n | mm)
    · change IsQueryBoundP ((groupStep z t).run st >>= fun r =>
        (simulateQ (suffixImpl z) (cont r.1)).run r.2) _ _
      have hb := isQueryBoundP_bind (groupStep_bound z t st)
        (fun r _ => ih r.1 _ _ (hₒ.2 r.1) (hq.2 r.1) r.2)
      exact hb.mono (by simp only [isGroupOp] at *; split <;> grind)
    · change IsQueryBoundP (liftM ((genSpec F groupSig).query (.inr n)) >>= fun u =>
        (simulateQ (suffixImpl z) (cont u)).run st) _ _
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (by simp [isGroupOp]), fun u => ?_⟩
      exact ih u _ _ (hₒ.2 u) (hq.2 u) st
    · change IsQueryBoundP
        ((do
          match ← cacheFind F (translate z st mm) st.cache with
          | some c => pure (record st c)
          | none => do
              let c ← encrypt (F := F) (translate z st mm).2
              pure (record { st with
                cache := (translate z st mm, c) :: st.cache
                count := st.count + 1 } c)) >>= fun r =>
                  (simulateQ (suffixImpl z) (cont r.1)).run r.2) _ _
      rw [bind_assoc]
      refine (isQueryBoundP_bind (m := qₒ + 3 * q)
        (cacheFind_bound (F := F) _ _) ?_).mono (by omega)
      intro cached _
      have hpos : 0 < q := by simpa using hq.1
      cases cached with
      | some c =>
          simp only [pure_bind]
          exact (ih _ _ _ (hₒ.2 _) (hq.2 _) _).mono (by simp [isGroupOp])
      | none =>
          simp only [bind_assoc, pure_bind]
          exact (isQueryBoundP_bind (encrypt_bound _) fun c _ =>
            ih _ _ _ (hₒ.2 _) (hq.2 _) _).mono (by simp [isGroupOp]; omega)

private theorem groupStep_count (z : Handle) (t : Query F groupSig) (st : SimState)
    (r : (spec F groupSig).Range t × SimState)
    (hr : r ∈ support ((groupStep z t).run st)) : r.2.count = st.count := by
  simp only [groupStep, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨u, _, rfl⟩ := hr
  rfl

private theorem prefix_bound [SampleableType F] (z : Handle) (k : ℕ)
    (A : GenericAdversary F) (qₒ : ℕ)
    (hₒ : IsQueryBoundP A (fun i => isGroupOp i = true) qₒ) (st : SimState) :
    IsQueryBoundP ((runPrefix z k A).run st)
      (fun i => isGroupOp i = true) (qₒ + 3 * (k - st.count)) := by
  induction A using OracleComp.inductionOn generalizing qₒ st with
  | pure b => exact isQueryBoundP_pure _ _ _
  | query_bind t cont ih =>
    rw [isQueryBoundP_query_bind_iff] at hₒ
    rcases t with t | (n | mm)
    · change IsQueryBoundP ((groupStep z t).run st >>= fun r =>
        (runPrefix z k (cont r.1)).run r.2) _ _
      refine (isQueryBoundP_bind (m :=
        (if isGroupOp (.inl t : (spec F groupSig +
          (unifSpec + (HandlePair →ₒ HandlePair))).Domain) = true then qₒ - 1 else qₒ) +
          3 * (k - st.count)) (groupStep_bound z t st) (fun r hr => ?_)).mono ?_
      · have hb := ih r.1 _ (hₒ.2 r.1) r.2
        rwa [groupStep_count z t st r hr] at hb
      · simp only [isGroupOp] at *
        split <;> grind
    · change IsQueryBoundP (liftM ((genSpec F groupSig).query (.inr n)) >>= fun u =>
        (runPrefix z k (cont u)).run st) _ _
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (by simp [isGroupOp]), fun u => ih u _ (hₒ.2 u) st⟩
    · change IsQueryBoundP (cacheFind F (translate z st mm) st.cache >>= _) _ _
      refine (isQueryBoundP_bind (m := qₒ + 3 * (k - st.count))
        (cacheFind_bound (F := F) _ _) ?_).mono (by omega)
      intro cached _
      cases cached with
      | some c => exact ih _ _ (hₒ.2 _) _
      | none =>
        dsimp only
        split
        · rename_i hlt
          change IsQueryBoundP (encrypt (F := F) (translate z st mm).1 >>= fun c =>
            (runPrefix z k (cont (record { st with
              cache := (translate z st mm, c) :: st.cache, count := st.count + 1 } c).1)).run
                (record { st with
                  cache := (translate z st mm, c) :: st.cache, count := st.count + 1 } c).2) _ _
          refine (isQueryBoundP_bind (m := qₒ + 3 * (k - (st.count + 1)))
            (encrypt_bound _) (fun c _ => ih _ _ (hₒ.2 _) _)).mono ?_
          omega
        · exact isQueryBoundP_pure _ _ _

private def PrefixResult.Bounded
    (p : (spec F groupSig + (unifSpec + (HandlePair →ₒ HandlePair))).Domain → Prop)
    [DecidablePred p] (n : ℕ) : PrefixResult F → Prop
  | .done _ => True
  | .paused _ cont => ∀ c, IsQueryBoundP (cont c) p n

private theorem prefix_bounded [SampleableType F] (z : Handle) (k : ℕ)
    (p : (spec F groupSig + (unifSpec + (HandlePair →ₒ HandlePair))).Domain → Prop)
    [DecidablePred p] (A : GenericAdversary F) (n : ℕ) (h : IsQueryBoundP A p n)
    (st : SimState) (r : PrefixResult F × SimState)
    (hr : r ∈ support ((runPrefix z k A).run st)) : r.1.Bounded p n := by
  induction A using OracleComp.inductionOn generalizing st r with
  | pure b =>
      change r ∈ support (pure (.done b, st) : OracleComp (genSpec F groupSig) _) at hr
      rw [mem_support_pure_iff] at hr
      subst r
      trivial
  | query_bind t cont ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      have hc u : IsQueryBoundP (cont u) p n := (h.2 u).mono (by split <;> omega)
      rcases t with t | (j | mm)
      · change r ∈ support ((groupStep z t).run st >>= fun u =>
          (runPrefix z k (cont u.1)).run u.2) at hr
        rw [mem_support_bind_iff] at hr
        obtain ⟨u, _, hu⟩ := hr
        exact ih u.1 (hc u.1) u.2 r hu
      · change r ∈ support (liftM ((genSpec F groupSig).query (.inr j)) >>= fun u =>
          (runPrefix z k (cont u)).run st) at hr
        rw [mem_support_bind_iff] at hr
        obtain ⟨u, _, hu⟩ := hr
        exact ih u (hc u) st r hu
      · change r ∈ support (cacheFind F (translate z st mm) st.cache >>= _) at hr
        rw [mem_support_bind_iff] at hr
        obtain ⟨cached, _, hr⟩ := hr
        cases cached with
        | some c => exact ih _ (hc _) _ r hr
        | none =>
          dsimp only at hr
          split at hr
          · rw [mem_support_bind_iff] at hr
            obtain ⟨c, _, hr⟩ := hr
            exact ih _ (hc _) _ r hr
          · rw [mem_support_pure_iff] at hr
            subst r
            exact hc

/-- Message selection uses at most the original operation budget plus three operations per
preceding fresh query and one operation to create a private zero handle. For `k < q` this is
at most `qₒ + 3 * q`. -/
theorem isQueryBoundP_step_chooseMessages [Zero F] [SampleableType F]
    (A : GenericAdversary F) (qₒ q k : ℕ)
    (hₒ : IsQueryBoundP A (fun i => isGroupOp i = true) qₒ) (hk : k < q) :
    IsQueryBoundP (A.step k).chooseMessages (fun i => isGroupOp i = true) (qₒ + 3 * q) := by
  change IsQueryBoundP (liftM ((genSpec F groupSig).query (.inl (.smul () 0 0))) >>= _) _ _
  erw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr (by omega), fun z => ?_⟩
  refine (isQueryBoundP_bind (prefix_bound z k A qₒ hₒ ⟨fun _ => [0, 1], [], 0⟩)
    (m := 0) ?_).mono ?_
  · rintro ⟨res, st⟩ _
    cases res <;> exact isQueryBoundP_pure _ _ _
  · simp [isGroupOp]
    omega

/-- Every reachable paused continuation retains the original operation and left/right bounds.
Consequently the second phase uses at most `qₒ + 3 * q` group operations, for any challenge
handles, without a budget hypothesis on unreachable states. -/
theorem isQueryBoundP_step_distinguish [Zero F] [SampleableType F]
    (A : GenericAdversary F) (qₒ q k : ℕ)
    (hₒ : IsQueryBoundP A (fun i => isGroupOp i = true) qₒ)
    (hq : IsQueryBoundP A (· matches .inr (.inr _)) q)
    (out : Handle × Handle × (A.step k).State) (hout : out ∈ support (A.step k).chooseMessages)
    (a b : Handle) :
    IsQueryBoundP ((A.step k).distinguish out.2.2 a b)
      (fun i => isGroupOp i = true) (qₒ + 3 * q) := by
  change out ∈ support (liftM ((genSpec F groupSig).query (.inl (.smul () 0 0))) >>= _) at hout
  erw [mem_support_bind_iff] at hout
  obtain ⟨z, _, hout⟩ := hout
  erw [mem_support_bind_iff] at hout
  obtain ⟨⟨res, st⟩, hs, hout⟩ := hout
  have ho' := prefix_bounded z k _ A qₒ hₒ _ (res, st) hs
  have hq' := prefix_bounded z k _ A q hq _ (res, st) hs
  cases res with
  | done guess =>
      erw [mem_support_pure_iff] at hout
      subst out
      exact isQueryBoundP_pure _ _ _
  | paused mm cont =>
      erw [mem_support_pure_iff] at hout
      subst out
      exact (isQueryBoundP_map_iff _ _ _).2 (suffix_bound z _ qₒ q (ho' _) (hq' _) _)

/-- The extracted generic one-time adversary has unconditional advantage at most twice the
quadratic generic DDH bound. Each phase uses `qₒ + 3 * q` operations; the DDH reduction and its
initial table account for the additional seven entries in the collision bound. -/
theorem oneTimeAdvantage_step_toOneTime_le [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
    {gen : G} (hg : Function.Bijective (· • gen : F → G))
    (A : GenericAdversary F) (qₒ q k : ℕ)
    (hₒ : IsQueryBoundP A (fun i => isGroupOp i = true) qₒ)
    (hq : IsQueryBoundP A (· matches .inr (.inr _)) q) (hk : k < q) :
    AsymmEncAlg.IND_CPA_OneTime_Advantage (elGamalAsymmEnc F G gen)
      ProbCompRuntime.probComp ((A.step k).toOneTime gen) ≤
        2 * ((3 * (2 * (qₒ + 3 * q) + 7).choose 2 : ℕ) / (Fintype.card F : ℝ≥0∞)) := by
  simpa only [two_mul] using oneTimeAdvantage_toOneTime_le hg (A.step k)
    (qₒ + 3 * q) (qₒ + 3 * q)
    (isQueryBoundP_step_chooseMessages A qₒ q k hₒ hk)
    (isQueryBoundP_step_distinguish A qₒ q k hₒ hq)

private def readPair [Zero G] (tbl : Tbl (fun _ : Unit => G)) (p : HandlePair) : G × G :=
  (lookup tbl () p.1, lookup tbl () p.2)

private def cacheRead [DecidableEq G] [Zero G] (tbl : Tbl (fun _ : Unit => G))
    (mm : G × G) : List (HandlePair × HandlePair) → Option (G × G)
  | [] => none
  | (nn, c) :: cs => if mm = readPair tbl nn then some (readPair tbl c) else cacheRead tbl mm cs

private def cacheLookup [DecidableEq G] [Zero G] (tbl : Tbl (fun _ : Unit => G))
    (mm : HandlePair) : List (HandlePair × HandlePair) → Option HandlePair
  | [] => none
  | (nn, c) :: cs => if readPair tbl mm = readPair tbl nn then some c else cacheLookup tbl mm cs

private theorem cacheLookup_map [DecidableEq G] [Zero G] (tbl : Tbl (fun _ : Unit => G))
    (mm : HandlePair) (cs : List (HandlePair × HandlePair)) :
    (cacheLookup tbl mm cs).map (readPair tbl) = cacheRead tbl (readPair tbl mm) cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [cacheLookup, cacheRead]; split <;> simp_all

private theorem cacheLookup_mem [DecidableEq G] [Zero G] (tbl : Tbl (fun _ : Unit => G))
    (mm c : HandlePair) (cs : List (HandlePair × HandlePair))
    (hc : cacheLookup tbl mm cs = some c) : ∃ nn, (nn, c) ∈ cs := by
  induction cs with
  | nil => simp [cacheLookup] at hc
  | cons e cs ih =>
      simp only [cacheLookup] at hc
      split at hc
      · cases Option.some.inj hc
        exact ⟨e.1, List.mem_cons_self⟩
      · obtain ⟨nn, hn⟩ := ih hc
        exact ⟨nn, List.mem_cons_of_mem _ hn⟩

private theorem runGen_cacheFind [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (tbl : Tbl (fun _ : Unit => G)) (mm : HandlePair) (cs : List (HandlePair × HandlePair)) :
    runGen (Model.group (F := F) G) (fun _ => id) (cacheFind F mm cs) tbl =
        pure (cacheLookup tbl mm cs, tbl) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      rw [cacheFind, runGen_bind]
      change (pure (decide (lookup tbl () mm.1 = lookup tbl () c.1.1), tbl) >>= _) = _
      erw [pure_bind, runGen_bind]
      change (pure (decide (lookup tbl () mm.2 = lookup tbl () c.1.2), tbl) >>= _) = _
      erw [pure_bind]
      by_cases he : readPair tbl mm = readPair tbl c.1
      · have ha := congrArg Prod.fst he
        have hb := congrArg Prod.snd he
        simp only [readPair] at ha hb
        simp only [ha, hb, decide_true, Bool.and_self, ↓reduceIte, cacheLookup, he]
        rfl
      · have he' : ¬(lookup tbl () mm.1 = lookup tbl () c.1.1 ∧
            lookup tbl () mm.2 = lookup tbl () c.1.2) := by
          simpa only [readPair, Prod.mk.injEq] using he
        simpa only [Bool.and_eq_true, decide_eq_true_eq, he', ↓reduceIte, cacheLookup, he] using ih

/-! ## Splitting the real counted execution -/

private structure RealState (G : Type) where
  table : Tbl (fun _ : Unit => G)
  cache : (G × G →ₒ G × G).QueryCache
  count : ℕ

private def realRecord (st : RealState G) (c : G × G) : HandlePair × RealState G :=
  (((st.table ()).length, (st.table ()).length + 1),
    { st with table := append (append st.table () c.1) () c.2 })

private def realGroup [Field F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (t : Query F groupSig) (st : RealState G) :
    (spec F groupSig).Range t × RealState G :=
  let r := (impl (Model.group G) (fun _ => id) Id t).run st.table
  (r.1, { st with table := r.2 })

private inductive RealPrefixResult (F G : Type)
  | done (b : Bool)
  | paused (mm : G × G) (cont : HandlePair → GenericAdversary F)

section RealExecution

variable [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]

private def realRun (gen pk : G) (n : ℕ) : GenericAdversary F → RealState G → ProbComp Bool :=
  OracleComp.construct
    (C := fun _ => RealState G → ProbComp Bool)
    (fun b _ => pure b)
    (fun t _ rec => match t with
      | .inl t => fun st =>
          let r := realGroup t st
          rec r.1 r.2
      | .inr (.inl u) => fun st => do
          let v ← unifSpec.query u
          rec v st
      | .inr (.inr mm) => fun st => do
          let nn := readPair st.table mm
          match st.cache nn with
          | some c =>
              let r := realRecord st c
              rec r.1 r.2
          | none =>
              let c ← (elGamalAsymmEnc F G gen).encrypt pk
                (if st.count < n then nn.1 else nn.2)
              let r := realRecord
                { st with cache := st.cache.cacheQuery nn c, count := st.count + 1 } c
              rec r.1 r.2)

private def realPrefix (gen pk : G) (k : ℕ) :
    GenericAdversary F → RealState G → ProbComp (RealPrefixResult F G × RealState G) :=
  OracleComp.construct
    (C := fun _ => RealState G → ProbComp (RealPrefixResult F G × RealState G))
    (fun b st => pure (.done b, st))
    (fun t cont rec => match t with
      | .inl t => fun st =>
          let r := realGroup t st
          rec r.1 r.2
      | .inr (.inl u) => fun st => do
          let v ← unifSpec.query u
          rec v st
      | .inr (.inr mm) => fun st => do
          let nn := readPair st.table mm
          match st.cache nn with
          | some c =>
              let r := realRecord st c
              rec r.1 r.2
          | none =>
              if st.count < k then
                let c ← (elGamalAsymmEnc F G gen).encrypt pk nn.1
                let r := realRecord
                  { st with cache := st.cache.cacheQuery nn c, count := st.count + 1 } c
                rec r.1 r.2
              else pure (.paused nn cont, st))

private theorem realRun_lr (gen pk : G) (n : ℕ) (mm : HandlePair)
    (cont : HandlePair → GenericAdversary F) (st : RealState G) :
    realRun gen pk n
      (liftM ((spec F groupSig + (unifSpec + (HandlePair →ₒ HandlePair))).query
        (.inr (.inr mm))) >>= cont :
        OracleComp (spec F groupSig + (unifSpec + (HandlePair →ₒ HandlePair))) Bool) st =
      (match st.cache (readPair st.table mm) with
      | some c => realRun gen pk n (cont (realRecord st c).1) (realRecord st c).2
      | none => do
          let c ← (elGamalAsymmEnc F G gen).encrypt pk
            (if st.count < n then (readPair st.table mm).1 else (readPair st.table mm).2)
          let s := realRecord { st with
            cache := st.cache.cacheQuery (readPair st.table mm) c, count := st.count + 1 } c
          realRun gen pk n (cont s.1) s.2) := by
  simp only [realRun, construct_query_bind]
  split <;> simp_all

private theorem realPrefix_lr (gen pk : G) (k : ℕ) (mm : HandlePair)
    (cont : HandlePair → GenericAdversary F) (st : RealState G) :
    realPrefix gen pk k
      (liftM ((spec F groupSig + (unifSpec + (HandlePair →ₒ HandlePair))).query
        (.inr (.inr mm))) >>= cont :
        OracleComp (spec F groupSig + (unifSpec + (HandlePair →ₒ HandlePair))) Bool) st =
      (match st.cache (readPair st.table mm) with
      | some c => realPrefix gen pk k (cont (realRecord st c).1) (realRecord st c).2
      | none =>
          if st.count < k then do
            let c ← (elGamalAsymmEnc F G gen).encrypt pk (readPair st.table mm).1
            let s := realRecord { st with
              cache := st.cache.cacheQuery (readPair st.table mm) c, count := st.count + 1 } c
            realPrefix gen pk k (cont s.1) s.2
          else pure (.paused (readPair st.table mm) cont, st)) := by
  simp only [realPrefix, construct_query_bind]
  split <;> simp_all

private theorem realRun_eq_counted (gen pk : G) (n : ℕ) (A : GenericAdversary F)
    (st : RealState G) :
    realRun gen pk n A st =
      Prod.fst <$> ((simulateQ ((elGamalAsymmEnc F G gen).IND_CPA_queryImpl_hybridLR_counted pk n)
        (run (Model.group G) (fun _ => id) (queryImpl (F := F) gen) A st.table)).run'
          (st.cache, st.count)) := by
  induction A using OracleComp.inductionOn generalizing st with
  | pure b => rfl
  | query_bind t cont ih =>
      rcases t with t | (u | mm)
      · cases t <;> exact ih _ _
      · have hr : run (Model.group G) (fun _ => id) (queryImpl (F := F) gen)
            (liftM ((spec F groupSig + (unifSpec + (HandlePair →ₒ HandlePair))).query
              (.inr (.inl u))) >>= cont) st.table =
            (do
              let v ← liftM ((elGamalAsymmEnc F G gen).IND_CPA_oracleSpec.query (.inl u))
              run (Model.group G) (fun _ => id) (queryImpl (F := F) gen) (cont v) st.table) := by
          simp only [run, simulateQ_query_bind, StateT.run_bind]
          change ((liftM ((elGamalAsymmEnc F G gen).IND_CPA_oracleSpec.query (.inl u)) >>=
            fun v => pure (v, st.table)) >>= _) = _
          erw [bind_assoc]
        rw [hr]
        simp only [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind, map_bind]
        change (liftM (unifSpec.query u) >>= fun v => realRun gen pk n (cont v) st) =
          Prod.fst <$> (Prod.fst <$> ((do
            let v ← unifSpec.query u
            pure (v, (st.cache, st.count))) >>= fun r =>
              (simulateQ ((elGamalAsymmEnc F G gen).IND_CPA_queryImpl_hybridLR_counted pk n)
                (run (Model.group G) (fun _ => id) (queryImpl (F := F) gen)
                  (cont r.1) st.table)).run r.2))
        simp only [bind_assoc, pure_bind, map_bind]
        congr 1
        funext v
        exact ih v st
      · have hr : run (Model.group G) (fun _ => id) (queryImpl (F := F) gen)
            (liftM ((spec F groupSig + (unifSpec + (HandlePair →ₒ HandlePair))).query
              (.inr (.inr mm))) >>= cont) st.table =
            (do
              let c ← liftM ((elGamalAsymmEnc F G gen).IND_CPA_oracleSpec.query
                (.inr (readPair st.table mm)))
              run (Model.group G) (fun _ => id) (queryImpl (F := F) gen)
                (cont (realRecord st c).1) (realRecord st c).2.table) := by
          simp only [run, simulateQ_query_bind, StateT.run_bind]
          change ((liftM ((elGamalAsymmEnc F G gen).IND_CPA_oracleSpec.query
            (.inr (readPair st.table mm))) >>= fun c =>
              pure ((realRecord st c).1, (realRecord st c).2.table)) >>= _) = _
          erw [bind_assoc]
        rw [hr]
        simp only [simulateQ_query_bind, StateT.run'_eq, StateT.run_bind]
        change _ =
          Prod.fst <$> (Prod.fst <$>
            (((elGamalAsymmEnc F G gen).IND_CPA_hybridChallengeOracleLR_counted pk n
              (readPair st.table mm)).run (st.cache, st.count) >>= fun r =>
              (simulateQ ((elGamalAsymmEnc F G gen).IND_CPA_queryImpl_hybridLR_counted pk n)
                (run (Model.group G) (fun _ => id) (queryImpl (F := F) gen)
                  (cont (realRecord st r.1).1) (realRecord st r.1).2.table)).run r.2))
        rcases hc : st.cache (readPair st.table mm) with _ | c
        · rw [AsymmEncAlg.IND_CPA_hybridChallengeOracleLR_counted_run_none _ _ _ _ hc]
          simp only [realRun, construct_query_bind, hc, bind_assoc, pure_bind, map_bind]
          congr 1
          funext c
          exact ih _ _
        · rw [AsymmEncAlg.IND_CPA_hybridChallengeOracleLR_counted_run_some _ _ _ _ _ hc]
          simp only [realRun, construct_query_bind, hc, pure_bind]
          exact ih _ _

private theorem realRun_above (gen pk : G) (k n : ℕ) (A : GenericAdversary F)
    (st : RealState G) (hk : k ≤ st.count) (hn : n ≤ st.count) :
    realRun gen pk k A st = realRun gen pk n A st := by
  induction A using OracleComp.inductionOn generalizing st with
  | pure b => rfl
  | query_bind t cont ih =>
      rcases t with t | (u | mm)
      · exact ih _ _ hk hn
      · change (liftM (unifSpec.query u) >>= fun v => realRun gen pk k (cont v) st) =
          (liftM (unifSpec.query u) >>= fun v => realRun gen pk n (cont v) st)
        congr 1
        funext v
        exact ih v st hk hn
      · simp only [realRun, construct_query_bind]
        split
        · exact ih _ _ hk hn
        · simp only [show ¬st.count < k by omega, show ¬st.count < n by omega, ↓reduceIte]
          congr 1
          funext c
          exact ih _ _ (by dsimp [realRecord]; omega) (by dsimp [realRecord]; omega)

private def realResume (gen pk : G) (k : ℕ) (branch : Bool)
    (r : RealPrefixResult F G × RealState G) : ProbComp Bool :=
  match r.1 with
  | .done b => pure b
  | .paused mm cont => do
      let c ← (elGamalAsymmEnc F G gen).encrypt pk (if branch then mm.1 else mm.2)
      let s := realRecord
        { r.2 with cache := r.2.cache.cacheQuery mm c, count := r.2.count + 1 } c
      realRun gen pk k (cont s.1) s.2

private theorem realPrefix_resume (gen pk : G) (k : ℕ) (branch : Bool)
    (A : GenericAdversary F) (st : RealState G) (hst : st.count ≤ k) :
    (realPrefix gen pk k A st >>= realResume gen pk k branch) =
      realRun gen pk (if branch then k + 1 else k) A st := by
  induction A using OracleComp.inductionOn generalizing st with
  | pure b => rfl
  | query_bind t cont ih =>
      rcases t with t | (u | mm)
      · exact ih _ _ hst
      · change ((liftM (unifSpec.query u) >>= fun v => realPrefix gen pk k (cont v) st) >>=
          realResume gen pk k branch) =
          (liftM (unifSpec.query u) >>= fun v =>
            realRun gen pk (if branch then k + 1 else k) (cont v) st)
        rw [bind_assoc]
        congr 1
        funext v
        exact ih v st hst
      · simp only [realPrefix, realRun, construct_query_bind]
        split
        · exact ih _ _ hst
        · by_cases hlt : st.count < k
          · have hb : st.count < (if branch then k + 1 else k) := by
              cases branch <;> simp_all
            simp only [hlt, hb, ↓reduceIte, bind_assoc]
            congr 1
            funext c
            exact ih _ _ (by dsimp [realRecord]; omega)
          · have he : st.count = k := by omega
            simp only [hlt, ↓reduceIte, pure_bind, realResume]
            have hb : (if st.count < (if branch then k + 1 else k)
                then (readPair st.table mm).1 else (readPair st.table mm).2) =
                (if branch then (readPair st.table mm).1 else (readPair st.table mm).2) := by
              cases branch <;> simp [he]
            rw [hb]
            congr 1
            funext c
            apply realRun_above <;> dsimp [realRecord] <;> cases branch <;> simp_all

end RealExecution

/-! ## Read-back invariants -/

private def ValidPair (T : Tbl (fun _ : Unit => G)) (p : HandlePair) : Prop :=
  p.1 < (T ()).length ∧ p.2 < (T ()).length

private def CacheValid (T : Tbl (fun _ : Unit => G)) (cs : List (HandlePair × HandlePair)) : Prop :=
  ∀ p ∈ cs, ValidPair T p.1 ∧ ValidPair T p.2

private def readState [Zero G] [DecidableEq G] (st : SimState)
    (T : Tbl (fun _ : Unit => G)) : RealState G :=
  ⟨readBack st.translation T, QueryCache.ofFn (fun mm => cacheRead T mm st.cache), st.count⟩

private structure SimInv [Zero G] (gen pk : G) (z : Handle) (st : SimState)
    (T : Tbl (fun _ : Unit => G)) : Prop where
  wf : WellFormed (fun _ => z) st.translation T
  keyLen : 1 < (T ()).length
  generator : lookup T () 0 = gen
  publicKey : lookup T () 1 = pk
  cacheValid : CacheValid T st.cache

private theorem ValidPair.mono {T T' : Tbl (fun _ : Unit => G)} {p : HandlePair}
    (h : ValidPair T p) (hp : T () <+: T' ()) : ValidPair T' p :=
  ⟨lt_of_lt_of_le h.1 hp.length_le, lt_of_lt_of_le h.2 hp.length_le⟩

private theorem readPair_prefix [Zero G] {T T' : Tbl (fun _ : Unit => G)} {p : HandlePair}
    (h : ValidPair T p) (hp : T () <+: T' ()) : readPair T' p = readPair T p := by
  exact Prod.ext (lookup_eq_of_prefix () hp p.1 h.1) (lookup_eq_of_prefix () hp p.2 h.2)

private theorem cacheRead_prefix [Zero G] [DecidableEq G]
    {T T' : Tbl (fun _ : Unit => G)} (cs : List (HandlePair × HandlePair))
    (h : CacheValid T cs) (hp : T () <+: T' ()) (mm : G × G) :
    cacheRead T' mm cs = cacheRead T mm cs := by
  induction cs with
  | nil => rfl
  | cons p cs ih =>
      have hv := h p List.mem_cons_self
      simp only [cacheRead, readPair_prefix hv.1 hp, readPair_prefix hv.2 hp]
      rw [ih (fun p hp => h p (List.mem_cons_of_mem _ hp))]

private theorem SimInv.mono [Zero G] {gen pk : G} {z : Handle} {st : SimState}
    {T T' : Tbl (fun _ : Unit => G)} (h : SimInv gen pk z st T)
    (hp : T () <+: T' ()) : SimInv gen pk z st T' := by
  refine ⟨?_, lt_of_lt_of_le h.keyLen hp.length_le, ?_, ?_, ?_⟩
  · intro u
    cases u
    exact ⟨fun a ha => lt_of_lt_of_le ((h.wf ()).1 a ha) hp.length_le,
      lt_of_lt_of_le (h.wf ()).2.1 hp.length_le,
      (lookup_eq_of_prefix () hp z (h.wf ()).2.1).trans (h.wf ()).2.2⟩
  · exact (lookup_eq_of_prefix () hp 0 (lt_trans Nat.zero_lt_one h.keyLen)).trans h.generator
  · exact (lookup_eq_of_prefix () hp 1 h.keyLen).trans h.publicKey
  · intro p hm
    exact ⟨((h.cacheValid p hm).1).mono hp, ((h.cacheValid p hm).2).mono hp⟩

private theorem readState_prefix [Zero G] [DecidableEq G]
    {gen pk : G} {z : Handle} {st : SimState} {T T' : Tbl (fun _ : Unit => G)}
    (h : SimInv gen pk z st T) (hp : T () <+: T' ()) : readState st T' = readState st T := by
  have ht : readBack st.translation T' = readBack st.translation T := by
    funext u
    cases u
    apply List.map_congr_left
    intro a ha
    exact lookup_eq_of_prefix () hp a ((h.wf ()).1 a ha)
  unfold readState
  rw [ht]
  congr 2
  funext mm
  exact cacheRead_prefix st.cache h.cacheValid hp mm

private theorem translate_valid [Zero G] {z : Handle} {st : SimState}
    {T : Tbl (fun _ : Unit => G)} (h : WellFormed (fun _ => z) st.translation T)
    (mm : HandlePair) : ValidPair T (translate z st mm) := by
  have hb (a : Handle) : (st.translation ()).getD a z < (T ()).length := by
    by_cases ha : a < (st.translation ()).length
    · simpa [List.getD_eq_getElem?_getD, ha] using
        (h ()).1 _ (List.getElem_mem ha)
    · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt ha)] using
          (h ()).2.1
  exact ⟨hb mm.1, hb mm.2⟩

private theorem translate_read [Zero G] {z : Handle} {st : SimState}
    {T : Tbl (fun _ : Unit => G)} (h : WellFormed (fun _ => z) st.translation T)
    (mm : HandlePair) :
    readPair T (translate z st mm) = readPair (readBack st.translation T) mm := by
  exact Prod.ext (lookup_readBack h () mm.1).symm (lookup_readBack h () mm.2).symm

private theorem record_read [Zero G] [DecidableEq G] (st : SimState)
    (T : Tbl (fun _ : Unit => G)) (c : HandlePair) :
    ((record st c).1, readState (record st c).2 T) =
      realRecord (readState st T) (readPair T c) := by
  apply Prod.ext
  · simp [record, readState, realRecord, readBack]
  · change RealState.mk _ _ _ = RealState.mk _ _ _
    congr 1
    funext u
    cases u
    simp [record, readState, readPair, readBack, append]

private theorem record_inv [Zero G] {gen pk : G} {z : Handle} {st : SimState}
    {T : Tbl (fun _ : Unit => G)} (h : SimInv gen pk z st T) (c : HandlePair)
    (hc : ValidPair T c) : SimInv gen pk z (record st c).2 T := by
  refine ⟨?_, h.keyLen, h.generator, h.publicKey, h.cacheValid⟩
  intro u
  cases u
  refine ⟨?_, (h.wf ()).2⟩
  intro a ha
  simp only [record, append, Function.update_self, List.mem_append, List.mem_singleton] at ha
  rcases ha with (ha | rfl) | rfl
  · exact (h.wf ()).1 a ha
  · exact hc.1
  · exact hc.2

private theorem cache_insert_read [Zero G] [DecidableEq G] (st : SimState)
    (T : Tbl (fun _ : Unit => G)) (mm c : HandlePair) :
    readState { st with cache := (mm, c) :: st.cache, count := st.count + 1 } T =
      { readState st T with
        cache := (readState st T).cache.cacheQuery (readPair T mm) (readPair T c)
        count := st.count + 1 } := by
  unfold readState
  congr 1
  apply QueryCache.ext
  intro nn
  by_cases he : nn = readPair T mm
  · subst nn
    simp [cacheRead]
  · simp [cacheRead, he, QueryCache.cacheQuery_of_ne]

private theorem cache_insert_inv [Zero G] {gen pk : G} {z : Handle} {st : SimState}
    {T : Tbl (fun _ : Unit => G)} (h : SimInv gen pk z st T) (mm c : HandlePair)
    (hm : ValidPair T mm) (hc : ValidPair T c) :
    SimInv gen pk z { st with cache := (mm, c) :: st.cache, count := st.count + 1 } T := by
  refine ⟨h.wf, h.keyLen, h.generator, h.publicKey, ?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact ⟨hm, hc⟩
  · exact h.cacheValid p hp

private theorem fresh_record_read [Zero G] [DecidableEq G]
    {gen pk : G} {z : Handle} {st : SimState} {T T' : Tbl (fun _ : Unit => G)}
    (h : SimInv gen pk z st T) (hp : T () <+: T' ()) (mm c : HandlePair)
    (hm : ValidPair T mm) :
    let s := record { st with cache := (mm, c) :: st.cache, count := st.count + 1 } c
    (s.1, readState s.2 T') =
      realRecord { readState st T with
        cache := (readState st T).cache.cacheQuery (readPair T mm) (readPair T' c)
        count := st.count + 1 } (readPair T' c) := by
  dsimp only
  rw [record_read, cache_insert_read, readState_prefix h hp, readPair_prefix hm hp]

private theorem fresh_record_inv [Zero G]
    {gen pk : G} {z : Handle} {st : SimState} {T T' : Tbl (fun _ : Unit => G)}
    (h : SimInv gen pk z st T) (hp : T () <+: T' ()) (mm c : HandlePair)
    (hm : ValidPair T mm) (hc : ValidPair T' c) :
    SimInv gen pk z (record
      { st with cache := (mm, c) :: st.cache, count := st.count + 1 } c).2 T' :=
  record_inv (cache_insert_inv (h.mono hp) mm c (hm.mono hp) hc) c hc

section GroupSteps

variable [Field F] [AddCommGroup G] [Module F G]

private def groupResult [DecidableEq G] (z : Handle) (t : Query F groupSig) (st : SimState)
    (T : Tbl (fun _ : Unit => G)) :
    ((spec F groupSig).Range t × SimState) × Tbl (fun _ : Unit => G) :=
  run (Model.group G) (fun _ => id) (m := Id) (fun _ => pure 0)
    ((groupStep z t).run st) T

private theorem runGen_groupStep [DecidableEq G] (z : Handle) (t : Query F groupSig) (st : SimState)
    (T : Tbl (fun _ : Unit => G)) :
    runGen (Model.group G) (fun _ => id) ((groupStep z t).run st) T =
      pure (groupResult z t st T) := by
  cases t <;> rfl

private theorem groupResult_inv [DecidableEq G] {gen pk : G} {z : Handle} {st : SimState}
    {T : Tbl (fun _ : Unit => G)} (h : SimInv gen pk z st T) (t : Query F groupSig) :
    SimInv gen pk z (groupResult z t st T).1.2 (groupResult z t st T).2 := by
  let r := groupResult z t st T
  have hs : r ∈ support (runGen (Model.group G) (fun _ => id) ((groupStep z t).run st) T) := by
    rw [runGen_groupStep]
    exact (mem_support_pure_iff _ _).2 rfl
  have hp := runGen_prefix (Model.group G) (fun _ => id) ((groupStep z t).run st) T r hs ()
  have hv := h.mono hp
  have ht : WellFormed (fun _ => z) r.1.2.translation r.2 :=
    wellFormed_runGen_virtualizeImpl (Model.group (F := F) G) (fun _ => id)
      h.wf (.inl t)
      ((r.1.1, r.1.2.translation), r.2) (by
        cases t <;> change _ ∈ support (pure _ : ProbComp _) <;>
          rw [mem_support_pure_iff] <;> rfl)
  refine ⟨ht, hv.keyLen, hv.generator, hv.publicKey, ?_⟩
  have hc : r.1.2.cache = st.cache := by cases t <;> rfl
  rw [show CacheValid r.2 r.1.2.cache = CacheValid r.2 st.cache by rw [hc]]
  exact hv.cacheValid

private theorem groupResult_read [DecidableEq G] {gen pk : G} {z : Handle} {st : SimState}
    {T : Tbl (fun _ : Unit => G)} (h : SimInv gen pk z st T) (t : Query F groupSig) :
    ((groupResult z t st T).1.1,
      readState (groupResult z t st T).1.2 (groupResult z t st T).2) =
        realGroup t (readState st T) := by
  let r := groupResult z t st T
  have hs : r ∈ support (runGen (Model.group G) (fun _ => id) ((groupStep z t).run st) T) := by
    rw [runGen_groupStep]
    exact (mem_support_pure_iff _ _).2 rfl
  have hp := runGen_prefix (Model.group G) (fun _ => id) ((groupStep z t).run st) T r hs ()
  have hv := runGen_virtualize (Model.group (F := F) G) (fun _ => id)
    (liftM ((genSpec F groupSig).query (.inl t))) h.wf
  have he : (pure ((realGroup t (readState st T)).1, (realGroup t (readState st T)).2.table) :
      ProbComp _) = pure (r.1.1, readBack r.1.2.translation r.2) := by
    cases t <;> exact hv
  have he' := (pure_inj _ _).mp he
  apply Prod.ext
  · exact (congrArg Prod.fst he').symm
  · have hc : r.1.2.cache = st.cache := by cases t <;> rfl
    change RealState.mk _ _ _ = RealState.mk _ _ _
    congr 1
    · exact (congrArg Prod.snd he').symm
    · apply QueryCache.ext
      intro mm
      change cacheRead r.2 mm r.1.2.cache = cacheRead T mm st.cache
      rw [hc, cacheRead_prefix st.cache h.cacheValid hp]
    · cases t <;> rfl

private theorem runGen_liftCoins [DecidableEq G] {α : Type} (A : ProbComp α)
    (T : Tbl (fun _ : Unit => G)) :
    runGen (Model.group (F := F) G) (fun _ => id)
      (simulateQ (fun n => liftM ((genSpec F groupSig).query (.inr n))) A) T =
        (fun a => (a, T)) <$> A := by
  induction A using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind n cont ih =>
      rw [simulateQ_query_bind, runGen_bind]
      change (((fun a => (a, T)) <$> liftM (unifSpec.query n)) >>= _) = _
      erw [bind_map_left]
      simp only [map_bind]
      congr 1
      funext a
      exact ih a

private def cipherResult (T : Tbl (fun _ : Unit => G)) (m : Handle) (r : F) :
    HandlePair × Tbl (fun _ : Unit => G) :=
  (((T ()).length, (T ()).length + 2),
    append (append (append T () (r • lookup T () 0)) () (r • lookup T () 1)) ()
      (lookup T () m + r • lookup T () 1))

private theorem runGen_encrypt [DecidableEq G] [SampleableType F] (T : Tbl (fun _ : Unit => G))
    (m : Handle) (hm : m < (T ()).length) (hkey : 1 < (T ()).length) :
    runGen (Model.group (F := F) G) (fun _ => id) (encrypt m) T =
      (fun r => cipherResult T m r) <$> ($ᵗ F) := by
  rw [encrypt, runGen_bind, runGen_liftCoins, bind_map_left, map_eq_bind_pure_comp]
  congr 1
  funext r
  erw [runGen_bind]
  change (pure ((T ()).length, append T () (r • lookup T () 0)) >>= _) = _
  erw [pure_bind, runGen_bind]
  change (pure (((append T () (r • lookup T () 0)) ()).length,
    append (append T () (r • lookup T () 0)) ()
      (r • lookup (append T () (r • lookup T () 0)) () 1)) >>= _) = _
  rw [lookup_eq_of_prefix () (prefix_append T () () _) 1 hkey]
  erw [pure_bind, runGen_bind]
  let T₁ := append T () (r • lookup T () 0)
  let T₂ := append T₁ () (r • lookup T () 1)
  have hp₁ : T () <+: T₁ () := prefix_append T () () _
  have hp₂ : T₁ () <+: T₂ () := prefix_append T₁ () () _
  change (pure ((T₂ ()).length,
    append T₂ () (lookup T₂ () m + lookup T₂ () (T₁ ()).length)) >>= _) = _
  rw [lookup_eq_of_prefix () (hp₁.trans hp₂) m hm]
  have hpad : lookup T₂ () (T₁ ()).length = r • lookup T () 1 := by
    simp [T₂, lookup, append]
  rw [hpad]
  erw [pure_bind]
  change pure (((T ()).length, (T₂ ()).length),
    append T₂ () (lookup T () m + r • lookup T () 1)) =
      (pure (cipherResult T m r) : ProbComp _)
  simp [cipherResult, T₂, T₁, append]

private theorem cipherResult_prefix (T : Tbl (fun _ : Unit => G)) (m : Handle) (r : F) :
    T () <+: (cipherResult T m r).2 () := by
  exact (prefix_append T () () _).trans
    ((prefix_append (append T () _) () () _).trans
      (prefix_append (append (append T () _) () _) () () _))

private theorem cipherResult_valid (T : Tbl (fun _ : Unit => G)) (m : Handle) (r : F) :
    ValidPair (cipherResult T m r).2 (cipherResult T m r).1 := by
  simp [ValidPair, cipherResult, append]

private theorem cipherResult_read (T : Tbl (fun _ : Unit => G)) (m : Handle) (r : F) :
    readPair (cipherResult T m r).2 (cipherResult T m r).1 =
      (r • lookup T () 0, lookup T () m + r • lookup T () 1) := by
  simp [readPair, cipherResult, append, lookup, List.getD_eq_getElem?_getD]

end GroupSteps

section Simulation

variable [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]

private theorem suffix_read (gen pk : G) (z : Handle) (A : GenericAdversary F)
    (st : SimState) (T : Tbl (fun _ : Unit => G)) (h : SimInv gen pk z st T) :
    (fun r => r.1.1) <$> runGen (Model.group G) (fun _ => id)
      ((simulateQ (suffixImpl z) A).run st) T = realRun gen pk 0 A (readState st T) := by
  induction A using OracleComp.inductionOn generalizing st T with
  | pure b => rfl
  | query_bind t cont ih =>
      rw [simulateQ_query_bind, StateT.run_bind]
      rcases t with t | (u | mm)
      · change (fun r => r.1.1) <$> runGen (Model.group G) (fun _ => id)
          ((groupStep z t).run st >>= fun r => (simulateQ (suffixImpl z) (cont r.1)).run r.2) T = _
        rw [runGen_bind, runGen_groupStep]
        erw [pure_bind]
        change _ = realRun gen pk 0 (cont (realGroup t (readState st T)).1)
          (realGroup t (readState st T)).2
        rw [← groupResult_read h t]
        exact ih _ _ _ (groupResult_inv h t)
      · change (fun r => r.1.1) <$> runGen (Model.group G) (fun _ => id)
          (liftM ((genSpec F groupSig).query (.inr u)) >>= fun v =>
            (simulateQ (suffixImpl z) (cont v)).run st) T = _
        rw [runGen_bind]
        change (fun r => r.1.1) <$> (((fun v => (v, T)) <$> liftM (unifSpec.query u)) >>=
          fun r => runGen (Model.group G) (fun _ => id)
            ((simulateQ (suffixImpl z) (cont r.1)).run st) r.2) = _
        erw [bind_map_left]
        simp only [map_bind]
        change _ = (liftM (unifSpec.query u) >>= fun v =>
          realRun gen pk 0 (cont v) (readState st T))
        congr 1
        funext v
        exact ih v st T h
      · change (fun r => r.1.1) <$> runGen (Model.group G) (fun _ => id)
          ((do
            match ← cacheFind F (translate z st mm) st.cache with
            | some c => pure (record st c)
            | none => do
                let c ← encrypt (F := F) (translate z st mm).2
                pure (record { st with
                  cache := (translate z st mm, c) :: st.cache
                  count := st.count + 1 } c)) >>= fun r =>
                    (simulateQ (suffixImpl z) (cont r.1)).run r.2) T = _
        erw [bind_assoc, runGen_bind, runGen_cacheFind, pure_bind]
        have hc' : (readState st T).cache (readPair (readState st T).table mm) =
            (cacheLookup T (translate z st mm) st.cache).map (readPair T) := by
          rw [cacheLookup_map, translate_read h.wf]
          rfl
        rw [realRun_lr]
        simp only [hc', Nat.not_lt_zero, ↓reduceIte]
        rcases hc : cacheLookup T (translate z st mm) st.cache with _ | c
        · simp only [Option.map_none]
          erw [bind_assoc, runGen_bind, runGen_encrypt T _ (translate_valid h.wf mm).2 h.keyLen]
          simp only [bind_map_left, map_bind]
          conv_rhs => simp only [elGamalAsymmEnc, bind_assoc, pure_bind]
          change _ = (($ᵗ F) >>= fun r =>
            realRun gen pk 0
              (cont (realRecord { readState st T with
                cache := (readState st T).cache.cacheQuery (readPair (readState st T).table mm)
                  (r • gen, (readPair (readState st T).table mm).2 + r • pk)
                count := st.count + 1 }
                (r • gen, (readPair (readState st T).table mm).2 + r • pk)).1)
              (realRecord { readState st T with
                cache := (readState st T).cache.cacheQuery (readPair (readState st T).table mm)
                  (r • gen, (readPair (readState st T).table mm).2 + r • pk)
                count := st.count + 1 }
                (r • gen, (readPair (readState st T).table mm).2 + r • pk)).2)
          congr 1
          funext r
          have he := fresh_record_read h (cipherResult_prefix T (translate z st mm).2 r)
            (translate z st mm) (cipherResult T (translate z st mm).2 r).1
            (translate_valid h.wf mm)
          have hm : lookup T () (translate z st mm).2 =
              (readPair (readState st T).table mm).2 := congrArg Prod.snd (translate_read h.wf mm)
          rw [cipherResult_read, h.generator, h.publicKey, hm, translate_read h.wf] at he
          erw [← he]
          exact ih _ _ _ (fresh_record_inv h (cipherResult_prefix T _ r) _ _
            (translate_valid h.wf mm) (cipherResult_valid T _ r))
        · simp only [Option.map_some]
          erw [pure_bind]
          rw [← record_read st T c]
          obtain ⟨nn, hn⟩ := cacheLookup_mem T (translate z st mm) c st.cache hc
          exact ih _ _ _ (record_inv h c (h.cacheValid (nn, c) hn).2)

private def readPrefix (r : (PrefixResult F × SimState) × Tbl (fun _ : Unit => G)) :
    RealPrefixResult F G × RealState G :=
  ((match r.1.1 with
    | .done b => .done b
    | .paused mm cont => .paused (readPair r.2 mm) cont), readState r.1.2 r.2)

private theorem prefix_read (gen pk : G) (z : Handle) (k : ℕ) (A : GenericAdversary F)
    (st : SimState) (T : Tbl (fun _ : Unit => G)) (h : SimInv gen pk z st T) :
    readPrefix <$> runGen (Model.group G) (fun _ => id) ((runPrefix z k A).run st) T =
      realPrefix gen pk k A (readState st T) := by
  induction A using OracleComp.inductionOn generalizing st T with
  | pure b => rfl
  | query_bind t cont ih =>
      simp only [runPrefix, construct_query_bind]
      rcases t with t | (u | mm)
      · change readPrefix <$> runGen (Model.group G) (fun _ => id)
          ((groupStep z t).run st >>= fun r => (runPrefix z k (cont r.1)).run r.2) T = _
        rw [runGen_bind, runGen_groupStep]
        erw [pure_bind]
        change _ = realPrefix gen pk k (cont (realGroup t (readState st T)).1)
          (realGroup t (readState st T)).2
        rw [← groupResult_read h t]
        exact ih _ _ _ (groupResult_inv h t)
      · change readPrefix <$> runGen (Model.group G) (fun _ => id)
          (liftM ((genSpec F groupSig).query (.inr u)) >>= fun v =>
            (runPrefix z k (cont v)).run st) T = _
        rw [runGen_bind]
        change readPrefix <$> (((fun v => (v, T)) <$> liftM (unifSpec.query u)) >>=
          fun r => runGen (Model.group G) (fun _ => id) ((runPrefix z k (cont r.1)).run st) r.2) = _
        erw [bind_map_left]
        simp only [map_bind]
        change _ = (liftM (unifSpec.query u) >>= fun v =>
          realPrefix gen pk k (cont v) (readState st T))
        congr 1
        funext v
        exact ih v st T h
      · change readPrefix <$> runGen (Model.group G) (fun _ => id)
          (cacheFind F (translate z st mm) st.cache >>= _) T = _
        erw [runGen_bind, runGen_cacheFind, pure_bind]
        have hc' : (readState st T).cache (readPair (readState st T).table mm) =
            (cacheLookup T (translate z st mm) st.cache).map (readPair T) := by
          rw [cacheLookup_map, translate_read h.wf]
          rfl
        rw [realPrefix_lr]
        simp only [hc']
        rcases hc : cacheLookup T (translate z st mm) st.cache with _ | c
        · simp only [Option.map_none]
          by_cases hlt : st.count < k
          · simp only [hlt, show (readState st T).count < k from hlt, ↓reduceIte]
            erw [runGen_bind, runGen_encrypt T _ (translate_valid h.wf mm).1 h.keyLen]
            simp only [bind_map_left, map_bind]
            conv_rhs => simp only [elGamalAsymmEnc, bind_assoc, pure_bind]
            change _ = (($ᵗ F) >>= fun r =>
              realPrefix gen pk k
                (cont (realRecord { readState st T with
                  cache := (readState st T).cache.cacheQuery (readPair (readState st T).table mm)
                    (r • gen, (readPair (readState st T).table mm).1 + r • pk)
                  count := st.count + 1 }
                  (r • gen, (readPair (readState st T).table mm).1 + r • pk)).1)
                (realRecord { readState st T with
                  cache := (readState st T).cache.cacheQuery (readPair (readState st T).table mm)
                    (r • gen, (readPair (readState st T).table mm).1 + r • pk)
                  count := st.count + 1 }
                  (r • gen, (readPair (readState st T).table mm).1 + r • pk)).2)
            congr 1
            funext r
            have he := fresh_record_read h (cipherResult_prefix T (translate z st mm).1 r)
              (translate z st mm) (cipherResult T (translate z st mm).1 r).1
              (translate_valid h.wf mm)
            have hm : lookup T () (translate z st mm).1 =
                (readPair (readState st T).table mm).1 := congrArg Prod.fst (translate_read h.wf mm)
            rw [cipherResult_read, h.generator, h.publicKey, hm, translate_read h.wf] at he
            erw [← he]
            exact ih _ _ _ (fresh_record_inv h (cipherResult_prefix T _ r) _ _
              (translate_valid h.wf mm) (cipherResult_valid T _ r))
          · simp only [hlt, show ¬(readState st T).count < k from hlt, ↓reduceIte]
            simp only [runGen, run, simulateQ_pure, StateT.run_pure, map_pure]
            change pure (RealPrefixResult.paused (readPair T (translate z st mm)) cont,
              readState st T) =
                pure (RealPrefixResult.paused (readPair (readState st T).table mm) cont,
                readState st T)
            rw [translate_read h.wf]
            rfl
        · simp only [Option.map_some]
          rw [← record_read st T c]
          obtain ⟨nn, hn⟩ := cacheLookup_mem T (translate z st mm) c st.cache hc
          exact ih _ _ _ (record_inv h c (h.cacheValid (nn, c) hn).2)

end Simulation

private def PrefixPost [Zero G] (gen pk : G) (z k : ℕ)
    (r : (PrefixResult F × SimState) × Tbl (fun _ : Unit => G)) : Prop :=
  SimInv gen pk z r.1.2 r.2 ∧ match r.1.1 with
    | .done _ => True
    | .paused mm _ => r.1.2.count = k ∧ ValidPair r.2 mm

private theorem prefix_post [Field F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq G]
    (gen pk : G) (z k : ℕ) (A : GenericAdversary F)
    (st : SimState) (T : Tbl (fun _ : Unit => G)) (h : SimInv gen pk z st T)
    (hk : st.count ≤ k) (r : (PrefixResult F × SimState) × Tbl (fun _ : Unit => G))
    (hr : r ∈ support (runGen (Model.group G) (fun _ => id) ((runPrefix z k A).run st) T)) :
    PrefixPost gen pk z k r := by
  induction A using OracleComp.inductionOn generalizing st T r with
  | pure b =>
      change r ∈ support (pure ((PrefixResult.done b, st), T) : ProbComp _) at hr
      rw [mem_support_pure_iff] at hr
      subst r
      exact ⟨h, trivial⟩
  | query_bind t cont ih =>
      simp only [runPrefix, construct_query_bind] at hr
      rcases t with t | (u | mm)
      · change r ∈ support (runGen (Model.group G) (fun _ => id)
          ((groupStep z t).run st >>= fun s => (runPrefix z k (cont s.1)).run s.2) T) at hr
        rw [runGen_bind, runGen_groupStep] at hr
        erw [pure_bind] at hr
        apply ih _ _ _ (groupResult_inv h t) _ r hr
        have he : (groupResult z t st T).1.2.count = st.count := by cases t <;> rfl
        rwa [he]
      · change r ∈ support (runGen (Model.group G) (fun _ => id)
          (liftM ((genSpec F groupSig).query (.inr u)) >>= fun v =>
            (runPrefix z k (cont v)).run st) T) at hr
        rw [runGen_bind] at hr
        change r ∈ support (((fun v => (v, T)) <$> liftM (unifSpec.query u)) >>=
          fun s => runGen (Model.group G) (fun _ => id) ((runPrefix z k (cont s.1)).run st) s.2)
          at hr
        erw [bind_map_left, mem_support_bind_iff] at hr
        obtain ⟨v, _, hr⟩ := hr
        exact ih v st T h hk r hr
      · change r ∈ support (runGen (Model.group G) (fun _ => id)
          (cacheFind F (translate z st mm) st.cache >>= _) T) at hr
        erw [runGen_bind, runGen_cacheFind, pure_bind] at hr
        rcases hc : cacheLookup T (translate z st mm) st.cache with _ | c
        · rw [hc] at hr
          dsimp only at hr
          by_cases hlt : st.count < k
          · simp only [hlt, ↓reduceIte] at hr
            erw [runGen_bind, runGen_encrypt T _ (translate_valid h.wf mm).1 h.keyLen,
              bind_map_left, mem_support_bind_iff] at hr
            obtain ⟨a, _, hr⟩ := hr
            exact ih _ _ _ (fresh_record_inv h (cipherResult_prefix T _ a) _ _
              (translate_valid h.wf mm) (cipherResult_valid T _ a))
              (by change st.count + 1 ≤ k; omega) r hr
          · simp only [hlt, ↓reduceIte] at hr
            change r ∈ support (pure ((PrefixResult.paused (translate z st mm) cont, st), T) :
              ProbComp _) at hr
            rw [mem_support_pure_iff] at hr
            subst r
            exact ⟨h, (by change st.count = k; omega), translate_valid h.wf mm⟩
        · rw [hc] at hr
          obtain ⟨nn, hn⟩ := cacheLookup_mem T (translate z st mm) c st.cache hc
          exact ih _ _ _ (record_inv h c (h.cacheValid (nn, c) hn).2) hk r hr

section GameEquality

variable [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]

/-- For each public key and fixed challenge bit, the generic one-time step produces exactly
that bit's adjacent counted hybrid: `k + 1` for the left branch, and `k` for the right branch. -/
theorem evalDist_step_branch (gen pk : G) (A : GenericAdversary F) (k : ℕ) (bit : Bool) :
    𝒟[do
      let out ← ((A.step k).toOneTime gen).chooseMessages pk
      let c ← (elGamalAsymmEnc F G gen).encrypt pk (if bit then out.1 else out.2.1)
      ((A.step k).toOneTime gen).distinguish out.2.2 c] =
    𝒟[(simulateQ ((elGamalAsymmEnc F G gen).IND_CPA_queryImpl_hybridLR_counted pk
      (if bit then k + 1 else k)) (A.toAdversary gen pk)).run' (∅, 0)] := by
  let st₀ : SimState := ⟨fun _ => [0, 1], [], 0⟩
  let T₀ : Tbl (fun _ : Unit => G) := fun _ => [gen, pk, 0]
  have hi : SimInv gen pk 2 st₀ T₀ := by
    constructor <;> simp [st₀, T₀, WellFormed, lookup, CacheValid]
  have hr : readState st₀ T₀ = RealState.mk (fun _ => [gen, pk]) ∅ 0 := by
    change RealState.mk (readBack (fun _ => [0, 1]) (fun _ => [gen, pk, 0])) ∅ 0 = _
    congr 1
  have hrun : realRun gen pk (if bit then k + 1 else k) A (readState st₀ T₀) =
      (simulateQ ((elGamalAsymmEnc F G gen).IND_CPA_queryImpl_hybridLR_counted pk
        (if bit then k + 1 else k)) (A.toAdversary gen pk)).run' (∅, 0) := by
    rw [hr, realRun_eq_counted]
    simp [toAdversary, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
  rw [← hrun, ← realPrefix_resume gen pk k bit A (readState st₀ T₀) (Nat.zero_le k),
    ← prefix_read gen pk 2 k A st₀ T₀ hi]
  simp only [GenericOneTimeAdversary.toOneTime, step, bind_map_left]
  erw [runGen_bind]
  change 𝒟[(pure (2, append (fun _ : Unit => [gen, pk]) ()
      ((0 : F) • lookup (fun _ => [gen, pk]) () 0)) >>= _) >>= _] = _
  have hz : append (fun _ : Unit => [gen, pk]) ()
      ((0 : F) • lookup (fun _ => [gen, pk]) () 0) = T₀ := by
    funext u
    cases u
    simp [T₀, append]
  rw [hz]
  erw [pure_bind, runGen_bind]
  simp only [bind_assoc]
  refine evalDist_bind_congr_of_support _ _ _ fun r hs => ?_
  have hp := prefix_post gen pk 2 k A st₀ T₀ hi (Nat.zero_le k) r hs
  rcases r with ⟨⟨res, st⟩, T⟩
  cases res with
  | done guess =>
      simp [runGen, run, realResume, readPrefix, elGamalAsymmEnc]
  | paused mm cont =>
      obtain ⟨h, hk, hm⟩ := hp
      change st.count = k at hk
      simp only [runGen, run, simulateQ_pure, StateT.run_pure, pure_bind,
        readPrefix, realResume]
      refine evalDist_bind_congr _ _ _ fun c => ?_
      let T' := append (append T () c.1) () c.2
      let cc : HandlePair := ((T ()).length, (T ()).length + 1)
      have ht : T () <+: T' () := (prefix_append T () () _).trans
        (prefix_append (append T () _) () () _)
      have hc : ValidPair T' cc := by simp [ValidPair, T', cc, append]
      have hv : readPair T' cc = c := by
        simp [readPair, T', cc, append, lookup, List.getD_eq_getElem?_getD]
      have he := fresh_record_read h ht mm cc hm
      rw [hv] at he
      have hi' := fresh_record_inv h ht mm cc hm hc
      simp only [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map]
      change 𝒟[(fun r => r.1.1) <$> runGen (Model.group G) (fun _ => id)
        ((simulateQ (suffixImpl 2) (cont (record
          { st with cache := (mm, cc) :: st.cache, count := st.count + 1 } cc).1)).run
            (record { st with cache := (mm, cc) :: st.cache, count := st.count + 1 } cc).2) T'] = _
      rw [suffix_read gen pk 2 _ _ _ hi']
      erw [← he]
      congr 1
      apply realRun_above
      · exact Nat.zero_le _
      · change k ≤ st.count + 1
        omega

/-- The one-time advantage of the generic step is exactly the distance between the two
adjacent hybrids of the induced multi-query adversary. -/
theorem oneTimeAdvantage_step_toOneTime_eq (gen : G) (A : GenericAdversary F) (k : ℕ) :
    AsymmEncAlg.IND_CPA_OneTime_Advantage (elGamalAsymmEnc F G gen)
      ProbCompRuntime.probComp ((A.step k).toOneTime gen) =
      𝒟[(elGamalAsymmEnc F G gen).IND_CPA_LR_hybrid (A.toAdversary gen) (k + 1)].boolDist
        𝒟[(elGamalAsymmEnc F G gen).IND_CPA_LR_hybrid (A.toAdversary gen) k] := by
  have hg : 𝒟[AsymmEncAlg.IND_CPA_OneTime_Game ((A.step k).toOneTime gen)
      ProbCompRuntime.probComp] =
      𝒟[do
        let bit ← ($ᵗ Bool)
        let b ← if bit then (elGamalAsymmEnc F G gen).IND_CPA_LR_hybrid (A.toAdversary gen) (k + 1)
          else (elGamalAsymmEnc F G gen).IND_CPA_LR_hybrid (A.toAdversary gen) k
        pure (bit == b)] := by
    change 𝒟[($ᵗ Bool) >>= fun bit => _] = _
    refine evalDist_bind_congr _ _ _ fun bit => ?_
    have hi : (do
        let b ← if bit then (elGamalAsymmEnc F G gen).IND_CPA_LR_hybrid (A.toAdversary gen) (k + 1)
          else (elGamalAsymmEnc F G gen).IND_CPA_LR_hybrid (A.toAdversary gen) k
        pure (bit == b)) = (do
        let b ← (elGamalAsymmEnc F G gen).IND_CPA_LR_hybrid (A.toAdversary gen)
          (if bit then k + 1 else k)
        pure (bit == b)) := by cases bit <;> rfl
    rw [hi]
    simp only [AsymmEncAlg.IND_CPA_LR_hybrid, bind_assoc]
    refine evalDist_bind_congr _ _ _ fun keys => ?_
    have he := ((EvalDistEq.of_evalDist_eq (evalDist_step_branch gen keys.1 A k bit)).map
      (bit == ·)).evalDist_eq
    simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc] using he
  rw [AsymmEncAlg.IND_CPA_OneTime_Advantage]
  change 𝒟[AsymmEncAlg.IND_CPA_OneTime_Game ((A.step k).toOneTime gen)
    ProbCompRuntime.probComp].boolBias = _
  rw [hg, evalDist_boolBias_bind_uniformBool]

end GameEquality

/-- The generic adapter satisfies the existing hybrid-sum bound whenever its handle-level
left/right calls satisfy the syntactic query budget. -/
theorem advantage_toAdversary_le_sum_hybrid [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
    (gen : G) (A : GenericAdversary F) (q : ℕ)
    (hq : IsQueryBoundP A (· matches .inr (.inr _)) q) :
    (elGamalAsymmEnc F G gen).IND_CPA_Advantage (A.toAdversary gen) ≤
      ∑ k ∈ Finset.range q,
        𝒟[(elGamalAsymmEnc F G gen).IND_CPA_LR_hybrid (A.toAdversary gen) (k + 1)].boolDist
          𝒟[(elGamalAsymmEnc F G gen).IND_CPA_LR_hybrid (A.toAdversary gen) k] := by
  let : Inhabited G := ⟨0⟩
  simpa only [AsymmEncAlg.IND_CPA_OneTime_Advantage_stepAdversary] using
    AsymmEncAlg.IND_CPA_Advantage_le_sum_oneTime_stepAdversary (A.toAdversary gen) q
      (makesAtMostQueries_toAdversary gen A q hq)

end GenericAdversary

/-- A generic adversary making at most `qₒ` group operations and `q` left/right calls has
unconditional multi-query IND-CPA advantage at most `q` times the generic one-time bound.
Each hybrid step uses at most `qₒ + 3 * q` operations in each phase: simulated encryptions
cost three operations. The two phases and seven setup entries give the collision-table size;
the factor three is the generic DDH collision bound, and the factor two converts DDH distance
to one-time IND-CPA advantage. -/
theorem IND_CPA_Advantage_toAdversary_le [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
    {gen : G} (hg : Function.Bijective (· • gen : F → G))
    (A : GenericAdversary F) (qₒ q : ℕ)
    (hₒ : IsQueryBoundP A (fun i => isGroupOp i = true) qₒ)
    (hq : IsQueryBoundP A (· matches .inr (.inr _)) q) :
    (elGamalAsymmEnc F G gen).IND_CPA_Advantage (A.toAdversary gen) ≤
      q * (2 * ((3 * (2 * (qₒ + 3 * q) + 7).choose 2 : ℕ) / (Fintype.card F : ℝ≥0∞))) := by
  refine (GenericAdversary.advantage_toAdversary_le_sum_hybrid gen A q hq).trans ?_
  calc
    _ ≤ ∑ _k ∈ Finset.range q,
        2 * ((3 * (2 * (qₒ + 3 * q) + 7).choose 2 : ℕ) / (Fintype.card F : ℝ≥0∞)) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← GenericAdversary.oneTimeAdvantage_step_toOneTime_eq]
      exact GenericAdversary.oneTimeAdvantage_step_toOneTime_le hg A qₒ q k hₒ hq
        (Finset.mem_range.mp hk)
    _ = _ := by simp

end elGamalAsymmEnc
