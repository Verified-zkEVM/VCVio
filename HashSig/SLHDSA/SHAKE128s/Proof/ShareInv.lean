/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ShareCouple

/-!
# What the lenient game keeps true

The coupling with the real game carries the real cache and log; the event the shared half pays
for also needs facts the lenient game keeps on its own. They are invariants of its run at the
adversary's oracles and at the verifier's:

* **the flag is closed under the record**: a guess filed raises the flag;
* **the signer is covered**: every framed request in the log has its `PRF_msg` answer in the
  frame table and its digest input filed;
* **served digests are traceable**: each comes with its log entry, its randomiser and its entry
  in the real cache;
* **the plain cache holds no table entry and no `PRF_msg` input at the real seed**;
* **snapshots are prefixes** of the served digests.

This part: what a routed query leaves of the state.
-/

public section

open OracleComp OracleSpec ENNReal

namespace SLHDSA.SHAKE128s.ShareInv

open Security CanonicalGraph ShareGame ShareCouple

/-! ## A routed query only adds -/

/-- **One state extends another**: the frame table and the plain cache only gain entries, and
nothing else of the state moves. -/
structure Extends (old new : St) : Prop where
  /-- Every frame-table entry of the old state is kept in the new one. -/
  prfs : ∀ frame value, old.prfs frame = some value → new.prfs frame = some value
  /-- Every plain-cache entry of the old state is kept in the new one. -/
  cache : ∀ input value, old.cache input = some value → new.cache input = some value

theorem Extends.refl (state : St) : Extends state state := ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem Extends.trans {first second third : St} (h1 : Extends first second)
    (h2 : Extends second third) : Extends first third :=
  ⟨fun f v h => h2.prfs f v (h1.prfs f v h), fun x v h => h2.cache x v (h1.cache x v h)⟩

theorem Extends.realView {setup : Setup} {old new : St} (h : Extends old new) (input : Bytes)
    (value : HashOutput) (hold : realView setup old input = some value) :
    realView setup new input = some value := by
  classical
  cases hw : setup.warm input with
  | some a =>
    rw [realView_of_warm setup _ input a hw] at hold ⊢
    exact hold
  | none =>
    rw [realView_of_not_warm setup _ input hw, merged, QueryCache.ofFn_apply] at hold ⊢
    split_ifs at hold ⊢
    · exact h.prfs _ _ hold
    · exact h.cache _ _ hold

open scoped Classical in
/-- **What one lenient routed query does**: the state extends, the bookkeeping stays, the answer
is the real cache's at the input, and the plain cache gains only inputs off the table and off the
`PRF_msg` class. -/
theorem route_spec (setup : Setup) (state : St) (input : Bytes) (z : HashOutput × St)
    (hz : z ∈ support (route true setup state input)) :
    Extends state z.2 ∧ Quiet state z.2 ∧ realView setup z.2 input = some z.1 ∧
      (∀ other value, z.2.cache other = some value → state.cache other = some value ∨
        (other = input ∧ setup.warm input = none ∧ ¬ IsPrfInput setup input)) := by
  classical
  unfold route at hz
  cases hwarm : setup.warm input with
  | some answer =>
    simp only [ite_true, hwarm, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨Extends.refl _, ⟨rfl, rfl, rfl⟩, realView_of_warm setup _ input answer hwarm,
      fun _ _ h => Or.inl h⟩
  | none =>
    simp only [ite_true, hwarm, true_and] at hz
    by_cases hprf : IsPrfInput setup input
    · rw [ite_eq_left hprf] at hz
      unfold prfAt at hz
      cases hcached : state.prfs (prfFrame input) with
      | some answer =>
        simp only [hcached, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        refine ⟨Extends.refl _, ⟨rfl, rfl, rfl⟩, ?_, fun _ _ h => Or.inl h⟩
        rw [realView_of_not_warm setup _ input hwarm, merged, QueryCache.ofFn_apply,
          ite_eq_left hprf, hcached]
      | none =>
        simp only [hcached, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨value, -, rfl⟩ := hz
        refine ⟨⟨fun f v h => ?_, fun _ _ h => h⟩, ⟨rfl, rfl, rfl⟩, ?_, fun _ _ h => Or.inl h⟩
        · by_cases hf : f = prfFrame input
          · subst hf; rw [hcached] at h; cases h
          · simpa [Function.update_of_ne hf] using h
        · rw [realView_of_not_warm setup _ input hwarm, merged, QueryCache.ofFn_apply,
            ite_eq_left hprf]
          simp
    · rw [ite_eq_right hprf] at hz
      unfold plain at hz
      cases hcached : state.cache input with
      | some answer =>
        simp only [hcached, support_pure, Set.mem_singleton_iff] at hz
        subst hz
        refine ⟨Extends.refl _, ⟨rfl, rfl, rfl⟩, ?_, fun _ _ h => Or.inl h⟩
        rw [realView_of_not_warm setup _ input hwarm, merged, QueryCache.ofFn_apply,
          ite_eq_right hprf, hcached]
      | none =>
        simp only [hcached, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨value, -, rfl⟩ := hz
        refine ⟨⟨fun _ _ h => h, fun x v h => ?_⟩, ⟨rfl, rfl, rfl⟩, ?_, fun other v h => ?_⟩
        · by_cases hx : x = input
          · subst hx; rw [hcached] at h; cases h
          · simpa [QueryCache.cacheQuery_of_ne _ _ hx] using h
        · rw [realView_of_not_warm setup _ input hwarm, merged, QueryCache.ofFn_apply,
            ite_eq_right hprf]
          simp [QueryCache.cacheQuery_self]
        · by_cases hx : other = input
          · exact Or.inr ⟨hx, rfl, hprf⟩
          · left
            simpa [QueryCache.cacheQuery_of_ne _ _ hx] using h

/-! ## The invariant -/

/-- **What the lenient game keeps true.** -/
structure Inv (setup : Setup) (p : St × Bool) : Prop where
  /-- A recorded guess has raised the flag. -/
  closed : ∀ entry ∈ p.1.record, Guess setup entry.2 entry.1 → p.2 = true
  /-- Every framed request in the log has its `PRF_msg` answer in the frame table and its
  digest input filed in the record. -/
  signer : ∀ entry ∈ p.1.log, ∀ framed, entry.1.frame = some framed →
    ∃ value, p.1.prfs framed = some value ∧
      ∃ filed ∈ p.1.record,
        filed.1 = Hashing.messageInput (Hashing.truncate value) setup.pk framed
  /-- Every served digest comes with its log entry, its randomiser and its entry in the real
  view of the state. -/
  served : ∀ digest ∈ p.1.served, ∃ entry ∈ p.1.log, ∃ framed, entry.1.frame = some framed ∧
    ∃ value, p.1.prfs framed = some value ∧
      entry.2 = some (ShareSigner.cellSig setup.warm setup.sk (Hashing.truncate value)
        digest).toBytes ∧
      realView setup p.1 (Hashing.messageInput (Hashing.truncate value) setup.pk framed) =
        some digest
  /-- The plain cache holds no input of the warm table and no `PRF_msg` input at the real
  seed. -/
  cacheOff : ∀ input value, p.1.cache input = some value →
    setup.warm input = none ∧ ¬ IsPrfInput setup input
  /-- The digests snapshotted with each record entry are a prefix of the served digests. -/
  snapshot : ∀ entry ∈ p.1.record, entry.2 <+: p.1.served

theorem inv_start (setup : Setup) : Inv setup (St.start, false) where
  closed := by simp [St.start]
  signer := by simp [St.start]
  served := by simp [St.start]
  cacheOff := by simp [St.start]
  snapshot := by simp [St.start]

/-- The invariant survives a step that only extends the caches, keeps the bookkeeping, files
some entries at the current digests, and raises the flag on a guess among them. -/
theorem inv_of_quietStep (setup : Setup) (p : St × Bool) (hinv : Inv setup p) (next : St)
    (flag : Bool) (hext : Extends p.1 next) (hserved : next.served = p.1.served)
    (hlog : next.log = p.1.log) (inputs : List Bytes)
    (hrecord : next.record = p.1.record ++ inputs.map fun input => (input, p.1.served))
    (hflag : p.2 = true → flag = true)
    (hguess : ∀ input ∈ inputs, Guess setup p.1.served input → flag = true)
    (hcache : ∀ input value, next.cache input = some value → p.1.cache input = some value ∨
      (setup.warm input = none ∧ ¬ IsPrfInput setup input)) :
    Inv setup (next, flag) where
  closed := by
    intro entry hentry hguessEntry
    rw [hrecord] at hentry
    rcases List.mem_append.mp hentry with hold | hnew
    · exact hflag (hinv.closed entry hold hguessEntry)
    · obtain ⟨input, hinput, rfl⟩ := List.mem_map.mp hnew
      exact hguess input hinput hguessEntry
  signer := by
    intro entry hentry framed hframe
    rw [hlog] at hentry
    obtain ⟨value, hvalue, filed, hfiled, hfiledEq⟩ := hinv.signer entry hentry framed hframe
    exact ⟨value, hext.prfs _ _ hvalue, filed, by rw [hrecord]; exact List.mem_append_left _ hfiled,
      hfiledEq⟩
  served := by
    intro digest hdigest
    rw [hserved] at hdigest
    obtain ⟨entry, hentry, framed, hframe, value, hvalue, hbytes, hview⟩ :=
      hinv.served digest hdigest
    exact ⟨entry, by rw [hlog]; exact hentry, framed, hframe, value, hext.prfs _ _ hvalue, hbytes,
      hext.realView _ _ hview⟩
  cacheOff := by
    intro input value hvalue
    rcases hcache input value hvalue with hold | hnew
    · exact hinv.cacheOff input value hold
    · exact hnew
  snapshot := by
    intro entry hentry
    rw [hrecord] at hentry
    rw [hserved]
    rcases List.mem_append.mp hentry with hold | hnew
    · exact hinv.snapshot entry hold
    · obtain ⟨input, -, rfl⟩ := List.mem_map.mp hnew
      exact List.prefix_refl _

open scoped Classical in
/-- **A world query keeps the invariant.** -/
theorem inv_world (setup : Setup) (queried : ShareSpec.Domain)
    (hworld : ∃ world, queried = Sum.inl (Sum.inl (Sum.inl world))) (p : St × Bool)
    (hinv : Inv setup p) (z : ShareSpec.Range queried × (St × Bool))
    (hz : z ∈ support (((handler true setup) queried).run p)) : Inv setup z.2 := by
  classical
  obtain ⟨state, flag⟩ := p
  obtain ⟨world, rfl⟩ := hworld
  rcases world with coin | input
  · simp only [handler, StateT.run, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨value, -, rfl⟩ := hz
    exact hinv
  · simp only [handler, StateT.run, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨step, hstep, rfl⟩ := hz
    obtain ⟨hext, ⟨hserved, hrecord, hlog⟩, -, hcache⟩ := route_spec setup state input step hstep
    refine inv_of_quietStep setup (state, flag) hinv _ _ ⟨hext.prfs, hext.cache⟩ hserved hlog
      [input] (by simp) (fun h => by simp only at h; simp [h]) (fun x hx hguess => ?_)
      (fun x v hx => ?_)
    · rw [List.mem_singleton] at hx
      subst hx
      simp [hguess]
    · rcases hcache x v hx with hold | ⟨rfl, hw, hp⟩
      · exact Or.inl hold
      · exact Or.inr ⟨hw, hp⟩

/-- The signer's `PRF_msg` answer, once in the real view, is in the frame table. -/
theorem prfs_of_realView (setup : Setup) (hgood : setup.Good) (state : St) (framed : Bytes)
    (value : HashOutput)
    (hview : realView setup state (Hashing.randomizerInput setup.prf setup.publicSeed framed) =
      some value) : state.prfs framed = some value := by
  classical
  rw [realView_of_not_warm setup state _ (warm_randomizerInput setup hgood framed), merged,
    QueryCache.ofFn_apply, ite_eq_left (isPrfInput_randomizerInput setup framed),
    prfFrame_randomizerInput] at hview
  exact hview

open scoped Classical in
/-- **A framed signing request keeps the invariant.** -/
theorem inv_sign_framed (setup : Setup) (hgood : setup.Good) (request : Message) (framed : Bytes)
    (hframe : request.frame = some framed) (p : St × Bool) (hinv : Inv setup p)
    (z : Option Bytes × (St × Bool))
    (hz : z ∈ support (((ShareFlag.advImpl true setup) (Sum.inr request)).run p)) :
    Inv setup z.2 := by
  classical
  obtain ⟨state, flag⟩ := p
  have hz' : z ∈ support (route true setup state
      (Hashing.randomizerInput setup.prf setup.publicSeed framed) >>= fun seed =>
        route true setup seed.2
            (Hashing.messageInput (Hashing.truncate seed.1) setup.pk framed) >>= fun digest =>
          (pure (some (ShareSigner.cellSig setup.warm setup.sk (Hashing.truncate seed.1)
              digest.1).toBytes,
            ({ digest.2 with
                served := digest.2.served ++ [digest.1]
                record := state.record ++
                  [(Hashing.messageInput (Hashing.truncate seed.1) setup.pk framed, state.served)]
                log := digest.2.log ++ [⟨request, some (ShareSigner.cellSig setup.warm setup.sk
                  (Hashing.truncate seed.1) digest.1).toBytes⟩] },
              flag || decide (¬ setup.Good ∨ Guess setup state.served
                (Hashing.messageInput (Hashing.truncate seed.1) setup.pk framed)))) :
            ProbComp (Option Bytes × (St × Bool)))) := by
    have h := hz
    rw [advImpl_sign_framed_run setup hgood request framed hframe state flag] at h
    exact h
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz'
  obtain ⟨seed, hseed, digest, hdigest, rfl⟩ := hz'
  obtain ⟨hext1, ⟨hserved1, hrecord1, hlog1⟩, hview1, hcache1⟩ :=
    route_spec setup state _ seed hseed
  obtain ⟨hext2, ⟨hserved2, hrecord2, hlog2⟩, hview2, hcache2⟩ :=
    route_spec setup seed.2 _ digest hdigest
  have hprfs : digest.2.prfs framed = some seed.1 :=
    hext2.prfs _ _ (prfs_of_realView setup hgood seed.2 framed seed.1 hview1)
  have hext := hext1.trans hext2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro entry hentry hguess
    simp only at hentry ⊢
    rcases List.mem_append.mp hentry with hold | hnew
    · have hflag : flag = true := hinv.closed entry hold hguess
      simp [hflag]
    · rw [List.mem_singleton] at hnew
      subst hnew
      simp [hguess]
  · intro entry hentry framed' hframe'
    simp only at hentry ⊢
    rcases List.mem_append.mp hentry with hold | hnew
    · rw [hlog2, hlog1] at hold
      obtain ⟨value, hvalue, filed, hfiled, hfiledEq⟩ := hinv.signer entry hold framed' hframe'
      exact ⟨value, hext.prfs _ _ hvalue, filed, List.mem_append_left _ hfiled, hfiledEq⟩
    · rw [List.mem_singleton] at hnew
      subst hnew
      simp only at hframe'
      rw [hframe] at hframe'
      cases hframe'
      exact ⟨seed.1, hprfs, _, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
  · intro d hd
    simp only at hd ⊢
    rcases List.mem_append.mp hd with hold | hnew
    · rw [hserved2, hserved1] at hold
      obtain ⟨entry, hentry, framed', hframe', value, hvalue, hbytes, hview⟩ :=
        hinv.served d hold
      refine ⟨entry, List.mem_append_left _ (by rw [hlog2, hlog1]; exact hentry), framed', hframe',
        value, hext.prfs _ _ hvalue, hbytes, ?_⟩
      exact hext.realView _ _ hview
    · rw [List.mem_singleton] at hnew
      subst hnew
      exact ⟨⟨request, _⟩, List.mem_append_right _ (List.mem_singleton_self _), framed, hframe,
        seed.1, hprfs, rfl, hview2⟩
  · intro input value hvalue
    simp only at hvalue
    rcases hcache2 input value hvalue with hold | ⟨rfl, hw, hp⟩
    · rcases hcache1 input value hold with hold' | ⟨rfl, hw, hp⟩
      · exact hinv.cacheOff input value hold'
      · exact ⟨hw, hp⟩
    · exact ⟨hw, hp⟩
  · intro entry hentry
    simp only at hentry ⊢
    rw [hserved2, hserved1]
    rcases List.mem_append.mp hentry with hold | hnew
    · exact (hinv.snapshot entry hold).trans (List.prefix_append _ _)
    · rw [List.mem_singleton] at hnew
      subst hnew
      exact List.prefix_append _ _

/-- **An unframed signing request keeps the invariant.** -/
theorem inv_sign_unframed (setup : Setup) (request : Message)
    (hframe : request.frame = none) (p : St × Bool) (hinv : Inv setup p)
    (z : Option Bytes × (St × Bool))
    (hz : z ∈ support (((ShareFlag.advImpl true setup) (Sum.inr request)).run p)) :
    Inv setup z.2 := by
  classical
  obtain ⟨state, flag⟩ := p
  have hz' : z ∈ support ((pure (none,
      ({ state with log := state.log ++ [⟨request, none⟩] }, flag)) :
      ProbComp (Option Bytes × (St × Bool)))) := by
    have h := hz
    rw [advImpl_sign_run] at h
    simp only [handler, StateT.run, hframe, pure_bind] at h
    exact h
  rw [support_pure, Set.mem_singleton_iff] at hz'
  subst hz'
  refine ⟨hinv.closed, ?_, ?_, hinv.cacheOff, hinv.snapshot⟩
  · intro entry hentry framed hframe'
    rcases List.mem_append.mp hentry with hold | hnew
    · exact hinv.signer entry hold framed hframe'
    · rw [List.mem_singleton] at hnew
      subst hnew
      simp only at hframe'
      rw [hframe] at hframe'
      cases hframe'
  · intro d hd
    obtain ⟨entry, hentry, framed, hframe', value, hvalue, hbytes, hview⟩ := hinv.served d hd
    exact ⟨entry, List.mem_append_left _ hentry, framed, hframe', value, hvalue, hbytes, hview⟩

/-- **Every adversary step keeps the invariant**, on a good walk. -/
theorem inv_adv (setup : Setup) (hgood : setup.Good) (queried : (OracleWorld + SigningSpec).Domain)
    (p : St × Bool) (hinv : Inv setup p)
    (z : (OracleWorld + SigningSpec).Range queried × (St × Bool))
    (hz : z ∈ support (((ShareFlag.advImpl true setup) queried).run p)) : Inv setup z.2 := by
  rcases queried with world | request
  · have h := hz
    rw [advImpl_world_run] at h
    exact inv_world setup (worldQuery world) ⟨world, rfl⟩ p hinv z h
  · cases hframe : request.frame with
    | none => exact inv_sign_unframed setup request hframe p hinv z hz
    | some framed => exact inv_sign_framed setup hgood request framed hframe p hinv z hz

/-- **Every verifier step keeps the invariant.** -/
theorem inv_verify (setup : Setup) (queried : OracleWorld.Domain) (p : St × Bool)
    (hinv : Inv setup p) (z : OracleWorld.Range queried × (St × Bool))
    (hz : z ∈ support (((ShareBound.worldImpl true setup) queried).run p)) : Inv setup z.2 := by
  have h := hz
  rw [worldImpl_run] at h
  exact inv_world setup (worldQuery queried) ⟨queried, rfl⟩ p hinv z h

end SLHDSA.SHAKE128s.ShareInv
