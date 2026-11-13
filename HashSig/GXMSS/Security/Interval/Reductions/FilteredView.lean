/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import HashSig.GXMSS.Security.Interval.Reductions.SplicedView
import all HashSig.GXMSS.Security.Interval.Reductions.SplicedView
import HashSig.GXMSS.Security.Auxiliary.ChainSelection
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.OracleComp.EvalDist.Sum

/-!
# Absorbing filters for adaptive interval splices

The option-state observation distinguishes a killed run from every returned first-request history.
Only good returned outputs are compared; no bad-output or missing-mass equality is asserted.
-/

public section
namespace GXMSS.Reductions
open IncomparableEncoding ENNReal OracleComp OracleSpec SyncSignatureUnforgeability
variable {PP T X H M R : Type} {h w v : ℕ}

/-- The common callback handler has the original first-request operational equation. -/
private theorem contextSplicedSigningOracle_apply [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v) (pp : PP)
    (guess : Guess h w v) (answer : H) (starts endpoints : Epoch h → Fin v → H)
    (q : Epoch h × M) (history : History (Epoch h) M (GXMSS.Signature R H h v)) :
    contextSplicedSigningOracle hash enc K ctx pp guess answer starts endpoints q history =
      match history q.1 with
      | some _ => pure (none, history)
      | none =>
        if ctx.activity q.1 then do
          let wr ← enc.retry ($ᵗ R) pp q.2 q.1 K
          let signature := wr.map
            (contextSplicedSignatureOfWord hash ctx pp guess answer starts endpoints q.1)
          pure (signature, Function.update history q.1 (some (q.2, signature)))
        else pure (none, Function.update history q.1 (some (q.2, none))) := by
  cases hused : history q.1 with
  | none =>
    cases hactive : ctx.activity q.1 <;>
      simp [contextSplicedSigningOracle, signingKernelOracle, contextSplicedSign,
        record, hused, hactive, map_eq_bind_pure_comp, bind_assoc]
  | some entry => simp [contextSplicedSigningOracle, signingKernelOracle, hused]

/-- Whether the retained first request at the selected epoch has a successful word below the
selected forged cut. The history remembers enough to decide this even after later queries. -/
private def badSelectedHistory
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (pp : PP)
    (selector : Guess h w v)
    (history : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v)) : Bool :=
  match history (guessedEpoch selector) with
  | some (msg, some sig) =>
    match enc.value pp msg sig.randomizer (guessedEpoch selector) with
    | some word => decide ((word (guessedChain selector)).val <
        (guessedPosition selector).val + 1)
    | none => false
  | _ => false

private def selectedHistoryProjection
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (pp : PP)
    (selector : Guess h w v)
    (history : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v)) :
    Option (SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v)) :=
  if badSelectedHistory enc pp selector history then none else some history

/-- State projection through an absorbing filter preserves each good returned output, even when
bad paths later lose mass. This deliberately asserts no equality for bad or missing outputs. -/
private theorem goodOutput_simulateQ_eq_filtered
    {ι : Type} {spec : OracleSpec ι} {σ α : Type}
    [MeasurableSpace σ] [MeasurableSpace α]
    [MeasurableSingletonClass σ] [MeasurableSingletonClass α]
    (original : QueryImpl spec (StateT σ ProbComp))
    (filtered : QueryImpl spec (StateT (Option σ) ProbComp))
    (bad : σ → Bool)
    (transform : (t : spec.Domain) → spec.Range t × σ → spec.Range t)
    (htransform : ∀ t u s', bad s' = false → transform t (u, s') = u)
    (hmono : ∀ t s, bad s = true →
      ∀ z ∈ support ((original t).run s), bad z.2 = true)
    (habsorb : ∀ t, ∀ z ∈ support ((filtered t).run none), z.2 = none)
    (hstep : ∀ t s, bad s = false →
      (fun z => (transform t z, if bad z.2 then none else some z.2)) <$>
        (original t).run s = (filtered t).run (some s))
    (oa : OracleComp spec α) (s₀ : σ) (a : α) (s : σ)
    (hgood : bad s = false) :
    𝒟[(simulateQ original oa).run s₀] {(a, s)} =
      𝒟[(simulateQ filtered oa).run
        (if bad s₀ then none else some s₀)] {(a, some s)} := by
  classical
  simp only [← prEvent_eq_evalDist_singleton]
  have zeroOriginal (program : OracleComp spec α) (start : σ)
      (hbad : bad start = true) :
      𝒟[(simulateQ original program).run start] {(a, s)} = 0 := by
    rw [← prEvent_eq_evalDist_singleton]
    apply (OracleComp.prEvent_eq_zero_iff _ _).2
    intro z hz heq
    have hpres := OracleComp.simulateQ_run_preserves_inv_of_query
      original (fun x => bad x = true) hmono program start hbad z hz
    subst z
    exact Bool.false_ne_true (hgood.symm.trans hpres)
  have zeroFiltered (program : OracleComp spec α) :
      𝒟[(simulateQ filtered program).run none] {(a, some s)} = 0 := by
    rw [← prEvent_eq_evalDist_singleton]
    apply (OracleComp.prEvent_eq_zero_iff _ _).2
    intro z hz heq
    have hpres := OracleComp.simulateQ_run_preserves_inv_of_query
      filtered (fun x => x = none) (by
        intro t state hs z hz
        subst state
        exact habsorb t z hz) program none rfl z hz
    subst z
    cases hpres
  induction oa using OracleComp.inductionOn generalizing s₀ with
  | pure x =>
    by_cases hbad : bad s₀ = true
    · have hsneq : s ≠ s₀ := by
        intro he
        subst s₀
        exact Bool.false_ne_true (hgood.symm.trans hbad)
      simpa [hbad, simulateQ_pure] using
        (fun (_ : x = a) (he : s₀ = s) => hsneq he.symm)
    · have hgood₀ : bad s₀ = false := by cases h : bad s₀ <;> simp_all
      simp [hgood₀]
  | query_bind t cont ih =>
    by_cases hbad : bad s₀ = true
    · simpa only [hbad, ite_true, ← prEvent_eq_evalDist_singleton, simulateQ_bind,
        simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, StateT.run_bind] using
        (zeroOriginal ((liftM (OracleSpec.query t) :
          OracleComp spec (spec.Range t)) >>= cont) s₀ hbad).trans
          (zeroFiltered ((liftM (OracleSpec.query t) :
            OracleComp spec (spec.Range t)) >>= cont)).symm
    · have hgood₀ : bad s₀ = false := by cases h : bad s₀ <;> simp_all
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, id_map, StateT.run_bind]
      simp only [hgood₀, Bool.false_eq_true, ite_false]
      rw [← hstep t s₀ hgood₀, bind_map_left]
      rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
      exact tsum_congr fun ⟨u, s'⟩ => by
        congr 1
        by_cases hbad' : bad s' = true
        · simp only [hbad', ite_true]
          simpa only [← prEvent_eq_evalDist_singleton] using
            (zeroOriginal (cont u) s' hbad').trans
              (zeroFiltered (cont (transform t (u, s')))).symm
        · have hgood' : bad s' = false := by cases h : bad s' <;> simp_all
          simpa [hgood', htransform t u s' hgood'] using ih u s'

/-- Kill a transcript as soon as a successful selected-epoch signing word lies before the
designated forged cut. Such a transcript cannot satisfy the enlarged selected event. The kill
state is absorbing, so the filtered interpreter retains exact returned winning mass. -/
private def contextFilteredSplicedSigningOracle [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v) (pp : PP)
    (selector splice : Guess h w v) (answer : H) (starts : Epoch h → Fin v → H)
    (endpoints : Epoch h → Fin v → H) :
    QueryImpl (SyncSignatureUnforgeability.signingSpec (Epoch h) M
      (GXMSS.Signature R H h v))
      (StateT (Option (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v))) ProbComp) := fun q state =>
  match state with
  | none => pure (none, none)
  | some history =>
    match history q.1 with
    | some _ => pure (none, some history)
    | none =>
      if ctx.activity q.1 then do
        let wr ← enc.retry ($ᵗ R) pp q.2 q.1 K
        match wr with
        | none => pure (none, some (Function.update history q.1 (some (q.2, none))))
        | some value =>
          if q.1 = guessedEpoch selector ∧
              (value.1 (guessedChain selector)).val < (guessedPosition selector).val + 1 then
            pure (none, none)
          else
            let signature := contextSplicedSignatureOfWord hash ctx pp splice answer starts
              endpoints q.1 value
            pure (some signature, some (Function.update history q.1
              (some (q.2, some signature))))
      else pure (none, some (Function.update history q.1 (some (q.2, none))))

private theorem contextFilteredSplicedSigningOracle_advance
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v) (pp : PP)
    (selector guess₁ guess₂ : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H)
    (hepoch : guessedEpoch guess₁ = guessedEpoch guess₂)
    (hchain : guessedChain guess₁ = guessedChain guess₂)
    (hnext : (guessedPosition guess₂).val = (guessedPosition guess₁).val + 1)
    (hselectEpoch : guessedEpoch selector = guessedEpoch guess₁)
    (hselectChain : guessedChain selector = guessedChain guess₁)
    (hselectPosition : (guessedPosition guess₂).val ≤ (guessedPosition selector).val) :
    contextFilteredSplicedSigningOracle hash enc K ctx pp selector guess₁ answer starts
      (splicedEndpoints hash pp guess₁ answer starts) =
    contextFilteredSplicedSigningOracle hash enc K ctx pp selector guess₂
      (hash.chain pp (guessedEpoch guess₁) (guessedChain guess₁)
        ((guessedPosition guess₁).val + 1) 1 answer) starts
      (splicedEndpoints hash pp guess₂
        (hash.chain pp (guessedEpoch guess₁) (guessedChain guess₁)
          ((guessedPosition guess₁).val + 1) 1 answer) starts) := by
  have hend := splicedEndpoints_advance hash pp guess₁ guess₂ answer starts
    hepoch hchain hnext
  rw [← hend]
  funext q state
  cases state with
  | none => rfl
  | some history =>
    rcases q with ⟨ep, msg⟩
    by_cases hused : history ep = none
    · by_cases hactive : ctx.activity ep = true
      · simp only [contextFilteredSplicedSigningOracle, hused, hactive, ↓reduceIte]
        apply bind_congr
        intro wr
        cases wr with
        | none => rfl
        | some value =>
          by_cases hbad : ep = guessedEpoch selector ∧
              (value.1 (guessedChain selector)).val < (guessedPosition selector).val + 1
          · simp [hbad]
          · have hword : ep = guessedEpoch guess₁ →
                (guessedPosition guess₂).val + 1 ≤
                  (value.1 (guessedChain guess₁)).val := by
              intro hep
              have hepsel : ep = guessedEpoch selector := by
                simpa only [hselectEpoch] using hep
              have hnot : ¬(value.1 (guessedChain selector)).val <
                  (guessedPosition selector).val + 1 := by
                intro hlt
                exact hbad ⟨hepsel, hlt⟩
              simpa only [hselectChain] using
                (show (guessedPosition guess₂).val + 1 ≤
                  (value.1 (guessedChain selector)).val by omega)
            have hsig := contextSplicedSignatureOfWord_advance hash ctx pp guess₁ guess₂ answer
              starts ep value hepoch hchain hnext hword
            have hsig' := hsig
            rw [← hend] at hsig'
            simp [hsig']
      · simp [contextFilteredSplicedSigningOracle, hused, hactive]
    · cases hrecord : history ep with
      | none => exact False.elim (hused hrecord)
      | some record =>
        simp [contextFilteredSplicedSigningOracle, hrecord]

/-- A selected bad first request is retained because a consumed epoch is never overwritten. -/
private theorem badSelectedHistory_contextSplicedSigningOracle_mono
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v) (pp : PP)
    (selector splice : Guess h w v) (answer : H) (starts : Epoch h → Fin v → H)
    (endpoints : Epoch h → Fin v → H)
    (q : Epoch h × M)
    (history : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v))
    (hbad : badSelectedHistory enc pp selector history = true)
    (z : Option (GXMSS.Signature R H h v) ×
      SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v))
    (hz : z ∈ support ((contextSplicedSigningOracle hash enc K ctx pp splice answer starts
      endpoints q).run history)) :
    badSelectedHistory enc pp selector z.2 = true := by
  classical
  rcases q with ⟨ep, msg⟩
  change z ∈ support (contextSplicedSigningOracle hash enc K ctx pp splice answer starts
    endpoints (ep, msg) history) at hz
  have hselected : history (guessedEpoch selector) ≠ none := by
    intro hn
    simp [badSelectedHistory, hn] at hbad
  by_cases hused : history ep = none
  · have heq : ep ≠ guessedEpoch selector := by
      intro he
      exact hselected (he ▸ hused)
    by_cases hactive : ctx.activity ep = true
    · simp only [contextSplicedSigningOracle_apply,
        hused, hactive, ↓reduceIte, mem_support_bind_iff] at hz
      obtain ⟨wr, _, hz⟩ := hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst z
      have heq' : guessedEpoch selector ≠ ep := Ne.symm heq
      simpa [badSelectedHistory, Function.update, heq'] using hbad
    · simp [contextSplicedSigningOracle_apply, hused, hactive] at hz
      subst z
      have heq' : guessedEpoch selector ≠ ep := Ne.symm heq
      simpa [badSelectedHistory, Function.update, heq'] using hbad
  · cases hrecord : history ep with
    | none => exact False.elim (hused hrecord)
    | some record =>
      simp only [contextSplicedSigningOracle_apply, hrecord, support_pure,
        Set.mem_singleton_iff] at hz
      subst z
      exact hbad

private theorem selectedHistoryProjection_contextSpliced_step_good
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v) (pp : PP)
    (selector splice : Guess h w v) (answer : H) (starts : Epoch h → Fin v → H)
    (endpoints : Epoch h → Fin v → H)
    (q : Epoch h × M)
    (history : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v))
    (hgood : badSelectedHistory enc pp selector history = false) :
    (fun z => (if badSelectedHistory enc pp selector z.2 then none else z.1,
      selectedHistoryProjection enc pp selector z.2)) <$>
      (contextSplicedSigningOracle hash enc K ctx pp splice answer starts endpoints q).run history =
    (contextFilteredSplicedSigningOracle hash enc K ctx pp selector splice answer starts
      endpoints q).run (some history) := by
  classical
  rcases q with ⟨ep, msg⟩
  change (fun z => (if badSelectedHistory enc pp selector z.2 then none else z.1,
      selectedHistoryProjection enc pp selector z.2)) <$>
      contextSplicedSigningOracle hash enc K ctx pp splice answer starts endpoints
        (ep, msg) history =
    contextFilteredSplicedSigningOracle hash enc K ctx pp selector splice answer starts
      endpoints (ep, msg) (some history)
  by_cases hused : history ep = none
  · by_cases hactive : ctx.activity ep = true
    · simp only [contextSplicedSigningOracle_apply, contextFilteredSplicedSigningOracle,
        hused, hactive, ↓reduceIte,
        map_bind]
      apply bind_congr_of_forall_mem_support
      intro wr hwr
      cases wr with
      | none =>
        have hnew : badSelectedHistory enc pp selector
            (Function.update history ep (some (msg, none))) = false := by
          by_cases heq : ep = guessedEpoch selector
          · subst ep; simp [badSelectedHistory, Function.update]
          · have heq' : guessedEpoch selector ≠ ep := Ne.symm heq
            simpa [badSelectedHistory, Function.update, heq'] using hgood
        simp [selectedHistoryProjection, hnew]
      | some value =>
        have hvalue : enc.value pp msg value.2 ep = some value.1 :=
          IncomparableEncoding.Retry.value_eq_some_of_mem_retry enc
            ($ᵗ R) pp msg ep K value.1 value.2 hwr
        by_cases hkill : ep = guessedEpoch selector ∧
            (value.1 (guessedChain selector)).val <
              (guessedPosition selector).val + 1
        · have hnew : badSelectedHistory enc pp selector
              (Function.update history ep (some (msg, some
                (contextSplicedSignatureOfWord hash ctx pp splice answer starts
                  endpoints ep value)))) =
                true := by
            rcases hkill with ⟨rfl, hlt⟩
            simp [badSelectedHistory, Function.update,
              contextSplicedSignatureOfWord, hvalue, hlt]
          rcases hkill with ⟨rfl, hlt⟩
          simp [selectedHistoryProjection, hnew, hlt]
        · have hnew : badSelectedHistory enc pp selector
              (Function.update history ep (some (msg, some
                (contextSplicedSignatureOfWord hash ctx pp splice answer starts
                  endpoints ep value)))) =
                false := by
            by_cases heq : ep = guessedEpoch selector
            · subst ep
              have hnot : ¬ (value.1 (guessedChain selector)).val <
                  (guessedPosition selector).val + 1 := by
                intro hlt; exact hkill ⟨rfl, hlt⟩
              simp [badSelectedHistory, Function.update,
                contextSplicedSignatureOfWord, hvalue, hnot]
            · have heq' : guessedEpoch selector ≠ ep := Ne.symm heq
              simpa [badSelectedHistory, Function.update, heq'] using hgood
          have hguard : ¬(ep = guessedEpoch selector ∧
              (value.1 (guessedChain selector)).val ≤
                (guessedPosition selector).val) := by
            intro h
            exact hkill ⟨h.1, by omega⟩
          simp [hguard, selectedHistoryProjection, hnew]
    · have hnew : badSelectedHistory enc pp selector
          (Function.update history ep (some (msg, none))) = false := by
        by_cases heq : ep = guessedEpoch selector
        · subst ep; simp [badSelectedHistory, Function.update]
        · have heq' : guessedEpoch selector ≠ ep := Ne.symm heq
          simpa [badSelectedHistory, Function.update, heq'] using hgood
      simp [contextSplicedSigningOracle_apply, contextFilteredSplicedSigningOracle,
        hused, hactive, selectedHistoryProjection, hnew]
  · cases hrecord : history ep with
    | none => exact False.elim (hused hrecord)
    | some record =>
      simp only [contextSplicedSigningOracle_apply, contextFilteredSplicedSigningOracle, hrecord]
      simp [selectedHistoryProjection, hgood]

private def runContextFilteredSpliced [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector splice : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H) : ProbComp (Option (Result PP H M R h v)) := do
  let endpoints := splicedEndpoints hash pp splice answer starts
  let pk : GXMSS.PublicKey PP H := ⟨ctx.root pp endpoints, pp⟩
  let sk : GXMSS.SecretKey PP H h v := ⟨pp, starts, endpoints⟩
  let impl : QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v))
      (StateT (Option (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v))) ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (Option (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v))) ProbComp) +
      contextFilteredSplicedSigningOracle hash enc K ctx pp selector splice answer starts endpoints
  let (forgery, state) ←
    (simulateQ impl (adv.forge pk)).run
      (some SyncSignatureUnforgeability.emptyHistory)
  match state with
  | none => return none
  | some history => return some ⟨pk, sk, forgery, history⟩

private theorem runContextFilteredSpliced_advance
    [SampleableType R]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector guess₁ guess₂ : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H)
    (hepoch : guessedEpoch guess₁ = guessedEpoch guess₂)
    (hchain : guessedChain guess₁ = guessedChain guess₂)
    (hnext : (guessedPosition guess₂).val = (guessedPosition guess₁).val + 1)
    (hselectEpoch : guessedEpoch selector = guessedEpoch guess₁)
    (hselectChain : guessedChain selector = guessedChain guess₁)
    (hselectPosition : (guessedPosition guess₂).val ≤ (guessedPosition selector).val) :
    runContextFilteredSpliced hash enc K ctx adv pp selector guess₁ answer starts =
      runContextFilteredSpliced hash enc K ctx adv pp selector guess₂
        (hash.chain pp (guessedEpoch guess₁) (guessedChain guess₁)
          ((guessedPosition guess₁).val + 1) 1 answer) starts := by
  unfold runContextFilteredSpliced
  have hend := splicedEndpoints_advance hash pp guess₁ guess₂ answer starts
    hepoch hchain hnext
  have hfil := contextFilteredSplicedSigningOracle_advance hash enc K ctx pp selector
    guess₁ guess₂ answer starts hepoch hchain hnext hselectEpoch hselectChain
    hselectPosition
  rw [← hend] at hfil
  simp only [← hend, hfil]

/-- The full adaptive source/splice interaction and filtered interaction assign the same mass
to each good returned forgery/history pair. -/
private theorem contextSplicedFiltered_good_raw_output
    [SampleableType R]
    [MeasurableSpace (SyncSignatureUnforgeability.Forgery (Epoch h) M
      (GXMSS.Signature R H h v))]
    [MeasurableSpace (SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v))]
    [MeasurableSingletonClass (SyncSignatureUnforgeability.Forgery (Epoch h) M
      (GXMSS.Signature R H h v))]
    [MeasurableSingletonClass (SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v))]
    (hash : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ)
    (ctx : ChainSimulationContext PP H h v)
    (adv : SchemeAdversary PP H M R h v) (pp : PP)
    (selector splice : Guess h w v) (answer : H)
    (starts : Epoch h → Fin v → H)
    (forgery : SyncSignatureUnforgeability.Forgery (Epoch h) M
      (GXMSS.Signature R H h v))
    (history : SyncSignatureUnforgeability.History (Epoch h) M
      (GXMSS.Signature R H h v))
    (hgood : badSelectedHistory enc pp selector history = false) :
    let endpoints := splicedEndpoints hash pp splice answer starts
    let pk : GXMSS.PublicKey PP H := ⟨ctx.root pp endpoints, pp⟩
    let original : QueryImpl
        (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
          (GXMSS.Signature R H h v))
        (StateT (SyncSignatureUnforgeability.History (Epoch h) M
          (GXMSS.Signature R H h v)) ProbComp) :=
      (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (StateT (SyncSignatureUnforgeability.History (Epoch h) M
          (GXMSS.Signature R H h v)) ProbComp) +
        contextSplicedSigningOracle hash enc K ctx pp splice answer starts endpoints
    let filtered : QueryImpl
        (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
          (GXMSS.Signature R H h v))
        (StateT (Option (SyncSignatureUnforgeability.History (Epoch h) M
          (GXMSS.Signature R H h v))) ProbComp) :=
      (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
        (StateT (Option (SyncSignatureUnforgeability.History (Epoch h) M
          (GXMSS.Signature R H h v))) ProbComp) +
        contextFilteredSplicedSigningOracle hash enc K ctx pp selector splice answer starts
          endpoints
    𝒟[(simulateQ original (adv.forge pk)).run
      SyncSignatureUnforgeability.emptyHistory] {(forgery, history)} =
    𝒟[(simulateQ filtered (adv.forge pk)).run
      (some SyncSignatureUnforgeability.emptyHistory)] {(forgery, some history)} := by
  classical
  let endpoints := splicedEndpoints hash pp splice answer starts
  let pk : GXMSS.PublicKey PP H := ⟨ctx.root pp endpoints, pp⟩
  let original : QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v))
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v)) ProbComp) +
      contextSplicedSigningOracle hash enc K ctx pp splice answer starts endpoints
  let filtered : QueryImpl
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v))
      (StateT (Option (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v))) ProbComp) :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (Option (SyncSignatureUnforgeability.History (Epoch h) M
        (GXMSS.Signature R H h v))) ProbComp) +
      contextFilteredSplicedSigningOracle hash enc K ctx pp selector splice answer starts endpoints
  let bad := badSelectedHistory (H := H) enc pp selector
  let transform : (t : (unifSpec + SyncSignatureUnforgeability.signingSpec
      (Epoch h) M (GXMSS.Signature R H h v)).Domain) →
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v)).Range t ×
        SyncSignatureUnforgeability.History (Epoch h) M
          (GXMSS.Signature R H h v) →
      (unifSpec + SyncSignatureUnforgeability.signingSpec (Epoch h) M
        (GXMSS.Signature R H h v)).Range t :=
    fun t z => match t with
      | .inl _ => z.1
      | .inr _ => if bad z.2 then none else z.1
  have htransform : ∀ t u s', bad s' = false → transform t (u, s') = u := by
    intro t u s' hs
    cases t <;> simp [transform, hs]
  have hmono : ∀ t s, bad s = true →
      ∀ z ∈ support ((original t).run s), bad z.2 = true := by
    intro t s hs z hz
    cases t with
    | inl uniform =>
      simp only [original, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply] at hz
      change z ∈ support
        ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) uniform) >>= fun a =>
          pure (a, s)) at hz
      simp only [mem_support_bind_iff] at hz
      obtain ⟨a, _, hret⟩ := hz
      simp only [support_pure, Set.mem_singleton_iff] at hret
      subst z
      exact hs
    | inr signing =>
      exact badSelectedHistory_contextSplicedSigningOracle_mono hash enc K ctx pp selector
        splice answer starts endpoints signing s hs z hz
  have habsorb : ∀ t, ∀ z ∈ support ((filtered t).run none), z.2 = none := by
    intro t z hz
    cases t with
    | inl uniform =>
      simp only [filtered, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply] at hz
      change z ∈ support
        ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) uniform) >>= fun a =>
          pure (a, none)) at hz
      simp only [mem_support_bind_iff] at hz
      obtain ⟨a, _, hret⟩ := hz
      simp only [support_pure, Set.mem_singleton_iff] at hret
      subst z
      rfl
    | inr signing =>
      simp only [filtered, QueryImpl.add_apply_inr] at hz
      change z ∈ support (contextFilteredSplicedSigningOracle hash enc K ctx pp selector
        splice answer starts endpoints signing none) at hz
      simp [contextFilteredSplicedSigningOracle] at hz
      subst z
      rfl
  have hstep : ∀ t s, bad s = false →
      (fun z => (transform t z, if bad z.2 then none else some z.2)) <$>
        (original t).run s = (filtered t).run (some s) := by
    intro t s hs
    cases t with
    | inl uniform =>
      simp [original, filtered, transform, bad, hs,
        QueryImpl.add_apply_inl]
    | inr signing =>
      change (fun z => (if badSelectedHistory enc pp selector z.2 then none else z.1,
          selectedHistoryProjection enc pp selector z.2)) <$>
            (contextSplicedSigningOracle hash enc K ctx pp splice answer starts
              endpoints signing).run s =
        (contextFilteredSplicedSigningOracle hash enc K ctx pp selector splice answer starts
          endpoints signing).run (some s)
      exact
        selectedHistoryProjection_contextSpliced_step_good hash enc K ctx pp selector
          splice answer starts endpoints signing s hs
  have hinit : bad SyncSignatureUnforgeability.emptyHistory = false := by
    simp [bad, badSelectedHistory, SyncSignatureUnforgeability.emptyHistory]
  simpa [endpoints, pk, original, filtered, bad, hinit] using
    goodOutput_simulateQ_eq_filtered original filtered bad transform htransform
      hmono habsorb hstep (adv.forge pk) SyncSignatureUnforgeability.emptyHistory
      forgery history hgood

private theorem goodEvent_eq_filtered
    {α σ : Type}
    [MeasurableSpace (α × σ)] [MeasurableSpace (α × Option σ)]
    [MeasurableSingletonClass (α × σ)]
    [MeasurableSingletonClass (α × Option σ)]
    [DiscreteMeasurableSpace (α × σ)]
    [DiscreteMeasurableSpace (α × Option σ)]
    (original : ProbComp (α × σ))
    (filtered : ProbComp (α × Option σ)) (bad : σ → Bool)
    (event : α × σ → Bool)
    (hgood : ∀ z, event z = true → bad z.2 = false)
    (hpoint : ∀ z, bad z.2 = false →
      𝒟[original] {z} = 𝒟[filtered] {(z.1, some z.2)}) :
    𝒟[event <$> original] {true} =
      𝒟[(fun z => z.2.elim false (fun s => event (z.1, s))) <$> filtered] {true} := by
  classical
  let filteredEvent : α × Option σ → Bool :=
    fun z => z.2.elim false (fun s => event (z.1, s))
  change 𝒟[event <$> original] {true} = 𝒟[filteredEvent <$> filtered] {true}
  rw [evalDist_map_apply original Measurable.of_discrete (measurableSet_singleton true),
    evalDist_map_apply filtered Measurable.of_discrete (measurableSet_singleton true)]
  change 𝒟[original] {z | event z = true} =
    𝒟[filtered] {z | filteredEvent z = true}
  rw [← prEvent_eq_evalDist_of_discrete original (fun z => event z = true),
    ← prEvent_eq_evalDist_of_discrete filtered (fun z => filteredEvent z = true)]
  rw [OracleComp.prEvent_eq_tsum_ite, OracleComp.prEvent_eq_tsum_ite]
  conv_rhs =>
    rw [ENNReal.tsum_prod']
  conv_lhs =>
    rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro a
  rw [tsum_option _ ENNReal.summable]
  simp only [filteredEvent, Option.elim_none,
    Option.elim_some, Bool.false_eq_true, ite_false, zero_add]
  exact tsum_congr fun s => by
    by_cases he : event (a, s) = true
    · simp only [he, ite_true]
      simpa only [prEvent_eq_evalDist_singleton, Prod.mk.eta] using
        hpoint (a, s) (hgood (a, s) he)
    · simp [he]

end GXMSS.Reductions

namespace GXMSS.Interval.Reductions
open IncomparableEncoding ENNReal OracleComp OracleSpec SyncSignatureUnforgeability
    GXMSS.Reductions GXMSS.IntervalMerkle
variable {PP T X H M R : Type} {h w v : ℕ}

/-- Filtered adaptive interval splice interaction. A successful signing word below the
selected cut kills the run; fresh inactive requests return failure and consume their epoch. -/
noncomputable def filteredChainSpliceView [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Epoch h) M (GXMSS.Signature R H h v))
    (pp : PP) (selector splice : Guess h w v) (response : H)
    (starts : Epoch h → Fin v → H) (fillers : Fillers I H) :
    ProbComp (Option (ExperimentResult (GXMSS.PublicKey PP H) (Epoch h) M
      (GXMSS.Signature R H h v))) :=
  (fun result => result.map (fun out : Result PP H M R h v =>
    ((out.pk, out.forgery, out.history) : ExperimentResult
      (GXMSS.PublicKey PP H) (Epoch h) M (GXMSS.Signature R H h v)))) <$>
    runContextFilteredSpliced P enc K (intervalChainContext P I fillers) A pp
      selector splice response starts

/-- Consecutive non-honest cuts give equal whole filtered interval programs, including
public roots, adaptive replies, inactive failures, consumed history and the absorbing kill state. -/
theorem filteredChainSpliceView_advance [SampleableType R]
    (P : HashInstance PP T X H h w v)
    (enc : IncomparableEncoding PP M R (Epoch h) v (2 ^ w)) (K : ℕ) (I : Interval h)
    (A : Adversary unifSpec (GXMSS.PublicKey PP H) (Epoch h) M (GXMSS.Signature R H h v))
    (pp : PP) (epoch : Epoch h) (chain : Fin v)
    (selectedPosition firstPosition secondPosition : Fin (2 ^ w - 1)) (response : H)
    (starts : Epoch h → Fin v → H) (fillers : Fillers I H)
    (hnext : secondPosition.val = firstPosition.val + 1)
    (hselectPosition : secondPosition.val ≤ selectedPosition.val) :
    filteredChainSpliceView P enc K I A pp (epoch, chain, selectedPosition)
      (epoch, chain, firstPosition) response starts fillers =
      filteredChainSpliceView P enc K I A pp (epoch, chain, selectedPosition)
        (epoch, chain, secondPosition)
        (P.chain pp epoch chain (firstPosition.val + 1) 1 response) starts fillers := by
  unfold filteredChainSpliceView
  rw [runContextFilteredSpliced_advance P enc K (intervalChainContext P I fillers) A pp
    (epoch, chain, selectedPosition) (epoch, chain, firstPosition) (epoch, chain, secondPosition)
    response starts rfl rfl hnext rfl rfl hselectPosition]
  rfl

end GXMSS.Interval.Reductions
