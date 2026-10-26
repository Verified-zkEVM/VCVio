/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.SignatureAlg.RomQueryCount
import VCVio.OracleComp.QueryTracking.SubSpec

/-!
# An unforgeability adversary followed by a program on its output

`SignatureAlg.UnforgeableAdversary.withPost adv post` runs the adversary `adv` and then, as its own
queries to the ambient oracles, the program `post pk out` on its public key `pk` and its output
`out`; it discards the program's result and outputs `out`. A reduction uses it to make the
adversary perform computations, a verification of its own forgery for instance, whose queries the
experiment then records like any other query of the adversary.

The experiment against `adv.withPost post` is the experiment of the scheme verifying by `post`
(`SignatureAlg.withVerify`) against `adv`, followed by the scheme's own verification of the
forgery (`SignatureAlg.unforgeableTranscriptExperiment_withPost`). Under a stateful handler, an
event of the former has probability at most that of any event of the latter satisfied by all of
its extensions (`SignatureAlg.prEvent_run_withVerify_le_prEvent_run_withPost`).

* `SignatureAlg.UnforgeableAdversary.RomQueryBound.withPost`: in the random oracle model the
  budget adds up. If `adv` makes at most `qh` hash and `qs` signing queries and every
  `post pk out` at most `v` hash queries, the adversary followed by `post` makes at most `qh + v`
  hash and `qs` signing queries.
-/

public section

open OracleSpec OracleComp

/-- Running a program lifted into `spec + sig` with the queries of `spec` passed through and
those of `sig` answered by a logging implementation runs the program and logs nothing. -/
theorem OracleComp.run_simulateQ_passthrough_add_liftComp {ι ιs : Type} {spec : OracleSpec ι}
    {sig : OracleSpec ιs} (so : QueryImpl sig (WriterT (QueryLog sig) (OracleComp spec)))
    {β : Type} (P : OracleComp spec β) :
    (simulateQ (spec.passthrough + so) (liftComp P (spec + sig))).run =
      (·, ([] : QueryLog sig)) <$> P := by
  rw [QueryImpl.passthrough_add, QueryImpl.simulateQ_add_liftComp_left]
  induction P using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
    rw [simulateQ_bind, WriterT.run_bind', simulateQ_spec_query, QueryImpl.liftTarget_apply]
    change ((·, ([] : QueryLog sig)) <$> (QueryImpl.id' spec t)) >>= _ = _
    simp only [bind_map_left, map_bind, ih]
    simp [QueryImpl.id'_apply]

namespace SignatureAlg

variable {ι : Type} {M PK SK S : Type}

/-- The adversary that runs `adv` and then the program `post pk out` on its public key `pk` and
its output `out`, as its own queries to the ambient oracles; its output is that of `adv`. -/
@[expose] def UnforgeableAdversary.withPost {spec : OracleSpec ι}
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S} (adv : UnforgeableAdversary sigAlg)
    {β : Type} (post : PK → M × S → OracleComp spec β) : UnforgeableAdversary sigAlg where
  main pk := do
    let out ← adv.main pk
    let _ ← liftComp (post pk out) (spec + (M →ₒ S))
    pure out

/-- Running an adversary followed by `post` with the signing oracle is running the adversary with
the signing oracle, then `post` on its output; `post` adds nothing to the log. -/
theorem runWithSigningOracle_withPost {spec : OracleSpec ι}
    (sigAlg : SignatureAlg (OracleComp spec) M PK SK S) (adv : UnforgeableAdversary sigAlg)
    {β : Type} (post : PK → M × S → OracleComp spec β) (pk : PK) (sk : SK) :
    sigAlg.runWithSigningOracle pk sk ((adv.withPost post).main pk) =
      sigAlg.runWithSigningOracle pk sk (adv.main pk) >>= fun r =>
        (fun _ => r) <$> post pk r.1 := by
  simp only [runWithSigningOracle_def, UnforgeableAdversary.withPost, simulateQ_bind,
    WriterT.run_bind', OracleComp.run_simulateQ_passthrough_add_liftComp, simulateQ_pure,
    WriterT.run_pure', bind_map_left, map_bind, map_pure]
  refine bind_congr fun r => ?_
  simp [List.append_nil]

/-- Under a stateful interpretation of the ambient oracles along whose runs a key `key` of the
state never decreases, the program `post` of a transcript of the experiment against `adv`
followed by `post` runs on the transcript's public key and forgery from some state to some state
whose key is at most that of the final one. -/
theorem exists_mem_support_run_post_of_mem_support_run_withPost {spec : OracleSpec ι}
    {σ τ : Type} [Preorder τ] (key : σ → τ) {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (so : QueryImpl spec (StateT σ ProbComp))
    (hmono : ∀ {γ : Type} (ob : OracleComp spec γ) (s : σ),
      ∀ z ∈ support ((simulateQ so ob).run s), key s ≤ key z.2)
    (adv : UnforgeableAdversary sigAlg) {β : Type} (post : PK → M × S → OracleComp spec β)
    {s₀ : σ} {z : UnforgeableTranscript M PK SK S × σ}
    (hz : z ∈ support ((simulateQ so (unforgeableTranscriptExperiment (adv.withPost post))).run
      s₀)) :
    ∃ (t₁ t₂ : σ) (b : β), key t₂ ≤ key z.2 ∧
      (b, t₂) ∈ support ((simulateQ so (post z.1.pk (z.1.msg, z.1.sig))).run t₁) := by
  obtain ⟨s₁, s₂, -, hf, hv⟩ :=
    exists_mem_support_run_of_mem_support_run_unforgeableTranscriptExperiment so _ hz
  rw [runWithSigningOracle_withPost, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hf
  obtain ⟨⟨⟨out, l⟩, t₁⟩, -, hf⟩ := hf
  rw [simulateQ_map, StateT.run_map, support_map] at hf
  obtain ⟨⟨b, t₂⟩, hb, hbt⟩ := hf
  simp only [Prod.mk.injEq] at hbt
  obtain ⟨⟨rfl, -⟩, rfl⟩ := hbt
  exact ⟨t₁, t₂, b, hmono _ _ (z.1.verified, z.2) hv, hb⟩

/-- **An adversary followed by a verification of its forgery.** The experiment against `adv`
followed by `post` is the experiment of the scheme verifying by `post` against `adv`, followed by
the scheme's own verification of the forgery, whose verdict replaces the transcript's. -/
theorem unforgeableTranscriptExperiment_withPost {spec : OracleSpec ι}
    (sigAlg : SignatureAlg (OracleComp spec) M PK SK S) (adv : UnforgeableAdversary sigAlg)
    (post : PK → M × S → OracleComp spec Bool) :
    unforgeableTranscriptExperiment (adv.withPost post) =
      unforgeableTranscriptExperiment
          (sigAlg := sigAlg.withVerify fun pk msg sig => post pk (msg, sig)) ⟨adv.main⟩ >>=
        fun z => (fun v => { z with verified := v }) <$> sigAlg.verify z.pk z.msg z.sig := by
  simp only [unforgeableTranscriptExperiment_def, runWithSigningOracle_withPost, bind_assoc,
    pure_bind, map_eq_bind_pure_comp, Function.comp_def]
  rfl

/-- **The experiment verifying by `post` is a prefix of the experiment against the adversary
followed by `post`.** Under a stateful handler `so` from a state `s`, an event `P` of the run of
the experiment of the scheme verifying by `post` against `adv`, each of whose reachable
occurrences leads, along every run of the scheme's own verification of the forgery, to the event
`Q` with the new verdict, has probability at most that of `Q` in the run of the experiment against
`adv` followed by `post`. -/
theorem prEvent_run_withVerify_le_prEvent_run_withPost {spec : OracleSpec ι} {σ : Type}
    (so : QueryImpl spec (StateT σ ProbComp)) (sigAlg : SignatureAlg (OracleComp spec) M PK SK S)
    (adv : UnforgeableAdversary sigAlg) (post : PK → M × S → OracleComp spec Bool) (s : σ)
    (P Q : UnforgeableTranscript M PK SK S × σ → Prop)
    (hPQ : ∀ z ∈ support ((simulateQ so (unforgeableTranscriptExperiment
        (sigAlg := sigAlg.withVerify fun pk msg sig => post pk (msg, sig)) ⟨adv.main⟩)).run s),
      P z → ∀ r ∈ support ((simulateQ so (sigAlg.verify z.1.pk z.1.msg z.1.sig)).run z.2),
        Q ({ z.1 with verified := r.1 }, r.2)) :
    Pr{let z ← (simulateQ so (unforgeableTranscriptExperiment
        (sigAlg := sigAlg.withVerify fun pk msg sig => post pk (msg, sig)) ⟨adv.main⟩)).run s}[
        P z] ≤
      Pr{let z ← (simulateQ so (unforgeableTranscriptExperiment (adv.withPost post))).run s}[
        Q z] := by
  rw [unforgeableTranscriptExperiment_withPost, simulateQ_bind, StateT.run_bind]
  refine prEvent_le_prEvent_bind_of_support _ _ _ _ fun z hz hP =>
    prEvent_eq_one_of_forall_mem_support _ _ fun b hb => ?_
  rw [simulateQ_map, StateT.run_map, support_map] at hb
  obtain ⟨r, hr, rfl⟩ := hb
  exact hPQ z hz hP r hr

/-- **The budget of an adversary followed by a program.** If `adv` makes at most `qh` hash and
`qs` signing queries and every `post pk out` at most `v` hash queries, then `adv` followed by
`post` makes at most `qh + v` hash and `qs` signing queries. -/
theorem UnforgeableAdversary.RomQueryBound.withPost {hs : OracleSpec ι}
    {sigAlg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S}
    {adv : UnforgeableAdversary sigAlg} {qh qs v : ℕ} (hadv : adv.RomQueryBound qh qs)
    {β : Type} {post : PK → M × S → OracleComp (unifSpec + hs) β}
    (hpost : ∀ pk out, IsQueryBoundP (post pk out) (fun t => t.isRight) v) :
    (adv.withPost post).RomQueryBound (qh + v) qs := by
  intro pk
  obtain ⟨hh, hsq⟩ := hadv pk
  have hhash : ∀ t : (unifSpec + hs).Domain,
      t.isRight ↔ IsHashQuery (hs := hs) (M := M) (S := S) (.inl t) := by
    rintro (n | t) <;> simp [IsHashQuery]
  have hsign : ∀ t : (unifSpec + hs).Domain,
      False ↔ IsSignQuery (hs := hs) (M := M) (S := S) (.inl t) := by
    rintro (n | t) <;> simp [IsSignQuery]
  refine ⟨isQueryBoundP_bind hh fun out _ => ?_, (isQueryBoundP_bind hsq fun out _ => ?_).mono
    (Nat.add_zero qs).le⟩
  · exact (isQueryBoundP_bind ((hpost pk out).liftComp_subSpec hhash)
      fun _ _ => isQueryBoundP_pure _ _ 0).mono (Nat.add_zero v).le
  · exact isQueryBoundP_bind ((isQueryBoundP_false (post pk out) 0).liftComp_subSpec hsign)
      fun _ _ => isQueryBoundP_pure _ _ 0

end SignatureAlg
