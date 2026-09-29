/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import VCVio.CryptoFoundations.SignatureAlg.Naturality

/-!
# The transcript of the unforgeability experiment

`unforgeableTranscriptExperiment` runs the body of `unforgeableExperiment` and returns its whole
transcript (`UnforgeableTranscript`): the key pair, the signing oracle's log, the forgery and the
verification verdict.  The experiment's success bit is `UnforgeableTranscript.wins` of the
transcript (`map_wins_unforgeableTranscriptExperiment`), so any event of the experiment is an
event of the transcript, and a proof about the adversary's success may read off the transcript
everything the experiment computed.

The transcript experiment commutes with oracle interpretation: interpreting the ambient oracles
of the whole experiment through `G` is the transcript experiment of the interpreted scheme against
the interpreted adversary (`simulateQ_unforgeableTranscriptExperiment`). A scheme whose key
generation draws a value `s` and then runs the key generation of a scheme `A s` whose secret keys
re-encode, through `g s`, into its own, while signing and verification agree under the
re-encoding, has as transcript experiment the draw followed by the transcript experiment of `A s`
with its secret key re-encoded (`unforgeableTranscriptExperiment_eq_bind_mapSk`).

Under a stateful interpretation of the ambient oracles, a transcript arises from the three stages
of the experiment in sequence, each run from the state the previous one left
(`exists_mem_support_run_of_mem_support_run_unforgeableTranscriptExperiment`), and when the
interpretation only grows its state, every entry of the signing log is the output of a run of
the signing algorithm between two intermediate states below the final one
(`exists_mem_support_run_sign_of_mem_log`).
-/

public section

open OracleSpec OracleComp

namespace SignatureAlg

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {M PK SK SK' S Sec : Type}

/-- The transcript of one execution of the unforgeability experiment: the key pair, the signing
oracle's log of queried messages and returned signatures, the forgery, and whether it verifies. -/
structure UnforgeableTranscript (M PK SK S : Type) where
  /-- The public key handed to the adversary. -/
  pk : PK
  /-- The secret key used by the signing oracle. -/
  sk : SK
  /-- The signing oracle's log. -/
  log : QueryLog (M →ₒ S)
  /-- The forged message. -/
  msg : M
  /-- The forged signature. -/
  sig : S
  /-- Whether the forgery verifies. -/
  verified : Bool

open scoped Classical in
/-- The success bit of a transcript: the forgery verifies and its message was never signed. -/
noncomputable def UnforgeableTranscript.wins (o : UnforgeableTranscript M PK SK S) : Bool :=
  !o.log.wasQueried o.msg && o.verified

/-- A transcript wins exactly when its message is absent from the signing log and the forgery
verifies. -/
theorem UnforgeableTranscript.wins_eq_true_iff (o : UnforgeableTranscript M PK SK S) :
    o.wins = true ↔ o.msg ∉ o.log.map (fun e => e.1) ∧ o.verified = true := by
  classical
  rw [← QueryLog.getQ_ne_nil_iff_mem_map_fst]
  simp only [UnforgeableTranscript.wins, QueryLog.wasQueried, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not]

/-- The unforgeability experiment returning its whole transcript. -/
noncomputable def unforgeableTranscriptExperiment
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S} (adv : UnforgeableAdversary sigAlg) :
    OracleComp spec (UnforgeableTranscript M PK SK S) := do
  let (pk, sk) ← sigAlg.keygen
  let ((msg, σ), log) ← sigAlg.runWithSigningOracle pk sk (adv.main pk)
  let verified ← sigAlg.verify pk msg σ
  return ⟨pk, sk, log, msg, σ, verified⟩

/-- The transcript with its secret key replaced by its image under `g`. -/
def UnforgeableTranscript.mapSk (g : SK' → SK) (z : UnforgeableTranscript M PK SK' S) :
    UnforgeableTranscript M PK SK S :=
  ⟨z.pk, g z.sk, z.log, z.msg, z.sig, z.verified⟩

/-- The unforgeability experiment is the success bit of its transcript. -/
theorem map_wins_unforgeableTranscriptExperiment
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S} (adv : UnforgeableAdversary sigAlg) :
    UnforgeableTranscript.wins <$> unforgeableTranscriptExperiment adv =
      unforgeableExperiment adv := by
  simp only [unforgeableTranscriptExperiment, unforgeableExperiment, map_bind, map_pure]
  rfl

/-- Interpreting the ambient oracles of the transcript experiment through `G` gives the
transcript experiment of the interpreted scheme against the interpreted adversary. -/
theorem simulateQ_unforgeableTranscriptExperiment (G : QueryImpl spec (OracleComp spec'))
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S} (adv : UnforgeableAdversary sigAlg) :
    simulateQ G (unforgeableTranscriptExperiment adv) =
      unforgeableTranscriptExperiment (sigAlg := sigAlg.map (simulateQ' G))
        (adv.mapOracles G) := by
  simp only [unforgeableTranscriptExperiment, runWithSigningOracle, simulateQ_bind,
    simulateQ_pure, map_keygen, map_verify, UnforgeableAdversary.mapOracles_main]
  refine bind_congr fun kp => ?_
  rw [simulateQ_WriterT_compose (spec.passthrough + sigAlg.signingOracle kp.1 kp.2) G
    ((spec'.passthrough + (sigAlg.map (simulateQ' G)).signingOracle kp.1 kp.2) ∘ₛ
      G.addLift (QueryImpl.id' (M →ₒ S))), QueryImpl.simulateQ_compose]
  rintro (t | msg)
  · simp [QueryImpl.simulateQ_add_liftM_left, writerT_run_simulateQ_liftTarget]
  · simp [QueryImpl.simulateQ_add_liftM_right, signingOracle]

/-- If the key generation of `B` draws `s` from `draw`, runs the key generation of `A s` and
re-encodes its secret key through `g s`, and `B` signs a re-encoded key and verifies as `A s` does,
then the transcript experiment of `B` draws `s` and runs the transcript experiment of `A s`,
re-encoding the transcript's secret key through `g s`. -/
theorem unforgeableTranscriptExperiment_eq_bind_mapSk
    (B : SignatureAlg (OracleComp spec) M PK SK S)
    (A : Sec → SignatureAlg (OracleComp spec) M PK SK' S)
    (draw : OracleComp spec Sec) (g : Sec → SK' → SK)
    (hkg : B.keygen = do let s ← draw; let kp ← (A s).keygen; return (kp.1, g s kp.2))
    (hsign : ∀ s pk sk' m, B.sign pk (g s sk') m = (A s).sign pk sk' m)
    (hver : ∀ s, B.verify = (A s).verify)
    (adv : UnforgeableAdversary B) :
    unforgeableTranscriptExperiment adv = (draw >>= fun s =>
      UnforgeableTranscript.mapSk (g s) <$>
        unforgeableTranscriptExperiment (sigAlg := A s) ⟨adv.main⟩) := by
  simp only [unforgeableTranscriptExperiment, hkg, bind_assoc, pure_bind, map_bind, map_pure,
    UnforgeableTranscript.mapSk]
  refine bind_congr fun s => bind_congr fun kp => ?_
  have hso : B.signingOracle kp.1 (g s kp.2) = (A s).signingOracle kp.1 kp.2 := by
    funext m; simp [signingOracle, hsign]
  simp only [runWithSigningOracle, hso, hver s]

/-- Under a stateful interpretation of the ambient oracles, a transcript arises from key
generation run from the initial state, the adversary under the logged signing oracle run from
the state key generation left, and verification run from the state the adversary left to the
final one. -/
theorem exists_mem_support_run_of_mem_support_run_unforgeableTranscriptExperiment {σ : Type}
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S} (so : QueryImpl spec (StateT σ ProbComp))
    (adv : UnforgeableAdversary sigAlg) {s₀ : σ} {z : UnforgeableTranscript M PK SK S × σ}
    (hz : z ∈ support ((simulateQ so (unforgeableTranscriptExperiment adv)).run s₀)) :
    ∃ s₁ s₂ : σ, ((z.1.pk, z.1.sk), s₁) ∈ support ((simulateQ so sigAlg.keygen).run s₀) ∧
      (((z.1.msg, z.1.sig), z.1.log), s₂) ∈
        support ((simulateQ so (sigAlg.runWithSigningOracle z.1.pk z.1.sk
          (adv.main z.1.pk))).run s₁) ∧
      (z.1.verified, z.2) ∈
        support ((simulateQ so (sigAlg.verify z.1.pk z.1.msg z.1.sig)).run s₂) := by
  unfold unforgeableTranscriptExperiment at hz
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨⟨⟨pk, sk⟩, s₁⟩, hk, ⟨⟨⟨msg, sig⟩, log⟩, s₂⟩, hf, ⟨verified, s₃⟩, hv, rfl⟩ := hz
  exact ⟨s₁, s₂, hk, hf, hv⟩

/-- Under a state-monotone stateful interpretation of the ambient oracles, every entry of a
transcript's signing log is the output of a run of the signing algorithm on the logged message
between two intermediate states, the second below the final state. -/
theorem exists_mem_support_run_sign_of_mem_log {σ : Type} [Preorder σ]
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S} (so : QueryImpl spec (StateT σ ProbComp))
    (hmono : ∀ {β : Type} (ob : OracleComp spec β) (s : σ) (z : β × σ),
      z ∈ support ((simulateQ so ob).run s) → s ≤ z.2)
    (adv : UnforgeableAdversary sigAlg) {s₀ : σ} {z : UnforgeableTranscript M PK SK S × σ}
    (hz : z ∈ support ((simulateQ so (unforgeableTranscriptExperiment adv)).run s₀))
    {e : (t : (M →ₒ S).Domain) × (M →ₒ S).Range t} (he : e ∈ z.1.log) :
    ∃ s₁ s₂ : σ, s₂ ≤ z.2 ∧
      (e.2, s₂) ∈ support ((simulateQ so (sigAlg.sign z.1.pk z.1.sk e.1)).run s₁) := by
  obtain ⟨s₁, s₂, -, hf, hv⟩ :=
    exists_mem_support_run_of_mem_support_run_unforgeableTranscriptExperiment so adv hz
  obtain ⟨t₁, t₂, -, ht₂, hmem⟩ :=
    QueryImpl.exists_le_mem_support_run_of_mem_log_add_withLogging so hmono
      (sigAlg.sign z.1.pk z.1.sk) (adv.main z.1.pk) hf he
  exact ⟨t₁, t₂, ht₂.trans (hmono _ _ (z.1.verified, z.2) hv), hmem⟩

end SignatureAlg
