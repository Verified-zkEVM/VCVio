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
the interpreted adversary (`simulateQ_unforgeableTranscriptExperiment`).

A scheme `B` whose key generation draws a value `s` and then generates a key pair of a scheme
`A s`, with the secret key re-encoded through `g s`, has as transcript experiment the draw
followed by the transcript experiment of `A s` with its secret key re-encoded. The general form,
`unforgeableTranscriptExperiment_eq_bind_mapSk_of_keygen_eq_map`, presents the key generation of
`A s` as a map `kp s` of a generator `gen s`, and needs signing to agree only at the generated
key pairs. `unforgeableTranscriptExperiment_eq_bind_mapSk` is its special case with `gen s` the
key generation of `A s`, where signing agrees at every key.

Under a stateful interpretation of the ambient oracles, a transcript arises from the three stages
of the experiment in sequence, each run from the state the previous one left
(`exists_mem_support_run_of_mem_support_run_unforgeableTranscriptExperiment`), and when the
interpretation only grows its state, every entry of the signing log is the output of a run of
the signing algorithm between two intermediate states below the final one
(`exists_mem_support_run_sign_of_mem_log`). Conversely, a predicate on the signing log and the
state that the adversary's ambient steps preserve, and that every run of the signing algorithm
preserves once its entry is appended to the log, holds at the end of the signing stage
(`holds_of_mem_support_run_runWithSigningOracle`); established by key generation and preserved by
verification, it holds at the end of the experiment
(`holds_of_mem_support_run_unforgeableTranscriptExperiment`).
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

@[simp] theorem UnforgeableTranscript.mapSk_pk (g : SK' → SK)
    (z : UnforgeableTranscript M PK SK' S) : (z.mapSk g).pk = z.pk := by
  simp only [UnforgeableTranscript.mapSk]

@[simp] theorem UnforgeableTranscript.mapSk_sk (g : SK' → SK)
    (z : UnforgeableTranscript M PK SK' S) : (z.mapSk g).sk = g z.sk := by
  simp only [UnforgeableTranscript.mapSk]

@[simp] theorem UnforgeableTranscript.mapSk_log (g : SK' → SK)
    (z : UnforgeableTranscript M PK SK' S) : (z.mapSk g).log = z.log := by
  simp only [UnforgeableTranscript.mapSk]

@[simp] theorem UnforgeableTranscript.mapSk_msg (g : SK' → SK)
    (z : UnforgeableTranscript M PK SK' S) : (z.mapSk g).msg = z.msg := by
  simp only [UnforgeableTranscript.mapSk]

@[simp] theorem UnforgeableTranscript.mapSk_sig (g : SK' → SK)
    (z : UnforgeableTranscript M PK SK' S) : (z.mapSk g).sig = z.sig := by
  simp only [UnforgeableTranscript.mapSk]

@[simp] theorem UnforgeableTranscript.mapSk_verified (g : SK' → SK)
    (z : UnforgeableTranscript M PK SK' S) : (z.mapSk g).verified = z.verified := by
  simp only [UnforgeableTranscript.mapSk]

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

/-- Suppose the key generation of `B` draws `s` from `draw` and `t` from `gen s`, and outputs the
key pair `kp s t` with its secret key re-encoded through `g s`. Suppose the key generation of
`A s` outputs `kp s t` for `t` drawn from `gen s`, that `B` signs at every generated key pair,
re-encoded, as `A s` signs at that key pair, and that `B` verifies as `A s` does. Then the
transcript experiment of `B` draws `s` and runs the transcript experiment of `A s`, re-encoding
the transcript's secret key through `g s`. -/
theorem unforgeableTranscriptExperiment_eq_bind_mapSk_of_keygen_eq_map {T : Type}
    (B : SignatureAlg (OracleComp spec) M PK SK S)
    (A : Sec → SignatureAlg (OracleComp spec) M PK SK' S)
    (draw : OracleComp spec Sec) (gen : Sec → OracleComp spec T) (kp : Sec → T → PK × SK')
    (g : Sec → SK' → SK)
    (hkg : B.keygen = do
      let s ← draw
      let t ← gen s
      return ((kp s t).1, g s (kp s t).2))
    (hkgA : ∀ s, (A s).keygen = kp s <$> gen s)
    (hsign : ∀ s t m, B.sign (kp s t).1 (g s (kp s t).2) m = (A s).sign (kp s t).1 (kp s t).2 m)
    (hver : ∀ s, B.verify = (A s).verify)
    (adv : UnforgeableAdversary B) :
    unforgeableTranscriptExperiment adv = (draw >>= fun s =>
      UnforgeableTranscript.mapSk (g s) <$>
        unforgeableTranscriptExperiment (sigAlg := A s) ⟨adv.main⟩) := by
  simp only [unforgeableTranscriptExperiment, hkg, hkgA, bind_assoc, pure_bind, map_bind,
    map_pure, bind_map_left, UnforgeableTranscript.mapSk]
  refine bind_congr fun s => bind_congr fun t => ?_
  have hso : B.signingOracle (kp s t).1 (g s (kp s t).2) =
      (A s).signingOracle (kp s t).1 (kp s t).2 := by
    simp only [signingOracle, funext (hsign s t)]
  simp only [runWithSigningOracle, hso, hver s]

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
        unforgeableTranscriptExperiment (sigAlg := A s) ⟨adv.main⟩) :=
  unforgeableTranscriptExperiment_eq_bind_mapSk_of_keygen_eq_map B A draw (fun s => (A s).keygen)
    (fun _ => id) g hkg (fun _ => (id_map _).symm) (fun s _ m => hsign s _ _ m) hver adv

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

/-- **Invariants of the signing stage.** Let `I` be a predicate on a signing log and the state of
a stateful interpretation of the ambient oracles, preserved by every step at an `allowed`
ambient query and by every run of the signing algorithm once its entry is appended to the log.
A program whose ambient queries are all `allowed`, run with the signing oracle from a state
satisfying `I` with the empty log, ends with its log in a state satisfying `I`. -/
theorem holds_of_mem_support_run_runWithSigningOracle {σ : Type}
    (so : QueryImpl spec (StateT σ ProbComp)) (sigAlg : SignatureAlg (OracleComp spec) M PK SK S)
    (pk : PK) (sk : SK) {allowed : ι → Prop} (I : QueryLog (M →ₒ S) → σ → Prop)
    (hamb : ∀ t, allowed t → ∀ log s, I log s → ∀ z ∈ support ((so t).run s), I log z.2)
    (hsign : ∀ msg log s, I log s →
      ∀ z ∈ support ((simulateQ so (sigAlg.sign pk sk msg)).run s), I (log ++ [⟨msg, z.1⟩]) z.2)
    {α : Type} {oa : OracleComp (spec + (M →ₒ S)) α}
    (hoa : AllQueriesSatisfy oa (Sum.elim allowed fun _ ↦ True)) {s₀ : σ} (h₀ : I [] s₀)
    {z : (α × QueryLog (M →ₒ S)) × σ}
    (hz : z ∈ support ((simulateQ so (sigAlg.runWithSigningOracle pk sk oa)).run s₀)) :
    I z.1.2 z.2 := by
  simpa only [List.nil_append] using
    QueryImpl.holds_of_mem_support_run_add_withLogging so (sigAlg.sign pk sk) I hamb hsign hoa h₀ hz

/-- **Invariants of the transcript experiment.** Let `I pk sk log s` be a predicate on a key pair,
a signing log and the state of a stateful interpretation of the ambient oracles. Suppose key
generation establishes it with the empty log, every step at an `allowed` ambient query and every
run of verification preserve it, and every run of signing preserves it once its entry is appended
to the log. Against an adversary whose ambient queries are all `allowed`, every transcript of
the experiment satisfies `I` with its key pair and log in the final state. -/
theorem holds_of_mem_support_run_unforgeableTranscriptExperiment {σ : Type}
    (so : QueryImpl spec (StateT σ ProbComp)) {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    {allowed : ι → Prop} (I : PK → SK → QueryLog (M →ₒ S) → σ → Prop) {s₀ : σ}
    (hkeygen : ∀ z ∈ support ((simulateQ so sigAlg.keygen).run s₀), I z.1.1 z.1.2 [] z.2)
    (hamb : ∀ t, allowed t → ∀ pk sk log s, I pk sk log s →
      ∀ z ∈ support ((so t).run s), I pk sk log z.2)
    (hsign : ∀ pk sk msg log s, I pk sk log s →
      ∀ z ∈ support ((simulateQ so (sigAlg.sign pk sk msg)).run s),
        I pk sk (log ++ [⟨msg, z.1⟩]) z.2)
    (hverify : ∀ pk sk log msg sig s, I pk sk log s →
      ∀ z ∈ support ((simulateQ so (sigAlg.verify pk msg sig)).run s), I pk sk log z.2)
    (adv : UnforgeableAdversary sigAlg)
    (hadv : ∀ pk, AllQueriesSatisfy (adv.main pk) (Sum.elim allowed fun _ ↦ True))
    {z : UnforgeableTranscript M PK SK S × σ}
    (hz : z ∈ support ((simulateQ so (unforgeableTranscriptExperiment adv)).run s₀)) :
    I z.1.pk z.1.sk z.1.log z.2 := by
  obtain ⟨s₁, s₂, hk, hf, hv⟩ :=
    exists_mem_support_run_of_mem_support_run_unforgeableTranscriptExperiment so adv hz
  exact hverify _ _ _ _ _ _
    (holds_of_mem_support_run_runWithSigningOracle so sigAlg z.1.pk z.1.sk (I z.1.pk z.1.sk)
      (fun t ht ↦ hamb t ht z.1.pk z.1.sk) (hsign z.1.pk z.1.sk) (hadv z.1.pk) (hkeygen _ hk) hf)
    _ hv

end SignatureAlg
