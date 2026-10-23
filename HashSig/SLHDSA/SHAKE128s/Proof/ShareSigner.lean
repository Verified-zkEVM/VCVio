/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Proof.ServedAgreement

/-!
# The stripped signer is two queries and a table read

The shared half's games answer a signing request in two steps: one that draws the request's
randomiser and digest — the only two inputs the signer asks that the walk's table cannot answer —
and one that assembles the signature. This file is the fact that makes the split faithful: the
stripped signer, run against the walk's warm cache, **is** its two queries followed by a pure
function of the cache (`strippedSign_eq_draw`).

The pure function is `cellSig`: the signer's computation after its digest is known, answered by
replaying the cache. `HonestProbes` already says every input that computation consults is
canonical, and the warm cache holds every canonical input, so stripping answers all of them
locally and the computation collapses to its replay (`strip_eq_pure_of_probes`).
-/

@[expose] public section

open OracleComp OracleSpec

namespace SlhDsaSecurity.ShareSigner

variable {α : Type}

open Security CacheReplay HonestProbes CanonicalGraph

/-! ## The signer after its digest -/

section Generic

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- **What the signer does once its digest is drawn.** -/
def signAfter (randomizer : Digest) (sk : SecretKey) (digest : HashOutput) : m Signature := do
  let indices := MessageDigest.forsIndices digest
  let address := Scheme.forsAddress digest
  let fors ← Fors.sign indices sk.seed sk.publicKey.seed address
  let forsKey ← Fors.publicKeyFromSignature fors indices sk.publicKey.seed address
  let hypertree ← Hypertree.sign forsKey sk.seed sk.publicKey.seed
    (MessageDigest.treeIndex digest) (MessageDigest.leafIndex digest).toFin
  return { randomizer, fors, hypertree }

theorem signInternalAt_eq (randomizer : Digest) (sk : SecretKey) (message : Bytes) :
    SignerRandomiser.signInternalAt (m := m) randomizer sk message =
      Hashing.messageDigest randomizer sk.publicKey message >>= signAfter randomizer sk := rfl

end Generic

/-- **Signing a framed request is its two queries and then `signAfter`.** -/
theorem sign_eq (sk : SecretKey) (request : Message) (framed : Bytes)
    (hframe : request.frame = some framed) :
    Scheme.sign (m := OracleComp HashSpec) sk request =
      (query (spec := HashSpec) (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) :
        OracleComp HashSpec HashOutput) >>= fun seed =>
        (query (spec := HashSpec)
            (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed) :
          OracleComp HashSpec HashOutput) >>= fun digest =>
          signAfter (Hashing.truncate seed) sk digest >>= fun signature =>
            pure (some signature.toBytes) := by
  simp only [Scheme.sign, hframe, SignerRandomiser.signInternal_eq, signInternalAt_eq,
    Hashing.randomizer, Hashing.shortHash, Hashing.messageDigest, Hashing.hash, bind_assoc,
    pure_bind]

/-- **Everything `signAfter` consults is canonical**, read at the replayed cells. -/
theorem probes_signAfter (cache : QueryCache HashSpec) (randomizer : Digest) (sk : SecretKey)
    (digest : HashOutput) :
    Probes cache (signAfter (m := OracleComp HashSpec) randomizer sk digest)
      (Canonical sk.publicKey.seed (replayCells cache sk.seed sk.publicKey.seed)) := by
  refine probes_bind cache _ _ _
    (@Fors.sign Id _ (replayQuery cache) (MessageDigest.forsIndices digest) sk.seed
      sk.publicKey.seed (forsKeyOf digest).address)
    (fors_sign_replay cache (MessageDigest.forsIndices digest) sk.seed sk.publicKey.seed
      (forsKeyOf digest).address)
    (probes_fors_sign cache sk.seed sk.publicKey.seed (forsKeyOf digest)
      (MessageDigest.forsIndices digest)) ?_
  refine probes_bind_replay cache _ _ _
    (probes_fors_publicKeyFromSignature cache sk.seed sk.publicKey.seed
      (forsKeyOf digest) (MessageDigest.forsIndices digest) _
      (fun _ => by rw [fors_sign_entry]) (fun _ _ => by rw [fors_sign_entry])) ?_
  refine probes_bind_replay cache _ _ _
    (probes_hypertree_signLayers cache sk.seed sk.publicKey.seed layers 0
      (MessageDigest.treeIndex digest).toNat (MessageDigest.leafIndex digest).toFin _
      (by omega) (MessageDigest.treeIndex digest).isLt) ?_
  exact probes_pure cache _ _

/-- **`signAfter` commutes with simulation**, as every honest algorithm does. -/
theorem signAfter_simulate {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl HashSpec m) [HasQuery HashSpec m]
    (himpl : ∀ input, impl input = (query (spec := HashSpec) input : m HashOutput))
    (randomizer : Digest) (sk : SecretKey) (digest : HashOutput) :
    simulateQ impl (signAfter (m := OracleComp HashSpec) randomizer sk digest) =
      (signAfter randomizer sk digest : m Signature) := by
  simp only [signAfter, simulateQ_bind, simulateQ_pure,
    Correctness.Naturality.fors_sign_simulate impl himpl,
    VerifierNaturality.fors_simulate impl himpl,
    Correctness.Naturality.hypertree_sign_simulate impl himpl]

/-! ## Stripping a computation the cache answers in full -/

/-- **A computation whose every probe the cache holds strips to its replay.** -/
theorem strip_eq_pure_of_probes {α : Type} (cache : QueryCache HashSpec) :
    ∀ (computation : OracleComp HashSpec α),
      Probes cache computation (fun probe => cache probe ≠ none) →
        simulateQ (StripCached.stripImpl cache) computation =
          pure (simulateQ (replay cache) computation) := by
  intro computation
  induction computation using OracleComp.inductionOn with
  | pure value => intro _; rfl
  | query_bind input next ih =>
    intro hprobes
    have hhead : cache input ≠ none := hprobes input (QueriesUnder.head input next)
    obtain ⟨value, hvalue⟩ := Option.ne_none_iff_exists'.mp hhead
    have hreplay : replay cache input = value := by simp [replay, hvalue]
    have hstrip : simulateQ (StripCached.stripImpl cache)
        (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput) =
        (pure value : OracleComp HashSpec HashOutput) := by
      simp [StripCached.stripImpl, hvalue]
    rw [simulateQ_bind, hstrip, pure_bind, ih value fun probe hprobe =>
      hprobes probe (QueriesUnder.tail input probe next (by rw [hreplay]; exact hprobe))]
    rw [simulateQ_bind, simulateQ_spec_query, hreplay]
    rfl

/-! ## The stripped signer at the walk's cache -/

/-- **The signature the signer assembles from its randomiser and digest**, read off a cache. -/
noncomputable def cellSig (cache : QueryCache HashSpec) (sk : SecretKey) (randomizer : Digest)
    (digest : HashOutput) : Signature :=
  @signAfter Id _ (replayQuery cache) randomizer sk digest

set_option maxHeartbeats 1000000 in
/-- **The stripped signer at the walk's warm cache draws its two inputs and then reads the
table.** -/
theorem strippedSign_eq_draw (sk : SecretKey) (outputs : Programming.Outputs)
    (request : Message) (framed : Bytes) (hframe : request.frame = some framed)
    (hrand : warmCache sk.publicKey.seed sk.seed outputs
      (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) = none)
    (hdigest : ∀ seed : HashOutput, warmCache sk.publicKey.seed sk.seed outputs
      (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed) = none) :
    StrippedGame.strippedSign (warmCache sk.publicKey.seed sk.seed outputs) sk request =
      (query (spec := OracleWorld)
          (Sum.inr (Hashing.randomizerInput sk.prf sk.publicKey.seed framed)) :
        OracleComp OracleWorld HashOutput) >>= fun seed =>
        (query (spec := OracleWorld)
            (Sum.inr (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed)) :
          OracleComp OracleWorld HashOutput) >>= fun digest =>
          pure (some (cellSig (warmCache sk.publicKey.seed sk.seed outputs) sk
            (Hashing.truncate seed) digest).toBytes) := by
  set warm := warmCache sk.publicKey.seed sk.seed outputs with hwarm
  rw [StrippedGame.strippedSign, sign_eq sk request framed hframe, simulateQ_bind,
    show simulateQ (StripCached.stripImpl warm)
        (query (spec := HashSpec) (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) :
          OracleComp HashSpec HashOutput) =
      (query (spec := HashSpec) (Hashing.randomizerInput sk.prf sk.publicKey.seed framed) :
        OracleComp HashSpec HashOutput) from by simp [StripCached.stripImpl, hrand],
    OracleComp.liftComp_bind]
  refine congrArg (Bind.bind _) (funext fun seed => ?_)
  rw [simulateQ_bind,
    show simulateQ (StripCached.stripImpl warm)
        (query (spec := HashSpec)
            (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed) :
          OracleComp HashSpec HashOutput) =
      (query (spec := HashSpec)
          (Hashing.messageInput (Hashing.truncate seed) sk.publicKey framed) :
        OracleComp HashSpec HashOutput) from by simp [StripCached.stripImpl, hdigest seed],
    OracleComp.liftComp_bind]
  refine congrArg (Bind.bind _) (funext fun digest => ?_)
  rw [strip_eq_pure_of_probes warm _ ?_]
  · have hvalue : (simulateQ (replay warm)
        (signAfter (m := OracleComp HashSpec) (Hashing.truncate seed) sk digest >>=
          fun signature => (pure (some signature.toBytes) : OracleComp HashSpec (Option Bytes)))
          : Option Bytes) =
        some (cellSig warm sk (Hashing.truncate seed) digest).toBytes := by
      rw [simulateQ_bind, @signAfter_simulate Id _ _ (replay warm) (replayQuery warm)
        (fun _ => rfl)]
      rfl
    rw [hvalue]
    exact OracleComp.liftComp_pure _ _
  · refine probes_bind_replay warm _ _ _ (fun probe hprobe => ?_) (probes_pure warm _ _)
    exact warmCache_ne_none sk.publicKey.seed sk.seed outputs probe
      (probes_signAfter warm _ sk digest probe hprobe)

end SlhDsaSecurity.ShareSigner
