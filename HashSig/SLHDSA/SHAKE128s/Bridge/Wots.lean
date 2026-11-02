/-
Copyright (c) 2026 Tom Wambsgans. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Wambsgans
-/

module

public import HashSig.SLHDSA.SHAKE128s.Bridge.Encodings
public import HashSig.SLHDSA.SHAKE128s.Bridge.Transfer
import HashSig.SLHDSA.SHAKE128s.Proof.ForsProgram

/-!
# The paper's hashing and WOTS+ programs are FIPS 205's, query for query

The paper model (`HashSig.SLHDSA.SHAKE128s.Statement.Scheme`) runs over one oracle with `240`-bit
answers; FIPS 205's library runs over the typed interface `unifSpec + hashSpec FIPS205.core`, which
`encImpl FIPS205.params` maps to one oracle with `30`-byte answers. This module shows that each
hashing and WOTS+ program of the paper, with its answers relabelled by `answerEquiv`
(`relabel answerEquiv`), is the corresponding FIPS 205 program mapped through `encImpl`, with its
output read back by `digestEquiv.symm`: the two programs issue the same queries in the same order.

Conventions: seeds are paper digests, given to FIPS 205 through `digestEquiv`; every other node
(messages, chain values, signatures) is a FIPS 205 node, given to the paper through
`digestEquiv.symm` (`wotsOfCore` for a whole signature); addresses are paper addresses, given to
FIPS 205 through `toAdrs`. Secrets come from the oracle-secret provider
`oracleSecret FIPS205.core (Equiv.refl _)`, the provider of `SLHDSA.Security.romScheme`.

## Main statements

* `simulateQ_relabel_tweakable` (and `_f`, `_h`, `_digestArray`): one tweakable-hash query.
* `simulateQ_relabel_derive`: a secret value is the oracle-secret provider's query.
* `simulateQ_relabel_chain`: `Wots.chain` is `chainM`.
* `simulateQ_relabel_sequenceFin`: `sequenceFin` is `Vector.ofFnM`, componentwise.
* `simulateQ_relabel_wotsPublicKey`, `simulateQ_relabel_wotsSign`,
  `simulateQ_relabel_wotsPublicKeyFromSignature`: WOTS+ key generation, signing and public-key
  recovery are `wotsPkGenWithSecret`, `wotsSignWithSecret` and `wotsPkFromSigWith` at the public
  hash callbacks. They hold at every WOTS+ hash address with a clear hash word.
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.SHAKE128s.Bridge

open SLHDSA SLHDSA.Security

/-- Programs of the paper model. -/
local notation "PaperComp" => OracleComp OracleWorld
/-- Programs of FIPS 205 over the typed interface. -/
local notation "TypedComp" => OracleComp (unifSpec + hashSpec FIPS205.core)

/-- The single oracle of FIPS 205's SHAKE model asked at a byte string. -/
local notation "ask" x =>
  (liftM (OracleSpec.query (spec := Game.World FIPS205.Answer) (Sum.inr x)) :
    OracleComp (Game.World FIPS205.Answer) FIPS205.Answer)

/-! ## One hash query -/

/-- A relabelled paper hash query is the single oracle's query, read back by
`answerEquiv.symm`. -/
theorem simulateQ_relabel_hash (input : Bytes) :
    simulateQ (relabel answerEquiv) (Hashing.hash input : PaperComp HashOutput) =
      answerEquiv.symm <$> ask input := by
  simp only [Hashing.hash]
  rfl

/-- A FIPS 205 tweakable-hash query is the single oracle's query at its encoding, read at its
first `n` bytes. -/
theorem simulateQ_encImpl_tl (seed : Digest) (a : Adrs) (xs : List FIPS205.core.Y) :
    simulateQ (encImpl FIPS205.params)
        (PublicHash.tl FIPS205.core (digestEquiv seed) a xs : TypedComp _) =
      prefixBytes FIPS205.params.params.n <$>
        ask (encode FIPS205.params
          (.inl (.thash (digestEquiv seed) (FIPS205.core.adrsToKey a) xs))) := by
  simp only [PublicHash.tl, encImpl]
  simp
  rfl

/-- **One tweakable-hash query.** The paper's tweakable hash of the concatenated nodes `ys` is
FIPS 205's `T_ℓ` of `ys`, at the same seed and address. -/
theorem simulateQ_relabel_tweakable (seed : Digest) (a : Address) (ys : List FIPS205.core.Y) :
    simulateQ (relabel answerEquiv)
        (Hashing.tweakable seed a ((ys.map fun y => bytesBE n (digestEquiv.symm y)).flatten) :
          PaperComp Digest) =
      digestEquiv.symm <$> simulateQ (encImpl FIPS205.params)
        (PublicHash.tl FIPS205.core (digestEquiv seed) (toAdrs a) ys : TypedComp _) := by
  have henc := encode_thash_toAdrs seed a (ys.map digestEquiv.symm)
  simp only [List.map_map, Function.comp_def, Equiv.apply_symm_apply, List.map_id'] at henc
  rw [simulateQ_encImpl_tl, henc, Hashing.tweakable, Hashing.shortHash, simulateQ_bind,
    simulateQ_relabel_hash, bind_map_left]
  simp only [simulateQ_pure]
  have key : ∀ ans : FIPS205.Answer, Hashing.truncate (answerEquiv.symm ans) =
      digestEquiv.symm (prefixBytes FIPS205.params.params.n ans) := by
    intro ans
    have := prefixBytes_answerEquiv (answerEquiv.symm ans)
    rw [Equiv.apply_symm_apply] at this
    rw [this, Equiv.symm_apply_apply]
  simp only [key]
  rfl

/-- The paper's tweakable hash of one node is FIPS 205's `F`. -/
theorem simulateQ_relabel_tweakable_f (seed : Digest) (a : Address) (y : FIPS205.core.Y) :
    simulateQ (relabel answerEquiv)
        (Hashing.tweakable seed a (bytesBE n (digestEquiv.symm y)) : PaperComp Digest) =
      digestEquiv.symm <$> simulateQ (encImpl FIPS205.params)
        (PublicHash.f FIPS205.core (digestEquiv seed) (toAdrs a) y : TypedComp _) := by
  have h := simulateQ_relabel_tweakable seed a [y]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil] at h
  exact h

/-- The paper's tweakable hash of two nodes is FIPS 205's `H`. -/
theorem simulateQ_relabel_tweakable_h (seed : Digest) (a : Address) (l r : FIPS205.core.Y) :
    simulateQ (relabel answerEquiv)
        (Hashing.tweakable seed a (bytesBE n (digestEquiv.symm l) ++
          bytesBE n (digestEquiv.symm r)) : PaperComp Digest) =
      digestEquiv.symm <$> simulateQ (encImpl FIPS205.params)
        (PublicHash.h FIPS205.core (digestEquiv seed) (toAdrs a) l r : TypedComp _) := by
  have h := simulateQ_relabel_tweakable seed a [l, r]
  simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil] at h
  exact h

/-- **Secret values.** The paper's `Hashing.derive` is the oracle-secret provider of
`romScheme`: the tweakable hash at the secret address applied to the secret seed. -/
theorem simulateQ_relabel_derive (publicSeed secretSeed : Digest) (a : Address) :
    simulateQ (relabel answerEquiv)
        (Hashing.derive publicSeed secretSeed a : PaperComp Digest) =
      digestEquiv.symm <$> simulateQ (encImpl FIPS205.params)
        (oracleSecret FIPS205.core (Equiv.refl _) (digestEquiv publicSeed)
          (digestEquiv secretSeed) (toAdrs a) : TypedComp _) := by
  have h := simulateQ_relabel_tweakable_f publicSeed a (digestEquiv secretSeed)
  rw [Equiv.symm_apply_apply] at h
  exact h

/-! ## WOTS+ chains -/

/-- `chainWith` unfolded from its first step: one hash at index `i`, then `s` steps from
`i + 1`. -/
theorem chainWith_succ' {Y : Type} {m : Type → Type*} [Monad m]
    (hash : Adrs → Y → m Y) (adrs : Adrs) (x : Y) (i s : ℕ) :
    chainWith hash adrs x i (s + 1) =
      hash (adrs.setHashAddress i) x >>= fun y => chainWith hash adrs y (i + 1) s := by
  exact chainWith_head hash adrs x i s

/-- **WOTS+ chains.** The paper's chain of `steps` steps from index `start` is FIPS 205's
`chainM`, provided every hash index fits its 32-bit field. -/
theorem simulateQ_relabel_chain (seed : Digest) (a : Address) (start steps : ℕ)
    (x : FIPS205.core.Y) (h : start + steps ≤ 2 ^ 32) :
    simulateQ (relabel answerEquiv)
        (Wots.chain seed a start steps (digestEquiv.symm x) : PaperComp Digest) =
      digestEquiv.symm <$> simulateQ (encImpl FIPS205.params)
        (chainM FIPS205.core (digestEquiv seed) (toAdrs a) x start steps : TypedComp _) := by
  induction steps generalizing start x with
  | zero => simp [Wots.chain_zero, chainM, chainWith_zero]
  | succ steps ih =>
    unfold chainM at ih ⊢
    rw [Wots.chain_succ, chainWith_succ', simulateQ_bind, simulateQ_relabel_tweakable_f,
      toAdrs_chainStepAddress a (by omega), simulateQ_bind, map_bind, bind_map_left]
    refine bind_congr fun y => ?_
    exact ih (start + 1) y (by omega)

/-! ## Sequencing -/

/-- **Sequencing.** If each paper program `P i` is the FIPS 205 program `V i` read back by
`conv`, then the paper's `sequenceFin` of `P` is FIPS 205's `Vector.ofFnM` of `V`, read back
componentwise. -/
theorem simulateQ_relabel_sequenceFin {α β : Type} (conv : β → α) :
    ∀ (k : ℕ) (P : Fin k → PaperComp α) (V : Fin k → TypedComp β),
      (∀ i, simulateQ (relabel answerEquiv) (P i) =
        conv <$> simulateQ (encImpl FIPS205.params) (V i)) →
      simulateQ (relabel answerEquiv) (sequenceFin k P) =
        (fun (v : Vector β k) (i : Fin k) => conv v[i]) <$>
          simulateQ (encImpl FIPS205.params) (Vector.ofFnM V) := by
  intro k P V h
  exact sequenceFin_ofFnM_bridge (simulateQ' (relabel answerEquiv))
    (simulateQ' (encImpl FIPS205.params)) P V conv h

/-! ## WOTS+ -/

/-- The paper's WOTS+ signature of a FIPS 205 one: every chain value read as a digest. -/
@[expose] def wotsOfCore (σ : WotsSig FIPS205.params.params FIPS205.core) : WotsSignature :=
  fun j => digestEquiv.symm (σ[j.val]'j.isLt)

/-- The paper's bytes of the nodes of a vector are the concatenated bytes of its entries. -/
theorem digestArrayBytes_getElem {k : ℕ} (v : Vector FIPS205.core.Y k) :
    digestArrayBytes (fun i : Fin k => digestEquiv.symm v[i]) =
      (v.toList.map fun y => bytesBE n (digestEquiv.symm y)).flatten := by
  rw [digestArrayBytes]
  congr 1
  apply List.ext_getElem <;> simp

/-- The paper's tweakable hash of the nodes of a vector is FIPS 205's `T_ℓ` of its entries. -/
theorem simulateQ_relabel_tweakable_digestArray (seed : Digest) (a : Address) {k : ℕ}
    (v : Vector FIPS205.core.Y k) :
    simulateQ (relabel answerEquiv)
        (Hashing.tweakable seed a (digestArrayBytes (fun i : Fin k => digestEquiv.symm v[i])) :
          PaperComp Digest) =
      digestEquiv.symm <$> simulateQ (encImpl FIPS205.params)
        (PublicHash.tl FIPS205.core (digestEquiv seed) (toAdrs a) v.toList : TypedComp _) := by
  rw [digestArrayBytes_getElem, simulateQ_relabel_tweakable]

/-- One WOTS+ chain from its secret value: the paper's secret derivation followed by `steps`
chain steps is FIPS 205's provider query at `wotsSkAdrs` followed by `chainWith` at
`wotsChainAdrs`. -/
theorem simulateQ_relabel_wotsChain (secretSeed publicSeed : Digest) (a : Address)
    (hk : a.kind = .wotsHash) (hh : a.hashOrIndex = 0) (i : Fin chains) (steps : ℕ)
    (hs : steps < 2 ^ 32) :
    simulateQ (relabel answerEquiv) (do
        let secret ← Hashing.derive publicSeed secretSeed (Wots.secretAddress a i)
        Wots.chain publicSeed { a with chainOrHeight := BitVec.ofNat 32 i.val } 0 steps secret :
        PaperComp Digest) =
      digestEquiv.symm <$> simulateQ (encImpl FIPS205.params) (do
        let x ← oracleSecret FIPS205.core (Equiv.refl _) (digestEquiv publicSeed)
          (digestEquiv secretSeed) (wotsSkAdrs (toAdrs a) i.val)
        chainWith (PublicHash.f FIPS205.core (digestEquiv publicSeed))
          (wotsChainAdrs (toAdrs a) i.val) x 0 steps : TypedComp _) := by
  rw [simulateQ_bind, simulateQ_relabel_derive, toAdrs_wotsSecretAddress, bind_map_left,
    simulateQ_bind, map_bind]
  refine bind_congr fun x => ?_
  rw [simulateQ_relabel_chain _ _ _ _ _ (by omega), toAdrs_wotsChainAddress a hk hh]
  rfl

/-- **WOTS+ key generation** (Algorithm 6): the paper's `Wots.publicKey` is
`wotsPkGenWithSecret` with the public-hash callbacks and the oracle-secret provider. -/
theorem simulateQ_relabel_wotsPublicKey (secretSeed publicSeed : Digest) (a : Address)
    (hk : a.kind = .wotsHash) (hh : a.hashOrIndex = 0) :
    simulateQ (relabel answerEquiv) (Wots.publicKey secretSeed publicSeed a : PaperComp Digest) =
      digestEquiv.symm <$> simulateQ (encImpl FIPS205.params)
        (wotsPkGenWithSecret FIPS205.core (PublicHash.f FIPS205.core (digestEquiv publicSeed))
          (PublicHash.tl FIPS205.core (digestEquiv publicSeed))
          (oracleSecret FIPS205.core (Equiv.refl _) (digestEquiv publicSeed)
            (digestEquiv secretSeed)) (toAdrs a) : TypedComp _) := by
  rw [Wots.publicKey_eq, wotsPkGenWithSecret_eq, wotsPkGenTopsWithSecret_eq, simulateQ_bind,
    simulateQ_relabel_sequenceFin digestEquiv.symm chains _ _
      (fun i => simulateQ_relabel_wotsChain secretSeed publicSeed a hk hh i (w - 1)
        (by decide)),
    bind_map_left, simulateQ_bind, map_bind]
  refine bind_congr fun v => ?_
  rw [simulateQ_relabel_tweakable_digestArray, toAdrs_wotsPublicKeyAddress]
  rfl

/-- **WOTS+ signing** (Algorithm 7): the paper's `Wots.sign` is `wotsSignWithSecret` with the
public-hash callback and the oracle-secret provider. -/
theorem simulateQ_relabel_wotsSign (msg : FIPS205.core.Y) (secretSeed publicSeed : Digest)
    (a : Address) (hk : a.kind = .wotsHash) (hh : a.hashOrIndex = 0) :
    simulateQ (relabel answerEquiv)
        (Wots.sign (digestEquiv.symm msg) secretSeed publicSeed a : PaperComp WotsSignature) =
      wotsOfCore <$> simulateQ (encImpl FIPS205.params)
        (wotsSignWithSecret FIPS205.core (PublicHash.f FIPS205.core (digestEquiv publicSeed))
          (oracleSecret FIPS205.core (Equiv.refl _) (digestEquiv publicSeed)
            (digestEquiv secretSeed)) msg (toAdrs a) : TypedComp _) := by
  rw [Wots.sign_eq, wotsSignWithSecret_eq,
    simulateQ_relabel_sequenceFin digestEquiv.symm chains _ _ (fun i => by
      rw [simulateQ_relabel_wotsChain secretSeed publicSeed a hk hh i _
        (lt_of_lt_of_le (Checksum.encode _ i).isLt (by decide)), ← chainStepsCore_eq_encode])]
  rfl

/-- **WOTS+ public key from a signature** (Algorithm 8): the paper's
`Wots.publicKeyFromSignature` is `wotsPkFromSigWith` with the public-hash callbacks. -/
theorem simulateQ_relabel_wotsPublicKeyFromSignature
    (sig : WotsSig FIPS205.params.params FIPS205.core) (msg : FIPS205.core.Y)
    (publicSeed : Digest) (a : Address) (hk : a.kind = .wotsHash) (hh : a.hashOrIndex = 0) :
    simulateQ (relabel answerEquiv)
        (Wots.publicKeyFromSignature (wotsOfCore sig) (digestEquiv.symm msg) publicSeed a :
          PaperComp Digest) =
      digestEquiv.symm <$> simulateQ (encImpl FIPS205.params)
        (wotsPkFromSigWith FIPS205.core (PublicHash.f FIPS205.core (digestEquiv publicSeed))
          (PublicHash.tl FIPS205.core (digestEquiv publicSeed)) sig msg (toAdrs a) :
          TypedComp _) := by
  rw [Wots.publicKeyFromSignature_eq, wotsPkFromSigWith_eq, wotsPkFromSigTopsWith_eq,
    simulateQ_bind,
    simulateQ_relabel_sequenceFin digestEquiv.symm chains _ _ (fun i => by
      have hd := (Checksum.encode (digestEquiv.symm msg) i).isLt
      rw [show (wotsOfCore sig) i = digestEquiv.symm sig[i.val] from rfl,
        simulateQ_relabel_chain _ _ _ _ _ (by simp only [w, winternitzBits] at hd ⊢; omega),
        toAdrs_wotsChainAddress a hk hh, ← chainStepsCore_eq_encode]),
    bind_map_left, simulateQ_bind, map_bind]
  refine bind_congr fun v => ?_
  rw [simulateQ_relabel_tweakable_digestArray, toAdrs_wotsPublicKeyAddress]
  rfl

end SLHDSA.SHAKE128s.Bridge
