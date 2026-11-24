/-
Copyright (c) 2026 Minhyuk Hwang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minhyuk Hwang
-/

module

public import VCVio.CryptoFoundations.HardnessAssumptions.CollisionResistance
public import VCVio.EvalDist.Monad.Measure

/-!
# The Merkle–Damgård transform

A compression function `h : C × B → C` maps a chaining value and a message block to a new chaining
value. The Merkle–Damgård transform extends it to messages of any number of blocks: starting from
the initial value `iv`, it absorbs one block at a time, `zᵢ = h (zᵢ₋₁, bᵢ)`. With length padding
(MD strengthening) the message `b₁ ⋯ b_L` is first extended by the block `encodeLen L`, so the hash
is the final chaining value of `b₁ ⋯ b_L (encodeLen L)`.

If the length blocks of two colliding messages differ whenever their lengths differ, the collision
of the iterated hash yields a collision of `h`. This holds for every pair when `encodeLen` is
injective; for a fixed-width length block, which cannot encode every natural number, it holds for
messages below the encodable length, so the security statements require it only on the messages
the adversary can output.

`collisionFinder` computes the collision deterministically from the two colliding messages: it
lists the compression-function inputs of both iterations from the last call backwards and returns
the first position at which they differ. When the message lengths differ, this is the final call,
whose length blocks differ; otherwise both lists have the same length and the first difference
going backwards is a collision, because the next calls agree and so receive equal chaining values.

## Main definitions

- `MerkleDamgard.chain` — the chaining value after absorbing a list of blocks.
- `MerkleDamgard.pad` — length padding: append the block encoding the number of blocks.
- `MerkleDamgard.hash` — the Merkle–Damgård hash with length padding.
- `MerkleDamgard.collisionFinder` — the compression-function collision extracted from two
  messages.
- `MerkleDamgard.crReduction` — the CR adversary against `h` built from one against `hash`.
- `MerkleDamgard.keyedHashFamily` — the transform applied to a keyed compression family.
- `MerkleDamgard.keyedCRReduction` — the keyed-CR adversary against the compression family.

## Main statements

- `MerkleDamgard.collisionFinder_spec` — distinct messages with equal hashes give a collision of
  `h` at `collisionFinder`.
- `MerkleDamgard.crAdvantage_le_crAdvantage_crReduction` — the CR advantage against `hash` is at
  most the CR advantage of `crReduction` against `h`.
- `MerkleDamgard.keyedCRAdvantage_le_keyedCRAdvantage_keyedCRReduction` — the keyed form.

## References

- [Boneh, Shoup, *A Graduate Course in Applied Cryptography*, v0.6, §8.4, Theorem 8.3]
  (https://crypto.stanford.edu/~dabo/cryptobook/BonehShoup_0_6.pdf)
- Jonathan Katz and Yehuda Lindell. *Introduction to Modern Cryptography*, 3rd ed., §6.2
  (domain extension: the Merkle–Damgård transform).
-/

public section

open OracleComp ENNReal CollisionResistance

namespace MerkleDamgard

variable {C B : Type}

/-! ## Construction -/

/-- The chaining value after absorbing `blocks` into `iv` with the compression function `h`:
`z₀ = iv` and `zᵢ = h (zᵢ₋₁, bᵢ)`. -/
@[expose] def chain (h : C × B → C) (iv : C) (blocks : List B) : C :=
  blocks.foldl (fun z b => h (z, b)) iv

/-- Length padding (MD strengthening): append the block that encodes the number of blocks. -/
@[expose] def pad (encodeLen : ℕ → B) (msg : List B) : List B :=
  msg ++ [encodeLen msg.length]

/-- The Merkle–Damgård hash with length padding: the chaining value of the padded message. -/
@[expose] def hash (h : C × B → C) (iv : C) (encodeLen : ℕ → B) (msg : List B) : C :=
  chain h iv (pad encodeLen msg)

/-- The compression-function inputs of `chain h iv revBlocks.reverse`, from the last call to the
first. The first entry pairs the chaining value before the last block with the last block. -/
@[expose] def inputsRev (h : C × B → C) (iv : C) : List B → List (C × B)
  | [] => []
  | b :: bs => (chain h iv bs.reverse, b) :: inputsRev h iv bs

/-- The compression-function collision extracted from two messages: the first position, from the
last call backwards, at which the compression-function inputs of the two padded iterations differ.
If they never differ, the final inputs of the two iterations are returned. -/
@[expose] def collisionFinder [DecidableEq C] [DecidableEq B]
    (h : C × B → C) (iv : C) (encodeLen : ℕ → B) (msg msg' : List B) : (C × B) × (C × B) :=
  (((inputsRev h iv (pad encodeLen msg).reverse).zip
      (inputsRev h iv (pad encodeLen msg').reverse)).find? (fun p => p.1 ≠ p.2)).getD
    ((chain h iv msg, encodeLen msg.length), (chain h iv msg', encodeLen msg'.length))

/-! ## Collision extraction -/

/-- Absorbing a final block applies `h` once more to the chaining value before it. -/
lemma chain_reverse_cons (h : C × B → C) (iv : C) (b : B) (bs : List B) :
    chain h iv (b :: bs).reverse = h (chain h iv bs.reverse, b) := by
  simp [chain]

/-- Read backwards, a padded message starts with its length block. -/
lemma reverse_pad (encodeLen : ℕ → B) (msg : List B) :
    (pad encodeLen msg).reverse = encodeLen msg.length :: msg.reverse := by
  simp [pad]

/-- The hash is the chaining value of the padded message, written through its reversal. -/
lemma hash_eq_chain_reverse (h : C × B → C) (iv : C) (encodeLen : ℕ → B) (msg : List B) :
    hash h iv encodeLen msg = chain h iv (pad encodeLen msg).reverse.reverse := by
  rw [List.reverse_reverse, hash]

/-- Two different block lists of equal length whose chaining values agree have a first
compression-function input, from the last call backwards, at which they differ, and the two
inputs there collide under `h`. -/
theorem find?_zip_inputsRev_spec [DecidableEq C] [DecidableEq B] (h : C × B → C) (iv : C) :
    ∀ {bs bs' : List B}, bs.length = bs'.length → bs ≠ bs' →
      chain h iv bs.reverse = chain h iv bs'.reverse →
      ∃ x x', ((inputsRev h iv bs).zip (inputsRev h iv bs')).find? (fun p => p.1 ≠ p.2) =
        some (x, x') ∧ x ≠ x' ∧ h x = h x'
  | [], [], _, hne, _ => absurd rfl hne
  | [], _ :: _, hlen, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _ => by simp at hlen
  | b :: bs, b' :: bs', hlen, hne, heq => by
    rw [chain_reverse_cons, chain_reverse_cons] at heq
    by_cases hx : (chain h iv bs.reverse, b) = (chain h iv bs'.reverse, b')
    · obtain ⟨hz, rfl⟩ := Prod.mk.inj hx
      have hne' : bs ≠ bs' := fun hbs => hne (hbs ▸ rfl)
      obtain ⟨x, x', hfind, hxx⟩ :=
        find?_zip_inputsRev_spec h iv (Nat.succ.inj hlen) hne' hz
      exact ⟨x, x', by simpa [inputsRev, hx] using hfind, hxx⟩
    · exact ⟨_, _, by simp [inputsRev, hx], hx, heq⟩

/-- **Collision extraction.** If the length blocks of two distinct messages differ whenever their
lengths differ, and the messages have the same Merkle–Damgård hash, then `collisionFinder` returns
a collision of the compression function. The length condition holds for every pair of messages
when `encodeLen` is injective, and for messages shorter than `N` blocks when `encodeLen` is
injective below `N`, as for a fixed-width length block. -/
theorem collisionFinder_spec [DecidableEq C] [DecidableEq B]
    (h : C × B → C) (iv : C) (encodeLen : ℕ → B) {msg msg' : List B}
    (hEnc : encodeLen msg.length = encodeLen msg'.length → msg.length = msg'.length)
    (hne : msg ≠ msg') (heq : hash h iv encodeLen msg = hash h iv encodeLen msg') :
    (collisionFinder h iv encodeLen msg msg').1 ≠ (collisionFinder h iv encodeLen msg msg').2 ∧
      h (collisionFinder h iv encodeLen msg msg').1 =
        h (collisionFinder h iv encodeLen msg msg').2 := by
  by_cases hlen : msg.length = msg'.length
  · have hlen' : (pad encodeLen msg).reverse.length = (pad encodeLen msg').reverse.length := by
      simp [pad, hlen]
    have hne' : (pad encodeLen msg).reverse ≠ (pad encodeLen msg').reverse := by
      rw [reverse_pad, reverse_pad]
      intro hp
      exact hne (List.reverse_injective (List.cons.inj hp).2)
    rw [hash_eq_chain_reverse, hash_eq_chain_reverse] at heq
    obtain ⟨x, x', hfind, hxx⟩ := find?_zip_inputsRev_spec h iv hlen' hne' heq
    simp only [collisionFinder, hfind, Option.getD_some]
    exact hxx
  · have hx : (chain h iv msg, encodeLen msg.length) ≠
        (chain h iv msg', encodeLen msg'.length) :=
      fun hp => hlen (hEnc (Prod.mk.inj hp).2)
    have hfind : ((inputsRev h iv (pad encodeLen msg).reverse).zip
        (inputsRev h iv (pad encodeLen msg').reverse)).find? (fun p => p.1 ≠ p.2) =
        some ((chain h iv msg, encodeLen msg.length),
          (chain h iv msg', encodeLen msg'.length)) := by
      simp [reverse_pad, inputsRev, hx]
    simp only [collisionFinder, hfind, Option.getD_some]
    exact ⟨hx, by simpa [hash, chain, pad] using heq⟩

/-! ## Collision resistance -/

/-- The CR adversary against the compression function `h` built from a CR adversary against the
Merkle–Damgård hash: run the adversary and apply `collisionFinder` to its two messages. -/
@[expose] def crReduction [DecidableEq C] [DecidableEq B]
    (h : C × B → C) (iv : C) (encodeLen : ℕ → B) (adversary : CRAdversary (List B)) :
    CRAdversary (C × B) :=
  ((fun msgs : List B × List B => collisionFinder h iv encodeLen msgs.1 msgs.2) <$>
    (adversary : ProbComp (List B × List B)) : ProbComp ((C × B) × (C × B)))

/-- **Merkle–Damgård preserves collision resistance.** If the length blocks of every message pair
the adversary can output differ whenever the lengths differ (for instance, `encodeLen` is
injective, or the adversary outputs only messages shorter than `N` blocks and `encodeLen` is
injective below `N`), the CR advantage of the adversary against `hash h iv encodeLen` is at most
the CR advantage of `crReduction h iv encodeLen adversary` against `h`. -/
theorem crAdvantage_le_crAdvantage_crReduction [DecidableEq C] [DecidableEq B]
    (h : C × B → C) (iv : C) (encodeLen : ℕ → B) (adversary : CRAdversary (List B))
    (hEnc : ∀ msgs ∈ support (m := ProbComp) adversary,
      encodeLen msgs.1.length = encodeLen msgs.2.length → msgs.1.length = msgs.2.length) :
    crAdvantage (hash h iv encodeLen) adversary ≤
      crAdvantage h (crReduction h iv encodeLen adversary) := by
  have key (A : ProbComp (List B × List B))
      (hA : ∀ msgs ∈ support A,
        encodeLen msgs.1.length = encodeLen msgs.2.length → msgs.1.length = msgs.2.length) :
      𝒟[crExperiment (hash h iv encodeLen) A] {true} ≤
        𝒟[crExperiment h ((fun msgs : List B × List B =>
          collisionFinder h iv encodeLen msgs.1 msgs.2) <$> A :
            ProbComp ((C × B) × (C × B)))] {true} := by
    unfold crExperiment
    rw [bind_map_left]
    refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
      fun ⟨msg, msg'⟩ hmem => ?_
    by_cases hwin : msg ≠ msg' ∧ hash h iv encodeLen msg = hash h iv encodeLen msg'
    · have hcoll := collisionFinder_spec h iv encodeLen (hA _ hmem) hwin.1 hwin.2
      simp [hwin, hcoll]
    · simp [hwin]
  exact key adversary hEnc

/-! ## Keyed hash families -/

variable {K : Type}

/-- The Merkle–Damgård transform of a keyed compression family: the same key generation, and the
Merkle–Damgård hash of the compression function selected by the key. -/
@[expose] def keyedHashFamily (H : KeyedHashFamily K (C × B) C) (iv : C) (encodeLen : ℕ → B) :
    KeyedHashFamily K (List B) C where
  keygen := H.keygen
  hash k := hash (H.hash k) iv encodeLen

/-- The keyed-CR adversary against a compression family built from one against its
Merkle–Damgård transform: run the adversary on the key and apply `collisionFinder` for the
compression function selected by that key. -/
@[expose] def keyedCRReduction [DecidableEq C] [DecidableEq B]
    (H : KeyedHashFamily K (C × B) C) (iv : C) (encodeLen : ℕ → B)
    (adversary : KeyedCRAdversary K (List B)) : KeyedCRAdversary K (C × B) :=
  fun k => do
    let (msg, msg') ← adversary k
    return collisionFinder (H.hash k) iv encodeLen msg msg'

/-- **Merkle–Damgård preserves keyed collision resistance.** If, under every key, the length
blocks of every message pair the adversary can output differ whenever the lengths differ, the
keyed-CR advantage of the adversary against `keyedHashFamily H iv encodeLen` is at most the
keyed-CR advantage of `keyedCRReduction H iv encodeLen adversary` against `H`. -/
theorem keyedCRAdvantage_le_keyedCRAdvantage_keyedCRReduction [DecidableEq C] [DecidableEq B]
    (H : KeyedHashFamily K (C × B) C) (iv : C) (encodeLen : ℕ → B)
    (adversary : KeyedCRAdversary K (List B))
    (hEnc : ∀ k, ∀ msgs ∈ support (adversary k),
      encodeLen msgs.1.length = encodeLen msgs.2.length → msgs.1.length = msgs.2.length) :
    keyedCRAdvantage (keyedHashFamily H iv encodeLen) adversary ≤
      keyedCRAdvantage H (keyedCRReduction H iv encodeLen adversary) := by
  let : MeasurableSpace K := ⊤
  unfold keyedCRAdvantage keyedCRExperiment keyedCRReduction keyedHashFamily
  simp only [monad_norm]
  refine evalDist_bind_apply_mono_of_discrete _ _ _ (MeasurableSet.singleton true) fun k => ?_
  refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
    fun ⟨msg, msg'⟩ hmem => ?_
  by_cases hwin : msg ≠ msg' ∧ hash (H.hash k) iv encodeLen msg = hash (H.hash k) iv encodeLen msg'
  · have hcoll := collisionFinder_spec (H.hash k) iv encodeLen (hEnc k _ hmem) hwin.1 hwin.2
    simp [hwin, hcoll]
  · simp [hwin]

end MerkleDamgard
