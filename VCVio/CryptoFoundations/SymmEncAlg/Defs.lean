/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import Mathlib.Control.Monad.Basic

/-!
# Symmetric encryption schemes

This module contains the probability-independent data and experiments for symmetric encryption.
Semantic notions of correctness and secrecy live in separate compatibility and measure modules.
-/

@[expose] public section

universe u

/-- A monad-generic symmetric encryption scheme over an ambient monad `m`, with message space `M`,
key space `K`, and ciphertext space `C`. -/
structure SymmEncAlg (m : Type → Type u) [Monad m] (M K C : Type) where
  /-- Sample a key. -/
  keygen : m K
  /-- Encrypt a message under a key. -/
  encrypt : K → M → m C
  /-- Decrypt a ciphertext under a key, returning `none` on failure. -/
  decrypt : K → C → m (Option M)

namespace SymmEncAlg

variable {m : Type → Type u} [Monad m] {M K C : Type}

/-- Round-trip experiment: sample a key, encrypt `msg`, then decrypt. -/
def CompleteExp (encAlg : SymmEncAlg m M K C) (msg : M) : m (Option M) := do
  let k ← encAlg.keygen
  let σ ← encAlg.encrypt k msg
  encAlg.decrypt k σ

/-! ## Perfect-secrecy experiments -/

/-- Joint message/ciphertext experiment used to express perfect secrecy. -/
def PerfectSecrecyExp (encAlg : SymmEncAlg m M K C) (mgen : m M) : m (M × C) := do
  let msg' ← mgen
  let k ← encAlg.keygen
  return (msg', ← encAlg.encrypt k msg')

/-- Ciphertext marginal induced by the perfect-secrecy experiment. -/
def PerfectSecrecyCipherExp (encAlg : SymmEncAlg m M K C) (mgen : m M) : m C :=
  Prod.snd <$> encAlg.PerfectSecrecyExp mgen

/-- Ciphertext experiment conditioned on a fixed message. -/
def PerfectSecrecyCipherGivenMsgExp (encAlg : SymmEncAlg m M K C) (msg : M) : m C := do
  let k ← encAlg.keygen
  encAlg.encrypt k msg

lemma PerfectSecrecyExp_eq_bind [LawfulMonad m] (encAlg : SymmEncAlg m M K C) (mgen : m M) :
    encAlg.PerfectSecrecyExp mgen =
      mgen >>= fun msg ↦ (msg, ·) <$> encAlg.PerfectSecrecyCipherGivenMsgExp msg := by
  simp [PerfectSecrecyExp, PerfectSecrecyCipherGivenMsgExp, monad_norm]

lemma PerfectSecrecyCipherExp_eq_bind [LawfulMonad m]
    (encAlg : SymmEncAlg m M K C) (mgen : m M) :
    encAlg.PerfectSecrecyCipherExp mgen =
      mgen >>= fun msg ↦ encAlg.PerfectSecrecyCipherGivenMsgExp msg := by
  simp [PerfectSecrecyCipherExp, PerfectSecrecyExp_eq_bind, monad_norm]

end SymmEncAlg
