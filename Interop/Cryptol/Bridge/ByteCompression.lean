/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Cryptol.Bridge.Compression
import Mathlib.Data.List.Range
import Mathlib.Tactic.FinCases

/-!
# The imperative byte-array compression boundary

Loop invariants track the initialized schedule prefix and all eight registers.
The byte-facing statement requires an eight-word state and a complete block
starting at any offset; no alignment condition is imposed.
-/

public section

namespace Cryptol.Bridge

open VCVio.Algorithms.Sha2
open Cryptol.Finite

private theorem pure_forIn_eq_foldl {A B : Type} (xs : List A) (step : B → A → B) (z : B) :
    (forIn xs z (fun i acc => pure (.yield (step acc i))) : Id B) = xs.foldl step z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.forIn_cons, pure_bind, List.foldl_cons] using ih (step z x)

private theorem range_fold_invariant {A : Type} (start count : Nat)
    (step : A → Nat → A) (inv : Nat → A → Prop) (initial : A)
    (hinit : inv start initial)
    (hstep : ∀ i, start ≤ i → i < start + count → ∀ x, inv i x → inv (i + 1) (step x i)) :
    inv (start + count) ((List.range' start count).foldl step initial) := by
  induction count with
  | zero => simpa using hinit
  | succ count ih =>
      rw [List.range'_concat, List.foldl_append]
      simp only [Nat.one_mul, List.foldl_cons, List.foldl_nil]
      exact hstep (start + count) (by omega) (by omega) _
        (ih (fun i hi hj x hx => hstep i hi (by omega) x hx))

/-- The actual loader loop is an ascending sequence of buffer writes. -/
theorem loadSchedule256_eq_fold (m : ByteArray) (base : Nat) :
    loadSchedule256 m base = (List.range' 0 16).foldl
      (fun w t => w.set! t (readWord256 m base t)) (Array.replicate 64 0) := by
  simp only [loadSchedule256, Std.Legacy.Range.forIn_eq_forIn_range', pure_forIn_eq_foldl]
  rfl

/-- The actual expansion loop visits each remaining schedule coordinate in order. -/
theorem expandSchedule256_eq_fold (initial : Array UInt32) :
    expandSchedule256 initial = (List.range' 16 48).foldl
      (fun w t => w.set! t (ssig1 w[t - 2]! + w[t - 7]! + ssig0 w[t - 15]! + w[t - 16]!))
      initial := by
  simp only [expandSchedule256, Std.Legacy.Range.forIn_eq_forIn_range', pure_forIn_eq_foldl]
  rfl

/-- The array's eight entries in the round register order. -/
@[expose] def arrayState (st : Array UInt32) : RoundState :=
  ⟨st[0]!, st[1]!, st[2]!, st[3]!, st[4]!, st[5]!, st[6]!, st[7]!⟩

/-- The actual round loop is the ordered fold of the round helper. -/
theorem runRounds256_eq_fold (st w : Array UInt32) :
    runRounds256 st w = (List.range' 0 64).foldl
      (fun s t => round256 s k[t]! w[t]!) (arrayState st) := by
  simp only [runRounds256, Std.Legacy.Range.forIn_eq_forIn_range', pure_forIn_eq_foldl]
  rfl

/-- Read the sixteen words through the same byte loader used by `compress`. -/
@[expose] def loadedBlock (m : ByteArray) (base : Nat) : Fin 16 → BitVec 32 :=
  fun i => (readWord256 m base i.val).toBitVec

/-- The buffer's size and its initialized prefix. -/
@[expose] def SchedulePrefix (words : Fin 64 → BitVec 32) (upto : Nat)
    (buffer : Array UInt32) : Prop :=
  buffer.size = 64 ∧ ∀ (i : Fin 64), i.val < upto → buffer[i.val]!.toBitVec = words i

private theorem get_set!_same (xs : Array UInt32) (i : Nat) (hi : i < xs.size) (x : UInt32) :
    (xs.set! i x)[i]! = x := by
  rw [Array.set!_eq_setIfInBounds,
    getElem!_pos (xs.setIfInBounds i x) i (by simpa using hi), Array.getElem_setIfInBounds hi]
  simp

private theorem get_set!_other (xs : Array UInt32) (i j : Nat) (hj : j < xs.size)
    (hne : i ≠ j) (x : UInt32) : (xs.set! i x)[j]! = xs[j]! := by
  rw [Array.set!_eq_setIfInBounds,
    getElem!_pos (xs.setIfInBounds i x) j (by simpa using hj),
    getElem!_pos xs j hj, Array.getElem_setIfInBounds hj]
  simp [hne]

/-- The loader initializes all sixteen input words and preserves the buffer size. -/
theorem loadSchedule256_prefix (m : ByteArray) (base : Nat) :
    SchedulePrefix (schedule256 (loadedBlock m base)) 16 (loadSchedule256 m base) := by
  rw [loadSchedule256_eq_fold]
  apply range_fold_invariant 0 16 _ (SchedulePrefix (schedule256 (loadedBlock m base)))
  · exact ⟨by simp, fun i hi => by omega⟩
  · intro t _ ht buffer hb
    refine ⟨by simpa using hb.1, ?_⟩
    intro i hi
    by_cases he : t = i.val
    · subst t
      rw [get_set!_same buffer i.val (by rw [hb.1]; exact i.isLt)]
      rw [schedule256, prefixValues_apply]
      simp only [scheduleStep, show i.val < 16 by omega, ↓reduceDIte, loadedBlock]
    · rw [get_set!_other buffer t i.val (by rw [hb.1]; exact i.isLt) he]
      exact hb.2 i (by omega)

/-- Expanding the initialized prefix computes every schedule coordinate. -/
theorem expandSchedule256_prefix (block : Fin 16 → BitVec 32) (initial : Array UInt32)
    (hinit : SchedulePrefix (schedule256 block) 16 initial) :
    SchedulePrefix (schedule256 block) 64 (expandSchedule256 initial) := by
  rw [expandSchedule256_eq_fold]
  apply range_fold_invariant 16 48 _ (SchedulePrefix (schedule256 block)) _ hinit
  intro t ht hbound buffer hb
  refine ⟨by simpa using hb.1, ?_⟩
  intro i hi
  by_cases he : t = i.val
  · subst t
    rw [get_set!_same buffer i.val (by rw [hb.1]; exact i.isLt)]
    have h2 := hb.2 ⟨i.val - 2, by omega⟩ (by change i.val - 2 < i.val; omega)
    have h7 := hb.2 ⟨i.val - 7, by omega⟩ (by change i.val - 7 < i.val; omega)
    have h15 := hb.2 ⟨i.val - 15, by omega⟩ (by change i.val - 15 < i.val; omega)
    have h16 := hb.2 ⟨i.val - 16, by omega⟩ (by change i.val - 16 < i.val; omega)
    rw [schedule256, prefixValues_apply]
    simp only [scheduleStep, show ¬ i.val < 16 by omega, ↓reduceDIte]
    rw [UInt32.toBitVec_add, UInt32.toBitVec_add, UInt32.toBitVec_add,
      ← smallSigma256One_eq, ← smallSigma256Zero_eq, h2, h7, h15, h16]
    rfl
  · rw [get_set!_other buffer t i.val (by rw [hb.1]; exact i.isLt) he]
    exact hb.2 i (by omega)

/-- The constants in the preserved Foundation dependency agree at every round. -/
theorem constants256_eq (i : Fin 64) : Foundation.constants256 i = k[i.val]!.toBitVec := by
  fin_cases i <;> decide

/-- Every initialized schedule yields the corresponding 64 native round updates. -/
theorem runRounds256_correct (st w : Array UInt32) (words : Fin 64 → BitVec 32)
    (hw : SchedulePrefix words 64 w) :
    stateBits (runRounds256 st w) = compressionRounds words (stateBits (arrayState st)) 64 := by
  rw [runRounds256_eq_fold]
  have h := range_fold_invariant 0 64 (fun s t => round256 s k[t]! w[t]!)
    (fun t s => stateBits s = compressionRounds words (stateBits (arrayState st)) t)
    (arrayState st) rfl ?_
  · exact h
  · intro t _ ht s hs
    change stateBits (round256 s k[t]! w[t]!) = compressionRound words t
      (compressionRounds words (stateBits (arrayState st)) t)
    rw [← round256_eq, Foundation.round256_denote, compressionRound]
    simp only [show t < 64 by omega, ↓reduceDIte]
    rw [constants256_eq, ← hs, hw.2 ⟨t, by omega⟩ (by omega)]

/-- The byte implementation and finite description agree, including feed-forward. -/
theorem compress_eq_native (st : Array UInt32) (m : ByteArray) (base : Nat) :
    compress st m base = Array.ofFn (fun i : Fin 8 => UInt32.ofBitVec
      (compressionNative (stateBits (arrayState st), loadedBlock m base) i)) := by
  have hw := expandSchedule256_prefix (loadedBlock m base) _ (loadSchedule256_prefix m base)
  have hr := runRounds256_correct st _ _ hw
  apply Array.ext
  · simp [compress, feedForward256]
  · intro i hleft hright
    have hi : i < 8 := by simpa [compress, feedForward256] using hleft
    have hfeed (j : Fin 8) : (compress st m base)[j.val]!.toBitVec =
        BitVec.add (stateBits (arrayState st) j)
          (stateBits (runRounds256 st (expandSchedule256 (loadSchedule256 m base))) j) := by
      fin_cases j <;> simp [compress, feedForward256, stateBits, arrayState]
    have hbits := hfeed ⟨i, hi⟩
    rw [getElem!_pos (compress st m base) i hleft, hr] at hbits
    rw [Array.getElem_ofFn]
    apply UInt32.toBitVec_inj.mp
    simpa only [UInt32.toBitVec_ofBitVec, compressionNative] using hbits

/-- Four bytes assemble to the big-endian bitvector used by Cryptol words. -/
theorem assembleWord256_eq (a b c d : UInt8) :
    (a.toUInt32 <<< 24 ||| b.toUInt32 <<< 16 ||| c.toUInt32 <<< 8 ||| d.toUInt32).toBitVec =
      a.toBitVec ++ b.toBitVec ++ c.toBitVec ++ d.toBitVec := by
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt8.toBitVec_toUInt32]
  symm
  simpa using (BitVec.setWidth_append_append_append_eq_shiftLeft_setWidth_or
    (w'''' := 32) (b := a.toBitVec) (b' := b.toBitVec) (b'' := c.toBitVec) (b''' := d.toBitVec))

/-- The selected block byte, with its bound supplied by the block-window hypothesis. -/
@[expose] def blockByte (m : ByteArray) (base : Nat) (h : base + 64 ≤ m.size)
    (i : Fin 64) : BitVec 8 := (m[base + i.val]'(by omega)).toBitVec

/-- Sixteen big-endian words decoded from exactly the chosen 64-byte window. -/
@[expose] def decodedBlock (m : ByteArray) (base : Nat) (h : base + 64 ≤ m.size) :
    Fin 16 → BitVec 32 := fun i =>
  blockByte m base h ⟨i.val * 4, by omega⟩ ++
    blockByte m base h ⟨i.val * 4 + 1, by omega⟩ ++
    blockByte m base h ⟨i.val * 4 + 2, by omega⟩ ++
    blockByte m base h ⟨i.val * 4 + 3, by omega⟩

/-- Every load reads an in-range byte and has the stated endianness, at any offset. -/
theorem loadedBlock_eq_decodedBlock (m : ByteArray) (base : Nat) (h : base + 64 ≤ m.size) :
    loadedBlock m base = decodedBlock m base h := by
  funext i
  unfold loadedBlock readWord256 decodedBlock blockByte
  dsimp only
  have h0 : base + i.val * 4 < m.size := by omega
  have h1 : base + i.val * 4 + 1 < m.size := by omega
  have h2 : base + i.val * 4 + 2 < m.size := by omega
  have h3 : base + i.val * 4 + 3 < m.size := by omega
  rw [getElem!_pos m _ h0, getElem!_pos m _ h1, getElem!_pos m _ h2, getElem!_pos m _ h3,
    assembleWord256_eq]
  simp only [Nat.add_assoc]

/-- Read an eight-word chaining state without default or out-of-range array accesses. -/
@[expose] def decodedState (st : Array UInt32) (h : st.size = 8) : Fin 8 → BitVec 32 :=
  fun i => (st[i.val]'(by omega)).toBitVec

/-- The register initialization agrees with all eight in-range state entries. -/
theorem stateBits_arrayState (st : Array UInt32) (h : st.size = 8) :
    stateBits (arrayState st) = decodedState st h := by
  funext i
  fin_cases i <;> simp [stateBits, arrayState, decodedState, getElem!_pos, h]

/-- The complete byte API correspondence, allowing nonzero and unaligned offsets. -/
theorem compress_eq_decoded (st : Array UInt32) (m : ByteArray) (base : Nat)
    (hst : st.size = 8) (hbytes : base + 64 ≤ m.size) :
    compress st m base = Array.ofFn (fun i : Fin 8 => UInt32.ofBitVec
      (compressionNative (decodedState st hst, decodedBlock m base hbytes) i)) := by
  rw [compress_eq_native, stateBits_arrayState st hst, loadedBlock_eq_decodedBlock m base hbytes]

end Cryptol.Bridge
