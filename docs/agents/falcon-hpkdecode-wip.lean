/-
WIP scaffolding for the `hpkDecode` round-trip (`pkDecode_pkEncode`), session 8 (paused).

STATUS: every declaration below is PROVEN, sorry-free, and compiles against the refactored
`LatticeCrypto/Falcon/Concrete/Encoding.lean` (where `pkEncode`/`pkDecode` now use
`for b in [0:n/4]` instead of `while`, because Lean's `while` lowers to an opaque `partial`
`Lean.Loop.forIn.loop` with no usable equational theory — see docs/agents/falcon-review.md §"B6"/codec notes).

This file is NOT part of any build target (it lives under docs/). It is a reference for the
session resuming `hpkDecode`: LIFT these lemmas into `Concrete/Encoding.lean` (adjust the
`import Mathlib`/`import Batteries` to Encoding.lean's narrower imports if the build allows),
then finish the THREE remaining pieces:

  REMAINING (decode side + assembly + wiring):
  1. `pkEncode_size (n) (hn4 : 4 ∣ n) (h) : (pkEncode n h).size = 7 * (n / 4)`
       — immediate from `pkEncode_eq_E` + `E_size` (n/4 groups × 7 bytes).
  2. `publicKeyBytes_extract (logn) (h) : (publicKeyBytes logn h).extract 1 size = pkEncode n h`
       — ByteArray extract-of-(#[hdr] ++ rest); mirror the just-proven `sigDecode_sigEncode`
         idiom in Encoding.lean (uses `ByteArray.extract_append_eq_right` + `byteArray_toList_eq`).
  3. `pkDecode_pkEncode (n) (hn4 : 4 ∣ n) (h) : pkDecode n (pkEncode n h) = some h`  ← MAIN
       — the pkDecode `for b in [0:n/4]` invariant. Plan:
         * `4∣n ⇒ needed = 7*(n/4) = (pkEncode…).size`, so the `size < needed` guard is false.
         * bytes read at `7*b+t` are `(gblock n h b).data[t]!` (via `pkEncode_eq_E` + `E_getElem`
           + `gblock_byte`).
         * those bytes decode (via `group_roundtrip`) to `h[4b..4b+3].val < modulus`, so the
           `≥ modulus` reject branch is DEAD (early `return none` never taken).
         * forIn invariant (reuse B6's `foldl_range_preserve`/`Std.Legacy.Range.forIn_eq_forIn_range'`
           + `List.forIn_pure_yield_eq_foldl` machinery from Instance.lean's proven B6 proofs):
           after the loop `result[k] = (h[k].val : Coeff)` ∀ k<n, hence
           `Vector.ofFn (result.getD · 0) = h` by `Vector.ext` + `(h[k].val : ZMod modulus) = h[k]`
           (`ZMod.natCast_val` / `ZMod.val_cast_of_lt` / `ZMod.cast_id`).
       Note the decode body early-returns `none` ⇒ the forIn state is `Option (Array Coeff)`-ish
       (`MProd`/`ForInStep`); show the `done` step is never taken on `pkEncode` input.
  4. Wire into `FPRBridge.concrete_verify_eq_verify`: discharge `hpkDecode` via
     `publicKeyBytes_extract ▸ pkDecode_pkEncode`; ADD a `(hn4 : 4 ∣ p.n)` hypothesis
     (required — `hn : p.n = 2^p.logn` admits logn∈{0,1} → n∈{1,2}, n%4≠0 → pkDecode = none).
     After this + the already-proven `sigDecode_sigEncode`, the bridge has NO semantic hyps left,
     only structural/numeric side-conditions (`hn`, `hsbytelen`, `hn_ovf`, `hn4`).

  Keep the standard-axioms-only discipline (no `native_decide`; `bv_decide` only if it stays
  `[propext, Classical.choice, Quot.sound]` — this scaffold uses the ℕ-arithmetic route instead).
-/
import Mathlib
import Batteries
import LatticeCrypto.Falcon.Concrete.Encoding

namespace Falcon.Concrete
open Falcon

private theorem toU8 (a : Nat) : a.toUInt8.toNat = a % 256 := by
  simp [Nat.toUInt8, Nat.toUInt8.eq_1]
private theorem lor_add (a b k : Nat) (hb : b < 2^k) (hd : 2^k ∣ a) : a ||| b = a + b := by
  obtain ⟨c, rfl⟩ := hd
  rw [mul_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq, mul_comm]
private theorem and3fff (a : Nat) : a &&& 0x3FFF = a % 2^14 := by
  have := Nat.and_two_pow_sub_one_eq_mod a 14
  norm_num at this ⊢; exact this

set_option maxHeartbeats 1000000 in
private theorem group_roundtrip (c0 c1 c2 c3 : Nat)
    (b0 : c0 < modulus) (b1 : c1 < modulus) (b2 : c2 < modulus) (b3 : c3 < modulus) :
    let d0 := (c0 >>> 6).toUInt8.toNat
    let d1 := ((c0 <<< 2) ||| (c1 >>> 12)).toUInt8.toNat
    let d2 := (c1 >>> 4).toUInt8.toNat
    let d3 := ((c1 <<< 4) ||| (c2 >>> 10)).toUInt8.toNat
    let d4 := (c2 >>> 2).toUInt8.toNat
    let d5 := ((c2 <<< 6) ||| (c3 >>> 8)).toUInt8.toNat
    let d6 := c3.toUInt8.toNat
    ((d0 <<< 6) ||| (d1 >>> 2)) = c0 ∧
    (((d1 <<< 12) ||| (d2 <<< 4) ||| (d3 >>> 4)) &&& 0x3FFF) = c1 ∧
    (((d3 <<< 10) ||| (d4 <<< 2) ||| (d5 >>> 6)) &&& 0x3FFF) = c2 ∧
    (((d5 <<< 8) ||| d6) &&& 0x3FFF) = c3 := by
  simp only [modulus] at b0 b1 b2 b3
  intro d0 d1 d2 d3 d4 d5 d6
  have hd0 : d0 = c0 / 64 := by
    show (c0 >>> 6).toUInt8.toNat = _; rw [toU8, Nat.shiftRight_eq_div_pow]; norm_num; omega
  have hd1 : d1 = (c0 * 4 + c1 / 4096) % 256 := by
    show ((c0 <<< 2) ||| (c1 >>> 12)).toUInt8.toNat = _
    rw [toU8, lor_add _ _ 2 (by rw [Nat.shiftRight_eq_div_pow]; omega)
        ⟨c0, by rw [Nat.shiftLeft_eq]; ring⟩, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hd2 : d2 = (c1 / 16) % 256 := by
    show (c1 >>> 4).toUInt8.toNat = _; rw [toU8, Nat.shiftRight_eq_div_pow]
  have hd3 : d3 = (c1 * 16 + c2 / 1024) % 256 := by
    show ((c1 <<< 4) ||| (c2 >>> 10)).toUInt8.toNat = _
    rw [toU8, lor_add _ _ 4 (by rw [Nat.shiftRight_eq_div_pow]; omega)
        ⟨c1, by rw [Nat.shiftLeft_eq]; ring⟩, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hd4 : d4 = (c2 / 4) % 256 := by
    show (c2 >>> 2).toUInt8.toNat = _; rw [toU8, Nat.shiftRight_eq_div_pow]
  have hd5 : d5 = (c2 * 64 + c3 / 256) % 256 := by
    show ((c2 <<< 6) ||| (c3 >>> 8)).toUInt8.toNat = _
    rw [toU8, lor_add _ _ 6 (by rw [Nat.shiftRight_eq_div_pow]; omega)
        ⟨c2, by rw [Nat.shiftLeft_eq]; ring⟩, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hd6 : d6 = c3 % 256 := by show c3.toUInt8.toNat = _; rw [toU8]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hd0, hd1, lor_add _ _ 6 (by rw [Nat.shiftRight_eq_div_pow]; omega)
        ⟨c0/64, by rw [Nat.shiftLeft_eq]; ring⟩, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    norm_num; omega
  · set e1 := (c0 * 4 + c1 / 4096) % 256 with he1
    set e2 := (c1 / 16) % 256 with he2
    set e3 := (c1 * 16 + c2 / 1024) % 256 with he3
    rw [hd1, hd2, hd3,
      lor_add (e1 <<< 12) (e2 <<< 4) 12 (by rw [Nat.shiftLeft_eq]; show e2 * 2^4 < 2^12; omega)
        ⟨e1, by rw [Nat.shiftLeft_eq]; ring⟩,
      lor_add (e1 <<< 12 + e2 <<< 4) (e3 >>> 4) 4 (by rw [Nat.shiftRight_eq_div_pow]; omega)
        ⟨e1 * 2^8 + e2, by rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]; ring⟩,
      and3fff, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    simp only [he1, he2, he3]; norm_num; omega
  · set e3 := (c1 * 16 + c2 / 1024) % 256 with he3
    set e4 := (c2 / 4) % 256 with he4
    set e5 := (c2 * 64 + c3 / 256) % 256 with he5
    rw [hd3, hd4, hd5,
      lor_add (e3 <<< 10) (e4 <<< 2) 10 (by rw [Nat.shiftLeft_eq]; show e4 * 2^2 < 2^10; omega)
        ⟨e3, by rw [Nat.shiftLeft_eq]; ring⟩,
      lor_add (e3 <<< 10 + e4 <<< 2) (e5 >>> 6) 2 (by rw [Nat.shiftRight_eq_div_pow]; omega)
        ⟨e3 * 2^8 + e4, by rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]; ring⟩,
      and3fff, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    simp only [he3, he4, he5]; norm_num; omega
  · rw [hd5, hd6, lor_add _ _ 8 (by omega) ⟨_, by rw [Nat.shiftLeft_eq]; ring⟩, and3fff,
      Nat.shiftLeft_eq]
    norm_num; omega



private def gblock (n : ℕ) (h : Rq n) (b : ℕ) : ByteArray :=
  let i := 4 * b
  let h0 := (h[i]!).val
  let h1 := (h[i+1]!).val
  let h2 := (h[i+2]!).val
  let h3 := (h[i+3]!).val
  ByteArray.mk #[ (h0 >>> 6).toUInt8, ((h0 <<< 2) ||| (h1 >>> 12)).toUInt8, (h1 >>> 4).toUInt8,
     ((h1 <<< 4) ||| (h2 >>> 10)).toUInt8, (h2 >>> 2).toUInt8,
     ((h2 <<< 6) ||| (h3 >>> 8)).toUInt8, h3.toUInt8 ]

private def encStep (n : ℕ) (h : Rq n) (out : ByteArray) (b : ℕ) : ByteArray :=
  let i := 4 * b
  let h0 := (h[i]!).val
  let h1 := (h[i+1]!).val
  let h2 := (h[i+2]!).val
  let h3 := (h[i+3]!).val
  ((((((out.push ((h0 >>> 6).toUInt8)).push (((h0 <<< 2) ||| (h1 >>> 12)).toUInt8)).push
    ((h1 >>> 4).toUInt8)).push (((h1 <<< 4) ||| (h2 >>> 10)).toUInt8)).push
    ((h2 >>> 2).toUInt8)).push (((h2 <<< 6) ||| (h3 >>> 8)).toUInt8)).push (h3.toUInt8)

private theorem gblock_size (n : ℕ) (h : Rq n) (b : ℕ) : (gblock n h b).size = 7 := rfl
private theorem gblock_data_size (n : ℕ) (h : Rq n) (b : ℕ) : (gblock n h b).data.size = 7 := rfl

private theorem encStep_eq_append (n : ℕ) (h : Rq n) (out : ByteArray) (b : ℕ) :
    encStep n h out b = out ++ gblock n h b := by
  apply ByteArray.ext
  simp only [encStep, gblock, ByteArray.data_push, ByteArray.data_append]
  rfl

private theorem encStep_size (n : ℕ) (h : Rq n) (out : ByteArray) (b : ℕ) :
    (encStep n h out b).size = out.size + 7 := by
  rw [encStep_eq_append, ByteArray.size_append, gblock_size]


private def E (n : ℕ) (h : Rq n) (m : ℕ) : ByteArray :=
  List.foldl (encStep n h) ByteArray.empty (List.range' 0 m)

private theorem E_succ (n : ℕ) (h : Rq n) (m : ℕ) :
    E n h (m+1) = encStep n h (E n h m) m := by
  simp only [E, List.range'_concat, List.foldl_concat]
  norm_num

private theorem E_size (n : ℕ) (h : Rq n) (m : ℕ) : (E n h m).size = 7 * m := by
  induction m with
  | zero => rfl
  | succ k ih => rw [E_succ, encStep_size, ih]; ring


private theorem E_getElem (n : ℕ) (h : Rq n) (m : ℕ) :
    ∀ b, b < m → ∀ t, t < 7 → (E n h m).data[7 * b + t]! = (gblock n h b).data[t]! := by
  induction m with
  | zero => intro b hb; omega
  | succ k ih =>
    intro b hb t ht
    rw [E_succ, encStep_eq_append, ByteArray.data_append]
    rcases Nat.lt_or_ge b k with hbk | hbk
    · -- b < k : append_left into E k
      have hlt : 7 * b + t < (E n h k).data.size := by
        rw [← ByteArray.size, E_size]; omega
      rw [getElem!_pos _ (7*b+t) (by rw [Array.size_append]; omega),
          Array.getElem_append_left hlt, ← getElem!_pos _ (7*b+t) hlt]
      exact ih b hbk t ht
    · -- b = k
      have hbeq : b = k := by omega
      subst hbeq
      have hsz : (E n h b).data.size = 7 * b := by rw [← ByteArray.size, E_size]
      have hidx : 7 * b + t = (E n h b).data.size + t := by rw [hsz]
      rw [hidx,
          getElem!_pos _ ((E n h b).data.size + t)
            (by rw [Array.size_append, gblock_data_size]; omega),
          getElem!_pos (gblock n h b).data t (by rw [gblock_data_size]; exact ht),
          Array.getElem_append_right (by omega)]
      congr 1
      omega


private theorem pkEncode_eq_E (n : ℕ) (h : Rq n) (hn : n % 4 = 0) :
    pkEncode n h = E n h (n / 4) := by
  unfold pkEncode E
  have hb : (n % 4 != 0) = false := by simp [hn]
  simp only [Id.run, bind_pure_comp, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.div_one, map_pure,
    Nat.add_sub_cancel, hb, Bool.false_eq_true, if_false]
  simp only [List.forIn_pure_yield_eq_foldl, pure_bind, bind_pure]
  rfl


-- explicit bytes of gblock
private theorem gblock_byte (n : ℕ) (h : Rq n) (b : ℕ) :
    let i := 4 * b
    let c0 := (h[i]!).val; let c1 := (h[i+1]!).val
    let c2 := (h[i+2]!).val; let c3 := (h[i+3]!).val
    (gblock n h b).data[0]! = (c0 >>> 6).toUInt8 ∧
    (gblock n h b).data[1]! = ((c0 <<< 2) ||| (c1 >>> 12)).toUInt8 ∧
    (gblock n h b).data[2]! = (c1 >>> 4).toUInt8 ∧
    (gblock n h b).data[3]! = ((c1 <<< 4) ||| (c2 >>> 10)).toUInt8 ∧
    (gblock n h b).data[4]! = (c2 >>> 2).toUInt8 ∧
    (gblock n h b).data[5]! = ((c2 <<< 6) ||| (c3 >>> 8)).toUInt8 ∧
    (gblock n h b).data[6]! = c3.toUInt8 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Falcon.Concrete
