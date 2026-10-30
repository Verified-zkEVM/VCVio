/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.Basic
public import VCVio.Algorithms.Sha2
public import VCVio.Algorithms.Encoding

/-!
# The leanSeal byte encoding of the pointer-chain puzzle

leanSeal v1 instantiates the pointer-chain puzzle (`VCVio/Schemes/PointerChainPuzzle/Basic.lean`)
with SHA-256 over byte strings. This file gives its byte-level programs, written over an arbitrary
byte-answer function `h : ByteArray → Bytes 32` and instantiated with `Sha2.sha256` (`sha256`),
and proves that the typed construction computes them.

States, contexts and keys are `Bytes 32`, salts `Bytes 16` and links `Bytes b` for a link width
`1 ≤ b ≤ 32`, with bytewise XOR as the group operation. With the length-prefixed labelled hash
`TH(label, x) = h(u8(len label) ‖ label ‖ x)` and the one-based chain index `be32(i + 1)` of the
zero-based chain `i`, the six typed oracles are answered by

| Oracle   | Answer                                          |
|----------|-------------------------------------------------|
| `start`  | `TH("leanseal/v1/start", ctx ‖ be32(i + 1) ‖ x)` |
| `step`   | `h(s ‖ salt ‖ be32(i + 1))`, 52 bytes of input  |
| `mask`   | the first `b` bytes of `TH("leanseal/v1/mask", ctx ‖ y)` |
| `acc`    | `TH("leanseal/v1/acc", a ‖ y)`                  |
| `key`    | `TH("leanseal/v1/key", ctx ‖ a)`                |
| `commit` | `TH("leanseal/v1/commit", ctx ‖ K)`             |

and `ctx = u8(1) ‖ u8(b) ‖ 0x0000 ‖ be32(n) ‖ be64(m) ‖ salt` is bytes `[4, 36)` of the puzzle
encoding, which is also the initial accumulator. The puzzle encoding is the magic `"LSPZ"`, `ctx`,
the commitment and the `n` links.

## Main statements

* `simulateQ_gen_eq`, `simulateQ_genWith_eq`, `simulateQ_derive_eq`, `simulateQ_solve_eq`: the
  typed generator, the key-deriving solver and the checked solver, with every oracle answered
  through the byte encoding by `h`, compute the byte-level `gen`, `genWith`, `derive` and `solve`
  at `h`; the solvers agree on every puzzle, not only on generated ones.
* `decode_encode`: decoding an encoded puzzle with valid parameters gives it back.
* `solve_genWith`, `solveBytes_generate`: the byte-level solver recovers the generated key, at
  every byte-answer function.
* `simulateQ_solve_eq_solveBytes`: the typed solver computes the byte-level solver run on the
  encoded puzzle.
-/

public section

open OracleSpec OracleComp VCVio.Algorithms

namespace PointerChainPuzzle.LeanSeal

/-! ## Fixed-width bytes -/

/-- Byte strings of length `k`. Addition is bytewise XOR. -/
@[ext]
structure Bytes (k : ℕ) where
  /-- The bytes. -/
  toVector : Vector UInt8 k
  deriving DecidableEq

namespace Bytes

variable {k : ℕ}

/-- The bytes as a list. -/
@[expose]
def toList (x : Bytes k) : List UInt8 := x.toVector.toList

/-- The bytes as a byte array. -/
@[expose]
def toByteArray (x : Bytes k) : ByteArray := ⟨x.toVector.toArray⟩

/-- The `k` bytes of `l` from offset `off`, with zeros past its end. -/
@[expose]
def read (l : List UInt8) (off : ℕ) : Bytes k := ⟨Vector.ofFn fun i => l.getD (off + i) 0⟩

/-- The first `k` bytes of `x`, with zeros past its end. -/
@[expose]
def take {k' : ℕ} (x : Bytes k') : Bytes k := read x.toList 0

/-- Byte strings of length `k` are byte vectors of length `k`. -/
@[expose]
def equivVector : Bytes k ≃ Vector UInt8 k where
  toFun := toVector
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma length_toList (x : Bytes k) : x.toList.length = k := by simp [toList]

lemma getElem_toList (x : Bytes k) (i : ℕ) (hi : i < x.toList.length) :
    x.toList[i] = x.toVector[i]'(by simpa using hi) := by
  simp [toList]

lemma ext_getElem {x y : Bytes k} (h : ∀ i (hi : i < k), x.toVector[i] = y.toVector[i]) :
    x = y :=
  Bytes.ext (Vector.ext h)

lemma read_append_left {l₁ l₂ : List UInt8} {off : ℕ} (h : off + k ≤ l₁.length) :
    (read (l₁ ++ l₂) off : Bytes k) = read l₁ off :=
  ext_getElem fun i hi => by
    simp only [read, Vector.getElem_ofFn, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]

lemma read_append_right {l₁ l₂ : List UInt8} {off : ℕ} (h : l₁.length ≤ off) :
    (read (l₁ ++ l₂) off : Bytes k) = read l₂ (off - l₁.length) :=
  ext_getElem fun i hi => by
    simp only [read, Vector.getElem_ofFn, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    congr 2
    omega

@[simp] lemma read_toList (x : Bytes k) : (read x.toList 0 : Bytes k) = x :=
  ext_getElem fun i hi => by
    simp [read, toList, List.getD_eq_getElem?_getD]

instance : Inhabited (Bytes k) := ⟨⟨Vector.replicate k 0⟩⟩

instance : Finite (Bytes k) := Finite.of_equiv _ equivVector.symm

noncomputable instance : Fintype (Bytes k) := Fintype.ofFinite _

instance : SampleableType (Bytes k) := SampleableType.ofEquiv equivVector.symm

instance : Zero (Bytes k) := ⟨⟨Vector.replicate k 0⟩⟩

instance : Add (Bytes k) := ⟨fun x y => ⟨Vector.zipWith (· ^^^ ·) x.toVector y.toVector⟩⟩

instance : Neg (Bytes k) := ⟨id⟩

instance : Sub (Bytes k) := ⟨(· + ·)⟩

@[simp] lemma getElem_zero (i : ℕ) (hi : i < k) : (0 : Bytes k).toVector[i] = 0 := by
  simp [OfNat.ofNat, Zero.zero]

@[simp] lemma getElem_add (x y : Bytes k) (i : ℕ) (hi : i < k) :
    (x + y).toVector[i] = x.toVector[i] ^^^ y.toVector[i] := by
  simp [HAdd.hAdd, Add.add]

lemma neg_eq (x : Bytes k) : -x = x := rfl

lemma sub_eq_add (x y : Bytes k) : x - y = x + y := rfl

instance : AddCommGroup (Bytes k) where
  add_assoc x y z := ext_getElem fun i hi => by simp [UInt8.xor_assoc]
  zero_add x := ext_getElem fun i hi => by simp
  add_zero x := ext_getElem fun i hi => by simp
  add_comm x y := ext_getElem fun i hi => by simp [UInt8.xor_comm]
  neg_add_cancel x := ext_getElem fun i hi => by simp [neg_eq]
  sub_eq_add_neg _ _ := rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

end Bytes

/-! ## Hashing -/

section Hash

variable (h : ByteArray → Bytes 32) {b n : ℕ}

/-- SHA-256 as a byte-answer function. -/
@[expose]
def sha256 (x : ByteArray) : Bytes 32 := ⟨⟨(Sha2.sha256 x).data, Sha2.sha256_size x⟩⟩

/-- `x` in `w` bytes, big-endian. -/
@[expose]
def be (w x : ℕ) : ByteArray := ⟨(Encoding.natToBytesBE x w).toArray⟩

/-- The labelled hash `TH(label, x) = h(u8(len label) ‖ label ‖ x)`. -/
@[expose]
def TH (label : String) (x : ByteArray) : Bytes 32 :=
  h (ByteArray.mk #[label.toUTF8.size.toUInt8] ++ label.toUTF8 ++ x)

/-- The start `s_{i+1} = TH("leanseal/v1/start", ctx ‖ be32(i + 1) ‖ x)` of the zero-based chain
`i` from its link `x`. -/
@[expose]
def start (ctx : Bytes 32) (i : Fin n) (x : Bytes b) : Bytes 32 :=
  TH h "leanseal/v1/start" (ctx.toByteArray ++ be 4 (i + 1) ++ x.toByteArray)

/-- The chain step `F_{i+1}(s) = h(s ‖ salt ‖ be32(i + 1))` of the zero-based chain `i`. -/
@[expose]
def step (salt : Bytes 16) (i : Fin n) (s : Bytes 32) : Bytes 32 :=
  h (s.toByteArray ++ salt.toByteArray ++ be 4 (i + 1))

/-- The mask of a chain end `y`: the first `b` bytes of `TH("leanseal/v1/mask", ctx ‖ y)`. -/
@[expose]
def mask (ctx y : Bytes 32) : Bytes b :=
  (TH h "leanseal/v1/mask" (ctx.toByteArray ++ y.toByteArray)).take

/-- Absorb the chain end `y` into the accumulator `a`: `TH("leanseal/v1/acc", a ‖ y)`. -/
@[expose]
def acc (a y : Bytes 32) : Bytes 32 :=
  TH h "leanseal/v1/acc" (a.toByteArray ++ y.toByteArray)

/-- The key from the final accumulator `a`: `TH("leanseal/v1/key", ctx ‖ a)`. -/
@[expose]
def key (ctx a : Bytes 32) : Bytes 32 :=
  TH h "leanseal/v1/key" (ctx.toByteArray ++ a.toByteArray)

/-- The commitment to the key `K`: `TH("leanseal/v1/commit", ctx ‖ K)`. -/
@[expose]
def commit (ctx k : Bytes 32) : Bytes 32 :=
  TH h "leanseal/v1/commit" (ctx.toByteArray ++ k.toByteArray)

/-- The six typed oracles answered through the byte encoding by `h`. -/
@[expose]
def oracles : Oracles n (Bytes 32) (Bytes b) (Bytes 16) (Bytes 32) where
  start := start h
  step := step h
  mask := mask h
  acc := acc h
  key := key h
  commit := commit h

/-- The typed oracles answered through the byte encoding by `h`, round by round, with uniform
queries passed through. -/
abbrev impl (b n : ℕ) :
    QueryImpl (unifSpec + (oracleSpec n (Bytes 32) (Bytes b) (Bytes 16) (Bytes 32)).batch)
      ProbComp :=
  QueryImpl.batch' (unifFwdAnswerImpl (oracles (b := b) (n := n) h).toImpl)

end Hash

/-! ## Parameters and the context -/

/-- The parameter ranges of leanSeal v1: `1 ≤ b ≤ 32`, `1 ≤ n ≤ 2^20`, `1 ≤ m ≤ 2^48` and
`n m ≤ 2^60`. -/
@[expose]
def Valid (b n m : ℕ) : Prop :=
  1 ≤ b ∧ b ≤ 32 ∧ 1 ≤ n ∧ n ≤ 2 ^ 20 ∧ 1 ≤ m ∧ m ≤ 2 ^ 48 ∧ n * m ≤ 2 ^ 60

instance (b n m : ℕ) : Decidable (Valid b n m) :=
  inferInstanceAs (Decidable (1 ≤ b ∧ b ≤ 32 ∧ 1 ≤ n ∧ n ≤ 2 ^ 20 ∧ 1 ≤ m ∧ m ≤ 2 ^ 48 ∧
    n * m ≤ 2 ^ 60))

lemma Valid.neZero {b n m : ℕ} (hv : Valid b n m) : NeZero n := ⟨by unfold Valid at hv; omega⟩

/-- The bytes of `ctx`: version `1`, `b`, two reserved zero bytes, `be32(n)`, `be64(m)` and the
salt. -/
@[expose]
def ctxList (b n m : ℕ) (salt : Bytes 16) : List UInt8 :=
  [1, b.toUInt8, 0, 0] ++ Encoding.natToBytesBE n 4 ++ Encoding.natToBytesBE m 8 ++ salt.toList

@[simp] lemma length_ctxList (b n m : ℕ) (salt : Bytes 16) : (ctxList b n m salt).length = 32 := by
  simp [ctxList]

/-- The context `ctx` of a puzzle with parameters `b`, `n`, `m` and the given salt. -/
@[expose]
def ctx (b n m : ℕ) (salt : Bytes 16) : Bytes 32 :=
  ⟨⟨(ctxList b n m salt).toArray, by simp⟩⟩

/-! ## Generation and solving -/

/-- A leanSeal puzzle with link width `b` and `n` chains, as a record. -/
abbrev Puzzle (b n : ℕ) := PointerChainPuzzle.Puzzle n (Bytes 32) (Bytes b) (Bytes 16)

section Programs

variable (h : ByteArray → Bytes 32) {b n : ℕ} (m : ℕ)

/-- The state `F_{i+1}^j(s_{i+1})` of the zero-based chain `i` after `j` steps from its link. -/
@[expose]
def chainAt (ctx : Bytes 32) (salt : Bytes 16) (i : Fin n) (x : Bytes b) (j : ℕ) : Bytes 32 :=
  (step h salt i)^[j] (start h ctx i x)

/-- The accumulator after the first `k` chain ends `ys`, from `a`: `a_{k+1} = acc(a_k, y_{k+1})`,
stopping at the last chain. -/
@[expose]
def accs (a : Bytes 32) (ys : Fin n → Bytes 32) : ℕ → Bytes 32
  | 0 => a
  | k + 1 => if hk : k < n then acc h (accs a ys k) (ys ⟨k, hk⟩) else accs a ys k

/-- The puzzle and key generated from the salt and the links `xs` (SPEC §4). -/
@[expose]
def genWith [NeZero n] (salt : Bytes 16) (xs : Fin n → Bytes b) : Puzzle b n × Bytes 32 :=
  let c := ctx b n m salt
  let ys := Vector.ofFn fun i : Fin n => chainAt h c salt i (xs i) m
  let K := key h c (accs h c (fun i : Fin n => ys[i]) n)
  (⟨salt, commit h c K, xs 0, fun i => mask h c ys[chainOf i] + xs (nextChain i)⟩, K)

/-- The generator: draw the salt and the links uniformly, and generate the puzzle and its key. -/
@[expose]
def gen [NeZero n] : ProbComp (Puzzle b n × Bytes 32) := do
  let salt ← $ᵗ Bytes 16
  let xs ← $ᵗ (Fin n → Bytes b)
  return genWith h m salt xs

/-- Run chains `k, k + 1, …` before the last one, at most `r` of them, from the accumulator and
link `st`: each chain end is absorbed and unmasks the next link (SPEC §5, step 2). -/
@[expose]
def unmask (puzzle : Puzzle b n) : ℕ → ℕ → Bytes 32 × Bytes b → Bytes 32 × Bytes b
  | 0, _, st => st
  | r + 1, k, st =>
      if hk : k < n - 1 then
        let c := ctx b n m puzzle.salt
        let y := chainAt h c puzzle.salt (⟨k, by omega⟩ : Fin n) st.2 m
        unmask puzzle r (k + 1) (acc h st.1 y, mask h c y + puzzle.maskedLinks ⟨k, hk⟩)
      else st

/-- The key-deriving solver (SPEC §5, steps 1 to 3). -/
@[expose]
def derive [NeZero n] (puzzle : Puzzle b n) : Bytes 32 :=
  let c := ctx b n m puzzle.salt
  let st := unmask h m puzzle (n - 1) 0 (c, puzzle.firstLink)
  key h c (acc h st.1 (chainAt h c puzzle.salt (lastChain : Fin n) st.2 m))

/-- The checked solver: the derived key if it matches the commitment, `none` otherwise. -/
@[expose]
def solve [NeZero n] (puzzle : Puzzle b n) : Option (Bytes 32) :=
  let K := derive h m puzzle
  if commit h (ctx b n m puzzle.salt) K = puzzle.commitment then some K else none

end Programs

/-! ## The puzzle encoding -/

section Encoding

variable {b n : ℕ}

/-- The magic `"LSPZ"`. -/
@[expose]
def magic : List UInt8 := [0x4c, 0x53, 0x50, 0x5a]

/-- The link of the zero-based chain `i`: `x_1` for `i = 0`, then the masked links. -/
@[expose]
def linkAt (puzzle : Puzzle b n) (i : ℕ) : Bytes b :=
  if i = 0 then puzzle.firstLink
  else if hi : i - 1 < n - 1 then puzzle.maskedLinks ⟨i - 1, hi⟩ else 0

/-- The `n b` link bytes `x_1 ‖ z_1 ‖ … ‖ z_{n-1}`. -/
@[expose]
def linkBytes (puzzle : Puzzle b n) : List UInt8 :=
  (List.range (n * b)).map fun j => (linkAt puzzle (j / b)).toList.getD (j % b) 0

/-- The puzzle encoding as a list of bytes (SPEC §6.1). -/
@[expose]
def encodeList (m : ℕ) (puzzle : Puzzle b n) : List UInt8 :=
  magic ++ ctxList b n m puzzle.salt ++ puzzle.commitment.toList ++ linkBytes puzzle

/-- The puzzle encoding (SPEC §6.1): `68 + n b` bytes. -/
@[expose]
def encode (m : ℕ) (puzzle : Puzzle b n) : ByteArray := ⟨(encodeList m puzzle).toArray⟩

/-- The number with big-endian bytes `l`. -/
@[expose]
def beNat : List UInt8 → ℕ
  | [] => 0
  | c :: l => c.toNat * 256 ^ l.length + beNat l

/-- A decoded puzzle with its parameters. -/
structure Decoded where
  /-- The link width. -/
  b : ℕ
  /-- The number of chains. -/
  n : ℕ
  /-- The number of steps per chain. -/
  m : ℕ
  /-- The parameters are in range. -/
  valid : Valid b n m
  /-- The puzzle. -/
  puzzle : Puzzle b n

/-- Decode the bytes `l` as a puzzle with parameters `b`, `n`, `m`: check the magic, the version,
the reserved bytes, the parameter ranges and the exact length, then read the fields. -/
@[expose]
def decodeWith (b n m : ℕ) (l : List UInt8) : Option Decoded :=
  if hl : l.take 4 = magic ∧ l.getD 4 0 = 1 ∧ l.getD 6 0 = 0 ∧ l.getD 7 0 = 0 ∧
      Valid b n m ∧ l.length = 68 + n * b then
    some
      { b, n, m
        valid := hl.2.2.2.2.1
        puzzle :=
          { salt := Bytes.read l 20
            commitment := Bytes.read l 36
            firstLink := Bytes.read l 68
            maskedLinks i := Bytes.read l (68 + b * (i + 1)) } }
  else none

/-- Decode a puzzle (SPEC §6.1), reading its parameters from the header: `none` on a wrong magic,
version or reserved byte, out-of-range parameters, or a length other than `68 + n b`. -/
@[expose]
def decode (bs : ByteArray) : Option Decoded :=
  let l := bs.data.toList
  decodeWith (l.getD 5 0).toNat (beNat ((l.drop 8).take 4)) (beNat ((l.drop 12).take 8)) l

/-- Decode a puzzle and solve it with the checked solver: `none` if it is malformed or the derived
key does not match the commitment. -/
@[expose]
def solveBytes (h : ByteArray → Bytes 32) (bs : ByteArray) : Option (Bytes 32) :=
  match decode bs with
  | none => none
  | some d => haveI := d.valid.neZero; solve h d.m d.puzzle

/-- The puzzle bytes and key generated from the salt and the links `xs`. -/
@[expose]
def generate (h : ByteArray → Bytes 32) (m : ℕ) [NeZero n] (salt : Bytes 16)
    (xs : Fin n → Bytes b) : ByteArray × Bytes 32 :=
  let r := genWith h m salt xs
  (encode m r.1, r.2)

lemma natToBytesBE_succ (x w : ℕ) :
    Encoding.natToBytesBE x (w + 1) =
      UInt8.ofNat (x / 256 ^ w % 256) :: Encoding.natToBytesBE x w := by
  simp only [Encoding.natToBytesBE, List.range_succ_eq_map, List.map_cons, List.map_map,
    Nat.add_sub_cancel, Nat.sub_zero]
  congr 2
  funext i
  simp only [Function.comp_apply, Nat.sub_sub, Nat.succ_eq_add_one, Nat.add_comm 1 i]

lemma beNat_natToBytesBE (x w : ℕ) : beNat (Encoding.natToBytesBE x w) = x % 256 ^ w := by
  induction w with
  | zero => simp [Encoding.natToBytesBE, beNat, Nat.mod_one]
  | succ w ih =>
      rw [natToBytesBE_succ, beNat, ih, Encoding.natToBytesBE_length, UInt8.toNat_ofNat',
        show (2 : ℕ) ^ 8 = 256 from rfl, Nat.mod_mod, Nat.mod_pow_succ]
      ring

@[simp] lemma length_linkBytes (puzzle : Puzzle b n) : (linkBytes puzzle).length = n * b := by
  simp [linkBytes]

lemma read_linkBytes (puzzle : Puzzle b n) {i : ℕ} (hi : i < n) :
    (Bytes.read (linkBytes puzzle) (b * i) : Bytes b) = linkAt puzzle i := by
  refine Bytes.ext_getElem fun j hj => ?_
  have hlt : b * i + j < n * b := by
    calc b * i + j < b * i + b := by omega
      _ = b * (i + 1) := by ring
      _ ≤ b * n := Nat.mul_le_mul_left _ hi
      _ = n * b := Nat.mul_comm _ _
  have hdiv : (b * i + j) / b = i := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj, Nat.add_zero]
  have hmod : (b * i + j) % b = j := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  simp [Bytes.read, linkBytes, List.getD_eq_getElem?_getD, hlt, hdiv, hmod,
    Bytes.getElem_toList, hj]

lemma length_encodeList (m : ℕ) (puzzle : Puzzle b n) :
    (encodeList m puzzle).length = 68 + n * b := by
  simp [encodeList, magic]
  omega

lemma length_magic_ctxList_commitment (m : ℕ) (puzzle : Puzzle b n) :
    (magic ++ ctxList b n m puzzle.salt ++ puzzle.commitment.toList).length = 68 := by
  simp [magic]

lemma read_encodeList_salt (m : ℕ) (puzzle : Puzzle b n) :
    (Bytes.read (encodeList m puzzle) 20 : Bytes 16) = puzzle.salt := by
  rw [encodeList, Bytes.read_append_left (by simp [magic]),
    Bytes.read_append_left (by simp [magic]), Bytes.read_append_right (by simp [magic]), ctxList,
    Bytes.read_append_right (by simp [magic])]
  simp [magic]

lemma read_encodeList_commitment (m : ℕ) (puzzle : Puzzle b n) :
    (Bytes.read (encodeList m puzzle) 36 : Bytes 32) = puzzle.commitment := by
  rw [encodeList, Bytes.read_append_left (by simp [magic]),
    Bytes.read_append_right (by simp [magic])]
  simp [magic]

lemma read_encodeList_link (m : ℕ) (puzzle : Puzzle b n) {i : ℕ} (hi : i < n) :
    (Bytes.read (encodeList m puzzle) (68 + b * i) : Bytes b) = linkAt puzzle i := by
  rw [encodeList, Bytes.read_append_right (by simp [magic]),
    length_magic_ctxList_commitment, Nat.add_sub_cancel_left, read_linkBytes _ hi]

lemma decodeWith_encodeList {m : ℕ} (hv : Valid b n m) (puzzle : Puzzle b n) :
    decodeWith b n m (encodeList m puzzle) = some ⟨b, n, m, hv, puzzle⟩ := by
  have hn : 0 < n := (hv.neZero).pos
  have hf : (Bytes.read (encodeList m puzzle) 68 : Bytes b) = puzzle.firstLink := by
    simpa [linkAt] using read_encodeList_link m puzzle (i := 0) hn
  have hz : (fun i : Fin (n - 1) => (Bytes.read (encodeList m puzzle) (68 + b * (i + 1)) :
      Bytes b)) = puzzle.maskedLinks := by
    funext i
    rw [read_encodeList_link m puzzle (by omega)]
    simp [linkAt]
  have h0 : (encodeList m puzzle).take 4 = magic := by simp [encodeList, magic]
  have h4 : (encodeList m puzzle).getD 4 0 = 1 := by simp [encodeList, magic, ctxList]
  have h6 : (encodeList m puzzle).getD 6 0 = 0 := by simp [encodeList, magic, ctxList]
  have h7 : (encodeList m puzzle).getD 7 0 = 0 := by simp [encodeList, magic, ctxList]
  simp only [decodeWith, h0, h4, h6, h7, hv, length_encodeList, and_self, ↓reduceDIte,
    read_encodeList_salt, read_encodeList_commitment, hf, hz]

/-- Decoding an encoded puzzle with valid parameters gives it back. -/
theorem decode_encode {m : ℕ} (hv : Valid b n m) (puzzle : Puzzle b n) :
    decode (encode m puzzle) = some ⟨b, n, m, hv, puzzle⟩ := by
  have hv' := hv
  unfold Valid at hv'
  have hb : ((encodeList m puzzle).getD 5 0).toNat = b := by
    simp [encodeList, magic, ctxList]
    omega
  have hn : beNat (((encodeList m puzzle).drop 8).take 4) = n := by
    simp [encodeList, magic, ctxList, beNat_natToBytesBE]
    omega
  have hm : beNat (((encodeList m puzzle).drop 12).take 8) = m := by
    simp [encodeList, magic, ctxList, beNat_natToBytesBE]
    omega
  simp only [decode, encode, List.toList_toArray]
  rw [hb, hn, hm, decodeWith_encodeList hv]

end Encoding

/-! ## Refinement -/

section Refinement

variable (h : ByteArray → Bytes 32) {b n : ℕ} (m : ℕ)

lemma accFold_oracles (a : Bytes 32) (ys : Fin n → Bytes 32) (k : ℕ) :
    accFold (oracles (b := b) h) a ys k = accs h a ys k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [accFold, accs, ih]; rfl

lemma honestPuzzle_oracles [NeZero n] (salt : Bytes 16) (xs : Fin n → Bytes b) :
    honestPuzzle m (ctx b n m) id (oracles h) salt xs = (genWith h m salt xs).1 := by
  simp only [genWith, honestPuzzle, honestKey, accAfter, accFold_oracles, chainEnd, chainState,
    Fin.getElem_fin, Vector.getElem_ofFn]
  rfl

lemma honestKey_oracles [NeZero n] (salt : Bytes 16) (xs : Fin n → Bytes b) :
    honestKey m (ctx b n m) id (oracles h) salt xs = (genWith h m salt xs).2 := by
  simp only [genWith, honestKey, accAfter, accFold_oracles, Fin.getElem_fin,
    Vector.getElem_ofFn]
  rfl

/-- The typed generator on given coins, with the oracles answered through the byte encoding by
`h`, computes the byte-level generator at `h`. -/
theorem simulateQ_genWith_eq [NeZero n] (salt : Bytes 16) (xs : Fin n → Bytes b) :
    simulateQ (impl h b n) (PointerChainPuzzle.genWith m (ctx b n m) id salt xs) =
      pure (genWith h m salt xs) := by
  rw [simulateQ_genWith, honestPuzzle_oracles, honestKey_oracles]

lemma simulateQ_impl_liftM {α : Type} (oa : ProbComp α) :
    simulateQ (impl h b n) (liftM oa) = oa := by
  simp [impl, unifFwdAnswerImpl, QueryImpl.simulateQ_add_liftM_left]

/-- The typed generator, with the oracles answered through the byte encoding by `h`, is the
byte-level generator at `h`. -/
theorem simulateQ_gen_eq [NeZero n] :
    simulateQ (impl h b n) (PointerChainPuzzle.gen m (ctx b n m) id (L := Bytes b)) =
      gen h m := by
  rw [PointerChainPuzzle.gen]
  simp [simulateQ_genWith_eq, simulateQ_impl_liftM, gen]

lemma simulateQ_maskedChains (puzzle : Puzzle b n) (r k : ℕ) (st : Bytes 32 × Bytes b) :
    simulateQ (impl h b n) (maskedChains m (ctx b n m) puzzle r k st) =
      pure (unmask h m puzzle r k st) := by
  induction r generalizing k st with
  | zero => rfl
  | succ r ih =>
      rw [maskedChains, unmask]
      split_ifs with hk
      · simp only [simulateQ_bind, simulateQ_runChain, pure_bind, simulateQ_queryRound₂]
        rw [ih]
        exact congrArg (fun st => pure (unmask h m puzzle r (k + 1) st))
          (Prod.ext rfl (add_comm _ _))
      · rfl

/-- The typed key-deriving solver, with the oracles answered through the byte encoding by `h`,
computes the byte-level key-deriving solver at `h`, on every puzzle. -/
theorem simulateQ_derive_eq [NeZero n] (puzzle : Puzzle b n) :
    simulateQ (impl h b n) (PointerChainPuzzle.derive m (ctx b n m) id puzzle) =
      pure (derive h m puzzle) := by
  rw [PointerChainPuzzle.derive]
  simp only [simulateQ_bind, simulateQ_maskedChains, pure_bind, simulateQ_runChain,
    simulateQ_queryPoint]
  rfl

/-- The typed checked solver, with the oracles answered through the byte encoding by `h`,
computes the byte-level checked solver at `h`, on every puzzle. -/
theorem simulateQ_solve_eq [NeZero n] (puzzle : Puzzle b n) :
    simulateQ (impl h b n) (PointerChainPuzzle.solve m (ctx b n m) id puzzle) =
      pure (solve h m puzzle) := by
  rw [PointerChainPuzzle.solve, simulateQ_bind, simulateQ_derive_eq, pure_bind, simulateQ_check]
  rfl

/-- The byte-level checked solver recovers the generated key, at every byte-answer function. -/
theorem solve_genWith [NeZero n] (salt : Bytes 16) (xs : Fin n → Bytes b) :
    solve h m (genWith h m salt xs).1 = some (genWith h m salt xs).2 := by
  have hs := simulateQ_solve (m := m) (mkCtx := ctx b n m) (initAcc := id) (O := oracles h) salt xs
  rw [honestPuzzle_oracles, honestKey_oracles, simulateQ_solve_eq] at hs
  exact (OracleComp.pure_inj _ _).1 hs

/-- The byte-level solver on an encoded puzzle with valid parameters is the checked solver on the
puzzle. -/
theorem solveBytes_encode (hv : Valid b n m) [NeZero n] (puzzle : Puzzle b n) :
    solveBytes h (encode m puzzle) = solve h m puzzle := by
  rw [solveBytes, decode_encode hv]

/-- The typed checked solver, with the oracles answered through the byte encoding by `h`,
computes the byte-level solver run on the encoded puzzle. -/
theorem simulateQ_solve_eq_solveBytes (hv : Valid b n m) [NeZero n] (puzzle : Puzzle b n) :
    simulateQ (impl h b n) (PointerChainPuzzle.solve m (ctx b n m) id puzzle) =
      pure (solveBytes h (encode m puzzle)) := by
  rw [simulateQ_solve_eq, solveBytes_encode h m hv]

/-- Decoding and solving a generated puzzle with valid parameters recovers its key, at every
byte-answer function. -/
theorem solveBytes_generate (hv : Valid b n m) [NeZero n] (salt : Bytes 16)
    (xs : Fin n → Bytes b) :
    solveBytes h (generate h m salt xs).1 = some (generate h m salt xs).2 :=
  (solveBytes_encode h m hv _).trans (solve_genWith h m salt xs)

end Refinement

end PointerChainPuzzle.LeanSeal
