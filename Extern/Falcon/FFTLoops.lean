/-
Copyright (c) 2026 XC0R. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

module
import all Extern.Falcon.FFT
import all LatticeCrypto.Falcon.FFTStages
public import Extern.Falcon.FFT
public import LatticeCrypto.Falcon.FFTStages
import LatticeCrypto.Ring.NTTLoop

/-!
# The loops of `fpolyFFT` and `fpolyIFFT` as butterfly stages

`fpolyFFT` and `fpolyIFFT` (ports of c-fn-dsa's `fpoly_FFT` / `fpoly_iFFT`) update an array of
`2 · hn` values in place, `hn = 2^(logn - 1)`, reading slot `q` as the complex number with real
part at `q` and imaginary part at `q + hn`. This file proves, for every `FloatLike` format, that
their loops compute the butterfly stages `Falcon.FFTStages.bfStage` on those complex slots:

- `cv_fpolyFFT`: the slots of `fpolyFFT logn f` are `fwdStagesF (logn - 1) (logn - 1)` of the
  slots of `f`, the forward stages with the table twiddles `gmPair (2^(s + 1) + c)` and the
  butterfly `fwdBFF` of the code;
- `cv_fpolyIFFT`: the slots of `fpolyIFFT logn v` are the inverse stages `invStagesF` followed by
  the multiplication of both parts of every slot by the final scale;
- `getElem!_fpolySetSmall`: the input conversion reads each coefficient with `FloatLike.ofInt32`.

Nothing here is about rounding: the statements are equalities of `FloatLike` terms. The `for`
loops over ranges are read as folds through `LatticeCrypto.NTTCert.forIn_range_pure`. The
blocked-loop lemmas of `LatticeCrypto.Ring.NTTLoop` (`rangeLayer`, `ctForward_range`) are stated
for butterflies over a commutative ring on one array of coefficients; the loops here update the
real and imaginary parts of each slot at two offsets, over `FloatLike` values, so they are
proved directly against `bfStage`.
-/

public section

namespace Falcon.Concrete.FFTOps

open Falcon.FFTStages

variable {F : Type} [FloatLike F]

/-! ## Arrays -/

private theorem getElem!_set!_eq (a : Array F) (p i : ℕ) (v : F) :
    (a.set! p v)[i]! = if p = i ∧ p < a.size then v else a[i]! := by
  by_cases h : p = i
  · subst h; by_cases hp : p < a.size <;> simp [hp]
  · simp [h, getElem!_def, Array.getElem?_setIfInBounds_ne h]

/-- Complex slot `q` of an array of `2 · hn` reals: the entries at `q` and `q + hn`. -/
@[expose] def cv (hn : ℕ) (a : Array F) (q : ℕ) : F × F := (a[q]!, a[q + hn]!)

/-- One in-place butterfly of the code on the slots `j1` and `j2`: read both, write both. -/
def bfly (hn j1 j2 : ℕ) (g : (F × F) × (F × F) → (F × F) × (F × F)) (ff : Array F) : Array F :=
  let r := g ((ff[j1]!, ff[j1 + hn]!), (ff[j2]!, ff[j2 + hn]!))
  (((ff.set! j1 r.1.1).set! (j1 + hn) r.1.2).set! j2 r.2.1).set! (j2 + hn) r.2.2

private theorem size_bfly (hn j1 j2 : ℕ) (g : (F × F) × (F × F) → (F × F) × (F × F))
    (ff : Array F) :
    (bfly hn j1 j2 g ff).size = ff.size := by
  simp [bfly]

private theorem cv_bfly (hn j1 j2 : ℕ) (g : (F × F) × (F × F) → (F × F) × (F × F)) (a : Array F)
    (ha : a.size = 2 * hn) (h12 : j1 < j2) (h2 : j2 < hn) (q : ℕ) (hq : q < hn) :
    cv hn (bfly hn j1 j2 g a) q =
      if q = j1 then (g (cv hn a j1, cv hn a j2)).1
      else if q = j2 then (g (cv hn a j1, cv hn a j2)).2 else cv hn a q := by
  simp only [cv, bfly, getElem!_set!_eq, Array.size_set!, ha]
  by_cases hq1 : q = j1
  · subst hq1
    simp (disch := omega) only [ite_true, ite_false, and_true, Prod.mk.eta,
      show j2 + hn ≠ q + hn by omega, show j2 ≠ q + hn by omega, show q + hn ≠ q by omega,
      show j2 ≠ q by omega, show j2 + hn ≠ q by omega, show q < 2 * hn by omega,
      show q + hn < 2 * hn by omega, false_and, ite_false]
  · by_cases hq2 : q = j2
    · subst hq2
      simp (disch := omega) only [hq1, ite_true, ite_false, and_true, Prod.mk.eta,
        show q < 2 * hn by omega, show q + hn < 2 * hn by omega, show j1 ≠ q by omega,
        show j1 + hn ≠ q by omega, show j1 ≠ q + hn by omega, show j1 + hn ≠ q + hn by omega,
        show q + hn ≠ q by omega, show q ≠ q + hn by omega, false_and]
    · simp (disch := omega) only [hq1, hq2, ite_false, show j1 ≠ q by omega,
        show j1 + hn ≠ q by omega, show j2 ≠ q by omega, show j2 + hn ≠ q by omega,
        show j1 ≠ q + hn by omega, show j1 + hn ≠ q + hn by omega, show j2 ≠ q + hn by omega,
        show j2 + hn ≠ q + hn by omega, false_and]

/-! ## One block, one stage -/

/-- The butterflies of one block: offsets `j < H` of the block at `j0`. -/
def blockLoop (hn H j0 : ℕ) (g : (F × F) × (F × F) → (F × F) × (F × F)) (a : Array F) :
    Array F :=
  (List.range' 0 H).foldl (fun b j => bfly hn (j0 + j) (j0 + j + H) g b) a

private theorem blockLoop_spec (hn H j0 : ℕ) (g : (F × F) × (F × F) → (F × F) × (F × F))
    (a : Array F) (ha : a.size = 2 * hn) (hb : j0 + 2 * H ≤ hn) :
    ∀ r ≤ H, ((List.range' 0 r).foldl (fun b j => bfly hn (j0 + j) (j0 + j + H) g b) a).size =
        2 * hn ∧
      ∀ q < hn, cv hn ((List.range' 0 r).foldl (fun b j => bfly hn (j0 + j) (j0 + j + H) g b) a) q =
        if j0 ≤ q ∧ q < j0 + r then (g (cv hn a q, cv hn a (q + H))).1
        else if j0 + H ≤ q ∧ q < j0 + H + r then (g (cv hn a (q - H), cv hn a q)).2
        else cv hn a q := by
  intro r
  induction r with
  | zero =>
    intro _
    refine ⟨by simpa using ha, fun q _ => ?_⟩
    simp only [List.range'_zero, List.foldl_nil]
    split_ifs <;> first | rfl | omega
  | succ r ih =>
    intro hr
    obtain ⟨hs, hc⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set b := (List.range' 0 r).foldl (fun b j => bfly hn (j0 + j) (j0 + j + H) g b) a
    refine ⟨by rw [size_bfly, hs], fun q hq => ?_⟩
    simp only [zero_add, one_mul]
    rw [cv_bfly hn _ _ g b hs (by omega) (by omega) q hq]
    have e1 : cv hn b (j0 + r) = cv hn a (j0 + r) := by
      rw [hc _ (by omega)]; split_ifs <;> first | rfl | omega
    have e2 : cv hn b (j0 + r + H) = cv hn a (j0 + r + H) := by
      rw [hc _ (by omega)]; split_ifs <;> first | rfl | omega
    rw [e1, e2]
    by_cases h1 : q = j0 + r
    · subst h1
      simp only [ite_true, show j0 ≤ j0 + r ∧ j0 + r < j0 + (r + 1) by omega, and_self]
    · by_cases h2 : q = j0 + r + H
      · subst h2
        simp only [h1, ite_true, ite_false,
          show ¬(j0 ≤ j0 + r + H ∧ j0 + r + H < j0 + (r + 1)) by omega,
          show j0 + H ≤ j0 + r + H ∧ j0 + r + H < j0 + H + (r + 1) by omega,
          show j0 + r + H - H = j0 + r by omega, and_self]
      · simp only [h1, h2, ite_false]
        rw [hc q hq]
        split_ifs <;> first | rfl | omega

/-- The blocks of one stage: block `i < nb` at `i · T`, with half-block `H` and pair map `G i`. -/
def stageLoop (hn H T nb : ℕ) (G : ℕ → (F × F) × (F × F) → (F × F) × (F × F)) (a : Array F) :
    Array F × ℕ :=
  (List.range' 0 nb).foldl (fun st i => (blockLoop hn H st.2 (G i) st.1, st.2 + T)) (a, 0)

private theorem stageLoop_spec (hn H T nb : ℕ) (hT : T = 2 * H) (hH : 0 < H)
    (G : ℕ → (F × F) × (F × F) → (F × F) × (F × F))
    (a : Array F) (ha : a.size = 2 * hn) (hcov : nb * (2 * H) ≤ hn) :
    ∀ i ≤ nb, (stageLoop hn H T i G a).2 = i * (2 * H) ∧ (stageLoop hn H T i G a).1.size = 2 * hn ∧
      ∀ q < hn, cv hn (stageLoop hn H T i G a).1 q =
        if q < i * (2 * H) then bfStage H G (cv hn a) q else cv hn a q := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨by simp [stageLoop], by simpa [stageLoop] using ha, fun q _ => ?_⟩
    simp [stageLoop]
  | succ i ih =>
    intro hi
    obtain ⟨h2, hs, hc⟩ := ih (by omega)
    have hst : stageLoop hn H T (i + 1) G a =
        (blockLoop hn H (stageLoop hn H T i G a).2 (G i) (stageLoop hn H T i G a).1,
          (stageLoop hn H T i G a).2 + T) := by
      simp only [stageLoop, List.range'_concat, List.foldl_append, List.foldl_cons,
        List.foldl_nil, zero_add, one_mul]
    subst hT
    rw [hst, h2]
    have hb : i * (2 * H) + 2 * H ≤ hn := by
      have : (i + 1) * (2 * H) ≤ nb * (2 * H) := Nat.mul_le_mul_right _ hi
      nlinarith
    obtain ⟨hs', hc'⟩ := blockLoop_spec hn H (i * (2 * H)) (G i) _ hs (by omega) H le_rfl
    refine ⟨by ring, hs', fun q hq => ?_⟩
    rw [blockLoop, hc' q hq]
    have hagree : ∀ q', i * (2 * H) ≤ q' → q' < hn →
        cv hn (stageLoop hn H (2 * H) i G a).1 q' = cv hn a q' := by
      intro q' h1 h2'
      rw [hc q' h2', ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    by_cases hA : i * (2 * H) ≤ q ∧ q < i * (2 * H) + H
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hA),
        ite_eq_left_of_eq_true _ _ (eq_true (by nlinarith)),
        hagree q hA.1 hq, hagree (q + H) (by omega) (by omega)]
      have hm : q % (2 * H) = q - i * (2 * H) ∧ q / (2 * H) = i := by
        have := mul_add_mod_div (T := 2 * H) (c := i) (j := q - i * (2 * H)) (by omega)
        rwa [show i * (2 * H) + (q - i * (2 * H)) = q by omega] at this
      simp only [bfStage, hm.1, hm.2, show q - i * (2 * H) < H by omega, ite_true]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hA)]
      by_cases hB : i * (2 * H) + H ≤ q ∧ q < i * (2 * H) + H + H
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hB),
          ite_eq_left_of_eq_true _ _ (eq_true (by nlinarith)),
          hagree q (by omega) hq,
          hagree (q - H) (by omega) (by omega)]
        have hm : q % (2 * H) = q - i * (2 * H) ∧ q / (2 * H) = i := by
          have := mul_add_mod_div (T := 2 * H) (c := i) (j := q - i * (2 * H)) (by omega)
          rwa [show i * (2 * H) + (q - i * (2 * H)) = q by omega] at this
        simp only [bfStage, hm.1, hm.2, show ¬(q - i * (2 * H) < H) by omega, ite_false]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hB), hc q hq]
        have hexp : (i + 1) * (2 * H) = i * (2 * H) + 2 * H := by ring
        split_ifs <;> first | rfl | omega

/-! ## The forward transform -/

/-- Table entry `m` of the twiddle table, as `(cos, sin)`. -/
@[expose] def gmPair (m : ℕ) : F × F :=
  (FloatLike.ofRawFPR (Falcon.Concrete.GMTable.gmRaw.getD (2 * m) 0),
    FloatLike.ofRawFPR (Falcon.Concrete.GMTable.gmRaw.getD (2 * m + 1) 0))

/-- The forward butterfly of `fpolyFFT` with twiddle `s`: `(x + s · y, x - s · y)`, each step
rounded by the format. -/
@[expose] def fwdBFF (s : F × F) (p : (F × F) × (F × F)) : (F × F) × (F × F) :=
  let z := (FloatLike.sub (FloatLike.mul p.2.1 s.1) (FloatLike.mul p.2.2 s.2),
    FloatLike.add (FloatLike.mul p.2.2 s.1) (FloatLike.mul p.2.1 s.2))
  ((FloatLike.add p.1.1 z.1, FloatLike.add p.1.2 z.2),
    (FloatLike.sub p.1.1 z.1, FloatLike.sub p.1.2 z.2))

/-- The inverse butterfly of `fpolyIFFT` with twiddle `s`: `(x + y, (x - y) · s̄)`, each step
rounded by the format. -/
@[expose] def invBFF (s : F × F) (p : (F × F) × (F × F)) : (F × F) × (F × F) :=
  let u := (FloatLike.sub p.1.1 p.2.1, FloatLike.sub p.1.2 p.2.2)
  ((FloatLike.add p.1.1 p.2.1, FloatLike.add p.1.2 p.2.2),
    (FloatLike.sub (FloatLike.mul u.1 s.1) (FloatLike.mul u.2 (FloatLike.neg s.2)),
      FloatLike.add (FloatLike.mul u.2 s.1) (FloatLike.mul u.1 (FloatLike.neg s.2))))

/-- The first `s` forward stages of the code on `2^k` complex slots. -/
@[expose] def fwdStagesF (k : ℕ) : ℕ → (ℕ → F × F) → ℕ → F × F
  | 0, x => x
  | s + 1, x => bfStage (2 ^ (k - 1 - s)) (fun c => fwdBFF (gmPair (2 ^ (s + 1) + c)))
      (fwdStagesF k s x)

/-- The first `j` inverse stages of the code on `2^k` complex slots. -/
@[expose] def invStagesF (k : ℕ) : ℕ → (ℕ → F × F) → ℕ → F × F
  | 0, x => x
  | j + 1, x => bfStage (2 ^ j) (fun c => invBFF (gmPair (2 ^ (k - j) + c))) (invStagesF k j x)

/-- One level of `fpolyFFT`, from the state `(array, t)` of the outer loop. -/
def fwdLevel (logn lm : ℕ) (st : Array F × ℕ) : Array F × ℕ :=
  ((stageLoop (1 <<< (logn - 1)) (st.2 >>> 1) st.2 (1 <<< lm >>> 1)
    (fun i => fwdBFF (gmPair ((1 <<< lm) + i))) st.1).1, st.2 >>> 1)

private theorem fpolyFFT_eq (logn : ℕ) (f : Array F) (h : ¬logn ≤ 1) :
    fpolyFFT logn f =
      ((List.range' 1 (logn - 1)).foldl (fun st lm => fwdLevel logn lm st)
        (f, 1 <<< (logn - 1))).1 := by
  unfold fpolyFFT
  simp only [h, ite_false, LatticeCrypto.NTTCert.forIn_range_pure, Id.run, pure_bind,
    Nat.sub_zero]
  rfl

private theorem shiftLeft_one (a : ℕ) : 1 <<< a = 2 ^ a := by rw [Nat.shiftLeft_eq, one_mul]

private theorem two_pow_shiftRight_one {a : ℕ} (ha : 1 ≤ a) : 2 ^ a >>> 1 = 2 ^ (a - 1) := by
  rw [Nat.shiftRight_eq_div_pow, pow_one, ← Nat.pow_div ha (by norm_num), pow_one]

private theorem fwdLevel_fst (logn lm : ℕ) (st : Array F × ℕ) :
    (fwdLevel logn lm st).1 = (stageLoop (2 ^ (logn - 1)) (st.2 >>> 1) st.2 (2 ^ lm >>> 1)
      (fun i => fwdBFF (gmPair (2 ^ lm + i))) st.1).1 := by
  simp only [fwdLevel, shiftLeft_one]

private theorem fwdLevel_snd (logn lm : ℕ) (st : Array F × ℕ) :
    (fwdLevel logn lm st).2 = st.2 >>> 1 := by
  simp only [fwdLevel]

/-- **The loops of `fpolyFFT` are the forward stages.** For `2 ≤ logn` and an input of
`2 · 2^(logn - 1)` entries, complex slot `q` of the output is slot `q` of `logn - 1` forward
stages of the input slots. -/
theorem cv_fpolyFFT (logn : ℕ) (hlogn : 2 ≤ logn) (f : Array F)
    (hf : f.size = 2 * 2 ^ (logn - 1)) :
    ∀ q < 2 ^ (logn - 1), cv (2 ^ (logn - 1)) (fpolyFFT logn f) q =
      fwdStagesF (logn - 1) (logn - 1) (cv (2 ^ (logn - 1)) f) q := by
  set k := logn - 1 with hk
  have hk1 : 1 ≤ k := by omega
  rw [fpolyFFT_eq logn f (by omega), shiftLeft_one]
  have key : ∀ j ≤ k,
      ((List.range' 1 j).foldl (fun st lm => fwdLevel logn lm st) (f, 2 ^ k)).2 = 2 ^ (k - j) ∧
      ((List.range' 1 j).foldl (fun st lm => fwdLevel logn lm st) (f, 2 ^ k)).1.size = 2 * 2 ^ k ∧
      ∀ q < 2 ^ k, cv (2 ^ k) ((List.range' 1 j).foldl (fun st lm => fwdLevel logn lm st)
        (f, 2 ^ k)).1 q = fwdStagesF k j (cv (2 ^ k) f) q := by
    intro j
    induction j with
    | zero => intro _; exact ⟨by simp, hf, fun q _ => rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨ht, hs, hc⟩ := ih (by omega)
      rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, one_mul]
      set st := (List.range' 1 j).foldl (fun st lm => fwdLevel logn lm st) (f, 2 ^ k)
      have hH : (fwdLevel logn (1 + j) st).2 = 2 ^ (k - 1 - j) := by
        rw [fwdLevel_snd]
        rw [ht, two_pow_shiftRight_one (by omega)]; congr 1; omega
      have hH' : st.2 >>> 1 = 2 ^ (k - 1 - j) := by
        rw [ht, two_pow_shiftRight_one (by omega)]; congr 1; omega
      have hT : st.2 = 2 * 2 ^ (k - 1 - j) := by
        rw [ht, ← pow_succ']; congr 1; omega
      have heq : 2 ^ k = 2 ^ j * (2 * 2 ^ (k - 1 - j)) := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      have hcov : 2 ^ j * (2 * 2 ^ (k - 1 - j)) ≤ 2 ^ k := le_of_eq heq.symm
      have hcov' : 2 ^ k ≤ 2 ^ j * (2 * 2 ^ (k - 1 - j)) := le_of_eq heq
      have hdvd : 2 * 2 ^ (k - 1 - j) ∣ 2 ^ k := ⟨2 ^ j, by rw [heq]; ring⟩
      have e1 : (fwdLevel logn (1 + j) st).1 = (stageLoop (2 ^ k) (2 ^ (k - 1 - j)) st.2 (2 ^ j)
          (fun i => fwdBFF (gmPair (2 ^ (1 + j) + i))) st.1).1 := by
        rw [fwdLevel_fst, hH', two_pow_shiftRight_one (by omega : 1 ≤ 1 + j),
          show 1 + j - 1 = j by omega, ← hk]
      have e2 : (fwdLevel logn (1 + j) st).2 = 2 ^ (k - 1 - j) := hH
      obtain ⟨-, hs', hc'⟩ := stageLoop_spec (2 ^ k) (2 ^ (k - 1 - j)) st.2 (2 ^ j) hT
        (by positivity) (fun i => fwdBFF (gmPair (2 ^ (1 + j) + i))) st.1 hs hcov (2 ^ j) le_rfl
      refine ⟨?_, ?_, fun q hq => ?_⟩
      · rw [e2]; congr 1; omega
      · rw [e1]; exact hs'
      · rw [e1, hc' q hq, ite_eq_left_of_eq_true _ _ (eq_true (lt_of_lt_of_le hq hcov'))]
        rw [bfStage_congr (2 ^ k) _ (by positivity) hdvd _ _ _ hc q hq, Nat.add_comm 1 j]
        rfl
  exact (key k le_rfl).2.2

/-! ## The inverse transform -/

/-- One level of `fpolyIFFT`, from the state `(array, t)` of the outer loop. -/
def invLevel (logn lm : ℕ) (st : Array F × ℕ) : Array F × ℕ :=
  ((stageLoop (1 <<< logn >>> 1) st.2 (st.2 <<< 1) (1 <<< (logn - lm) >>> 1)
    (fun i => invBFF (gmPair ((1 <<< (logn - lm)) + i))) st.1).1, st.2 <<< 1)

/-- The final scaling loop of `fpolyIFFT`: multiply the first `n` entries by `c`. -/
def scaleLoop (n : ℕ) (c : F) (a : Array F) : Array F :=
  (List.range' 0 n).foldl (fun b i => b.set! i (FloatLike.mul b[i]! c)) a

private theorem fpolyIFFT_eq (logn : ℕ) (f : Array F) (h : ¬logn ≤ 1) :
    fpolyIFFT logn f = scaleLoop (1 <<< logn)
      (FloatLike.scaled 4503599627370496 (0 - 51 - logn.toUInt32.toInt32))
      ((List.range' 1 (logn - 1)).foldl (fun st lm => invLevel logn lm st) (f, 1)).1 := by
  unfold fpolyIFFT
  simp only [h, ite_false, LatticeCrypto.NTTCert.forIn_range_pure, Id.run, pure_bind,
    Nat.sub_zero]
  rfl

private theorem scaleLoop_spec (n : ℕ) (c : F) (a : Array F) (ha : n ≤ a.size) :
    ∀ r ≤ n, ((List.range' 0 r).foldl (fun b i => b.set! i (FloatLike.mul b[i]! c)) a).size =
        a.size ∧
      ∀ p, ((List.range' 0 r).foldl (fun b i => b.set! i (FloatLike.mul b[i]! c)) a)[p]! =
          if p < r then FloatLike.mul a[p]! c else a[p]! := by
  intro r
  induction r with
  | zero => intro _; simp
  | succ r ih =>
    intro hr
    obtain ⟨hs, hc⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, zero_add, one_mul]
    refine ⟨by rw [Array.size_set!, hs], fun p => ?_⟩
    rw [getElem!_set!_eq, hc r, hc p, hs]
    by_cases hp : p = r
    · subst hp
      simp only [true_and, show p < a.size by omega, lt_irrefl, show p < p + 1 by omega,
        ite_true, ite_false]
    · have hp' : r ≠ p := fun h => hp h.symm
      simp only [hp', false_and, ite_false]
      split_ifs <;> first | rfl | omega

private theorem getElem!_scaleLoop (n : ℕ) (c : F) (a : Array F) (ha : n ≤ a.size) (p : ℕ)
    (hp : p < n) :
    (scaleLoop n c a)[p]! = FloatLike.mul a[p]! c := by
  rw [scaleLoop, (scaleLoop_spec n c a ha n le_rfl).2 p, ite_eq_left_of_eq_true _ _ (eq_true hp)]

private theorem invLevel_fst (logn lm : ℕ) (st : Array F × ℕ) :
    (invLevel logn lm st).1 = (stageLoop (2 ^ logn >>> 1) st.2 (st.2 <<< 1) (2 ^ (logn - lm) >>> 1)
      (fun i => invBFF (gmPair (2 ^ (logn - lm) + i))) st.1).1 := by
  simp only [invLevel, shiftLeft_one]

private theorem invLevel_snd (logn lm : ℕ) (st : Array F × ℕ) :
    (invLevel logn lm st).2 = st.2 <<< 1 := by
  simp only [invLevel]

/-- **The loops of `fpolyIFFT` are the inverse stages, then a scaling.** For `2 ≤ logn` and an
input of `2 · 2^(logn - 1)` entries, complex slot `q` of the output is slot `q` of the
`logn - 1` inverse stages of the input slots, both parts multiplied by the final scale. -/
theorem cv_fpolyIFFT (logn : ℕ) (hlogn : 2 ≤ logn) (f : Array F)
    (hf : f.size = 2 * 2 ^ (logn - 1)) :
    ∀ q < 2 ^ (logn - 1), cv (2 ^ (logn - 1)) (fpolyIFFT logn f) q =
      (FloatLike.mul (invStagesF (logn - 1) (logn - 1) (cv (2 ^ (logn - 1)) f) q).1
          (FloatLike.scaled 4503599627370496 (0 - 51 - logn.toUInt32.toInt32)),
        FloatLike.mul (invStagesF (logn - 1) (logn - 1) (cv (2 ^ (logn - 1)) f) q).2
          (FloatLike.scaled 4503599627370496 (0 - 51 - logn.toUInt32.toInt32))) := by
  set k := logn - 1 with hk
  have hk1 : 1 ≤ k := by omega
  have hhn : 2 ^ logn >>> 1 = 2 ^ k := by rw [two_pow_shiftRight_one (by omega)]
  have key : ∀ j ≤ k,
      ((List.range' 1 j).foldl (fun st lm => invLevel logn lm st) (f, 1)).2 = 2 ^ j ∧
      ((List.range' 1 j).foldl (fun st lm => invLevel logn lm st) (f, 1)).1.size = 2 * 2 ^ k ∧
      ∀ q < 2 ^ k, cv (2 ^ k) ((List.range' 1 j).foldl (fun st lm => invLevel logn lm st)
        (f, 1)).1 q = invStagesF k j (cv (2 ^ k) f) q := by
    intro j
    induction j with
    | zero => intro _; exact ⟨by simp, hf, fun q _ => rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨ht, hs, hc⟩ := ih (by omega)
      rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, one_mul]
      set st := (List.range' 1 j).foldl (fun st lm => invLevel logn lm st) (f, 1)
      have hT : st.2 <<< 1 = 2 * 2 ^ j := by rw [ht, Nat.shiftLeft_eq, pow_one, mul_comm]
      have hnb : 2 ^ (logn - (1 + j)) >>> 1 = 2 ^ (k - 1 - j) := by
        rw [two_pow_shiftRight_one (by omega)]; congr 1; omega
      have heq : 2 ^ k = 2 ^ (k - 1 - j) * (2 * 2 ^ j) := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      have hdvd : 2 * 2 ^ j ∣ 2 ^ k := ⟨2 ^ (k - 1 - j), by rw [heq]; ring⟩
      have e1 : (invLevel logn (1 + j) st).1 =
          (stageLoop (2 ^ k) (2 ^ j) (st.2 <<< 1) (2 ^ (k - 1 - j))
          (fun i => invBFF (gmPair (2 ^ (k - j) + i))) st.1).1 := by
        rw [invLevel_fst, hhn, hnb, ht, show logn - (1 + j) = k - j by omega]
      obtain ⟨-, hs', hc'⟩ := stageLoop_spec (2 ^ k) (2 ^ j) (st.2 <<< 1) (2 ^ (k - 1 - j)) hT
        (by positivity) (fun i => invBFF (gmPair (2 ^ (k - j) + i))) st.1 hs (le_of_eq heq.symm)
        (2 ^ (k - 1 - j)) le_rfl
      refine ⟨?_, ?_, fun q hq => ?_⟩
      · rw [invLevel_snd, hT, ← pow_succ']
      · rw [e1]; exact hs'
      · rw [e1, hc' q hq, ite_eq_left_of_eq_true _ _ (eq_true (lt_of_lt_of_le hq (le_of_eq heq)))]
        rw [bfStage_congr (2 ^ k) _ (by positivity) hdvd _ _ _ hc q hq]
        rfl
  intro q hq
  obtain ⟨-, hs, hc⟩ := key k le_rfl
  rw [fpolyIFFT_eq logn f (by omega), shiftLeft_one]
  have hn : 2 ^ logn = 2 * 2 ^ k := by rw [← pow_succ']; congr 1; omega
  simp only [cv]
  rw [getElem!_scaleLoop _ _ _ (by rw [hs, hn]) q (by rw [hn]; omega),
    getElem!_scaleLoop _ _ _ (by rw [hs, hn]) (q + 2 ^ k) (by rw [hn]; omega)]
  have h1 := congrArg Prod.fst (hc q hq)
  have h2 := congrArg Prod.snd (hc q hq)
  simp only [cv] at h1 h2
  rw [h1, h2]

/-! ## The input conversion -/

private theorem fpolySetSmall_eq (logn : ℕ) (f : Array Int32) :
    fpolySetSmall (F := F) logn f = (List.range' 0 (1 <<< logn)).foldl
      (fun d i => d.set! i (FloatLike.ofInt32 (f.getD i 0)))
      (Array.replicate (1 <<< logn) FloatLike.zero) := by
  unfold fpolySetSmall
  simp only [LatticeCrypto.NTTCert.forIn_range_pure, Id.run, pure_bind, Nat.sub_zero]
  rfl

private theorem setSmall_spec (n : ℕ) (f : Array Int32) :
    ∀ r ≤ n, ((List.range' 0 r).foldl (fun d i => d.set! i (FloatLike.ofInt32 (f.getD i 0)))
        (Array.replicate n (FloatLike.zero : F))).size = n ∧
      ∀ p < r, ((List.range' 0 r).foldl (fun d i => d.set! i (FloatLike.ofInt32 (f.getD i 0)))
        (Array.replicate n (FloatLike.zero : F)))[p]! = FloatLike.ofInt32 (f.getD p 0) := by
  intro r
  induction r with
  | zero => intro _; simp
  | succ r ih =>
    intro hr
    obtain ⟨hs, hc⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, zero_add, one_mul]
    refine ⟨by rw [Array.size_set!, hs], fun p hp => ?_⟩
    rw [getElem!_set!_eq, hs]
    by_cases hpr : p = r
    · subst hpr; simp only [true_and, show p < n by omega, ite_true]
    · have hp' : r ≠ p := fun h => hpr h.symm
      simp only [hp', false_and, ite_false]
      exact hc p (by omega)

/-- The input conversion reads coefficient `p` with `FloatLike.ofInt32`. -/
theorem getElem!_fpolySetSmall (logn : ℕ) (f : Array Int32) (p : ℕ) (hp : p < 2 ^ logn) :
    (fpolySetSmall (F := F) logn f)[p]! = FloatLike.ofInt32 (f.getD p 0) := by
  rw [fpolySetSmall_eq, shiftLeft_one]
  exact (setSmall_spec (2 ^ logn) f (2 ^ logn) le_rfl).2 p hp

/-- The input conversion has `2^logn` entries. -/
theorem size_fpolySetSmall (logn : ℕ) (f : Array Int32) :
    (fpolySetSmall (F := F) logn f).size = 2 ^ logn := by
  rw [fpolySetSmall_eq, shiftLeft_one]
  exact (setSmall_spec (2 ^ logn) f (2 ^ logn) le_rfl).1

/-! ## Sizes and complex slots read with `getD` -/

/-- `fpolyFFT` keeps the size `2 · 2^(logn - 1)` of its input. -/
theorem size_fpolyFFT (logn : ℕ) (hlogn : 2 ≤ logn) (f : Array F)
    (hf : f.size = 2 * 2 ^ (logn - 1)) : (fpolyFFT logn f).size = 2 * 2 ^ (logn - 1) := by
  rw [fpolyFFT_eq logn f (by omega)]
  set k := logn - 1 with hk
  rw [shiftLeft_one]
  have key : ∀ j ≤ k,
      ((List.range' 1 j).foldl (fun st lm => fwdLevel logn lm st) (f, 2 ^ k)).2 = 2 ^ (k - j) ∧
      ((List.range' 1 j).foldl (fun st lm => fwdLevel logn lm st) (f, 2 ^ k)).1.size =
        2 * 2 ^ k := by
    intro j
    induction j with
    | zero => intro _; exact ⟨by simp, hf⟩
    | succ j ih =>
      intro hj
      obtain ⟨ht, hs⟩ := ih (by omega)
      rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, one_mul]
      set st := (List.range' 1 j).foldl (fun st lm => fwdLevel logn lm st) (f, 2 ^ k)
      have hH' : st.2 >>> 1 = 2 ^ (k - 1 - j) := by
        rw [ht, two_pow_shiftRight_one (by omega)]; congr 1; omega
      have hT : st.2 = 2 * 2 ^ (k - 1 - j) := by rw [ht, ← pow_succ']; congr 1; omega
      have heq : 2 ^ k = 2 ^ j * (2 * 2 ^ (k - 1 - j)) := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      refine ⟨by rw [fwdLevel_snd, hH']; congr 1; omega, ?_⟩
      rw [fwdLevel_fst, hH', two_pow_shiftRight_one (by omega : 1 ≤ 1 + j),
        show 1 + j - 1 = j by omega, ← hk]
      exact (stageLoop_spec (2 ^ k) (2 ^ (k - 1 - j)) st.2 (2 ^ j) hT (by positivity) _ st.1 hs
        (le_of_eq heq.symm) (2 ^ j) le_rfl).2.1
  exact (key k le_rfl).2

/-- `fpolyIFFT` keeps the size `2 · 2^(logn - 1)` of its input. -/
theorem size_fpolyIFFT (logn : ℕ) (hlogn : 2 ≤ logn) (f : Array F)
    (hf : f.size = 2 * 2 ^ (logn - 1)) : (fpolyIFFT logn f).size = 2 * 2 ^ (logn - 1) := by
  rw [fpolyIFFT_eq logn f (by omega)]
  set k := logn - 1 with hk
  have hhn : 2 ^ logn >>> 1 = 2 ^ k := by rw [two_pow_shiftRight_one (by omega)]
  have hn : 2 ^ logn = 2 * 2 ^ k := by rw [← pow_succ']; congr 1; omega
  have key : ∀ j ≤ k,
      ((List.range' 1 j).foldl (fun st lm => invLevel logn lm st) (f, 1)).2 = 2 ^ j ∧
      ((List.range' 1 j).foldl (fun st lm => invLevel logn lm st) (f, 1)).1.size =
        2 * 2 ^ k := by
    intro j
    induction j with
    | zero => intro _; exact ⟨by simp, hf⟩
    | succ j ih =>
      intro hj
      obtain ⟨ht, hs⟩ := ih (by omega)
      rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, one_mul]
      set st := (List.range' 1 j).foldl (fun st lm => invLevel logn lm st) (f, 1)
      have hT : st.2 <<< 1 = 2 * 2 ^ j := by rw [ht, Nat.shiftLeft_eq, pow_one, mul_comm]
      have hnb : 2 ^ (logn - (1 + j)) >>> 1 = 2 ^ (k - 1 - j) := by
        rw [two_pow_shiftRight_one (by omega)]; congr 1; omega
      have heq : 2 ^ k = 2 ^ (k - 1 - j) * (2 * 2 ^ j) := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      refine ⟨by rw [invLevel_snd, hT, ← pow_succ'], ?_⟩
      rw [invLevel_fst, hhn, hnb, ht, show logn - (1 + j) = k - j by omega]
      exact (stageLoop_spec (2 ^ k) (2 ^ j) (2 ^ j <<< 1) (2 ^ (k - 1 - j))
        (by rw [Nat.shiftLeft_eq, pow_one, mul_comm]) (by positivity) _ st.1 hs
        (le_of_eq heq.symm) (2 ^ (k - 1 - j)) le_rfl).2.1
  obtain ⟨-, hs⟩ := key k le_rfl
  rw [scaleLoop, (scaleLoop_spec _ _ _ (by rw [shiftLeft_one, hs, hn]) _ le_rfl).1, hs]

/-- In bounds, a complex slot reads the entries with `getD`. -/
theorem cv_eq_getD (hn : ℕ) (a : Array F) (q : ℕ) (hq : q + hn < a.size) :
    cv hn a q = (a.getD q FloatLike.zero, a.getD (q + hn) FloatLike.zero) := by
  simp only [cv, Array.getD_eq_getD_getElem?, getElem!_pos a q (by omega),
    getElem!_pos a (q + hn) hq, Array.getElem?_eq_getElem (by omega : q < a.size),
    Array.getElem?_eq_getElem hq, Option.getD_some]

end Falcon.Concrete.FFTOps

end
