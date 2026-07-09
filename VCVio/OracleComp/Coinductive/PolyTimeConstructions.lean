/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coinductive.CoinFold
import ToMathlib.Data.BitVec

/-!
# Practical Polynomial-Time Constructions

Two ergonomic, reusable polynomial-time facts built on the coin-fold combinator and the
pure-function witness constructor — the two base ways a computation is polynomial time:

* **Randomized generation** — `uniformBitVec n` samples a uniform `BitVec n` by flipping
  `n` coins (a `coinFoldProg` that overwrites one bit per round), and
  `isPolyTime_uniformBitVec` is a direct `isPolyTime_coinFold` application (no bridge, since
  the generator *is* the fold).
* **Deterministic computation** — `isPolyTime_pure_ofFintype` certifies any function on a
  per-parameter finite input type as polynomial time via the finite-table machine, and its
  `BitVec` corollary `isPolyTime_bitVecFun` is hypothesis-free (given polynomial width
  bounds), directly backing the `IsPolyTimeFun` shape used for crypto schemes' target and
  leakage functions.
-/

open OracleSpec Computability

namespace OracleComp

/-! ## Uniform `BitVec` generation -/

/-- Sample a uniform `BitVec n` by flipping `n` coins, folding the `r`-th answer into bit
`r` of the accumulator. This is the bounded coin fold with `step = overwriteBit` and the
identity read-out. -/
def uniformBitVec (n : ℕ) : OracleComp coinSpec (BitVec n) :=
  coinFoldProg (fun (acc : BitVec n) r b => acc.overwriteBit r b) id n 0

/-- **Generating a uniform `BitVec n` is polynomial time.** A one-line application of the
coin-fold combinator: `uniformBitVec` is literally a fold, so no program bridge is needed. -/
theorem isPolyTime_uniformBitVec :
    OracleComp.IsPolyTime fun n (_ : Unit) => uniformBitVec n :=
  isPolyTime_coinFold
    (fun n (acc : BitVec n) r b => acc.overwriteBit r b)
    (fun n => id) (fun _ => 0) (fun n => n) Polynomial.X (fun n => by simp)
    (fun n => finEncodingPair (finEncodingOfFinEnum (Fin (n + 1))) (finEncodingBitVec n))
    (Polynomial.C 8 * Polynomial.X)
    (fun n s => by
      have h := (FinEnum.equiv s.1).isLt
      simp only [FinEnum.card_eq_fintypeCard, Fintype.card_fin] at h
      rw [length_boolify_finEncodingPair, length_encode_finEncodingBitVec,
        show Fintype.card (finEncodingOfFinEnum (Fin (n + 1))).Γ = 1 from rfl,
        show Fintype.card (finEncodingBitVec n).Γ = 2 from rfl]
      simp only [finEncodingOfFinEnum, List.length_replicate, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      omega)
    (fun n => finEncodingBitVec n)
    (Polynomial.C 4 * Polynomial.X + Polynomial.C 4)
    (fun n x => by
      have hlen : ((finEncodingOption (finEncodingBitVec n)).encode x).length ≤ n + 1 := by
        cases x with
        | none => simp [finEncodingOption]
        | some v =>
          simp only [finEncodingOption, List.length_cons, List.length_map,
            length_encode_finEncodingBitVec]
          omega
      rw [length_boolify_finEncodingOption, show Fintype.card (finEncodingBitVec n).Γ = 2 from rfl]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      omega)

/-! ## Deterministic functions on finite inputs -/

/-- **Any deterministic function on a per-parameter finite input type is polynomial time.**
An ergonomic wrapper over `isPolyTime_pure_of_witnesses`: the machine is `ofPureFn (f n)`
(state = the input, output `= some ∘ f`), so the query-selection witness is a constant, and
the update (projection) and output (`some ∘ f`) witnesses are finite-table machines
(`EncPolyTime.ofFintype`). The caller supplies encodings and linear length bounds on the
input (`sizeBound`), the option-wrapped output (`Sout`), and the query encoding (`Sq`). -/
theorem isPolyTime_pure_ofFintype {ι : Type} [DecidableEq ι] [Inhabited ι] [Finite ι]
    {spec : ℕ → OracleSpec.{0, 0} ι} [∀ n, (spec n).Fintype]
    {α β : ℕ → Type} [∀ n, Finite (α n)]
    (f : (n : ℕ) → α n → β n)
    (encIn : (n : ℕ) → FinEncoding (α n)) (encOut : (n : ℕ) → FinEncoding (β n))
    (encIface : (n : ℕ) → (spec n).InterfaceEncoding)
    (sizeBound : Polynomial ℕ) (hsize : ∀ n x, ((encIn n).boolify x).length ≤ sizeBound.eval n)
    (Sout : Polynomial ℕ)
    (hout : ∀ n x, ((finEncodingOption (encOut n)).boolify (some (f n x))).length ≤ Sout.eval n)
    (Sq : Polynomial ℕ)
    (hquery : ∀ n, ((encIface n).encQuery.boolify (default : ι)).length ≤ Sq.eval n) :
    OracleComp.IsPolyTime fun n x => (pure (f n x) : OracleComp (spec n) (β n)) := by
  letI : Fintype ι := Fintype.ofFinite ι
  letI : ∀ n, Fintype (α n) := fun n => Fintype.ofFinite (α n)
  refine OracleComp.isPolyTime_pure_of_witnesses f encIn encOut encIface sizeBound hsize
    (Polynomial.X + sizeBound + Sout + Sq + Polynomial.C 1) ?_
    (fun n => EncPolyTime.ofFintype _ (FinEncoding.boolify_injective _) _ _) ?_
    (fun n => EncPolyTime.ofFintype _ (FinEncoding.boolify_injective _) _ _) ?_
    (fun n => EncPolyTime.ofFintype _ (FinEncoding.boolify_injective _) _ _) ?_
  · intro m; simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; omega
  · intro n k
    refine (EncPolyTime.time_ofFintype_eval_le _ (fun _ => hquery n) k).trans ?_
    have h1 : Sq.eval n ≤ Sq.eval (n + k) := Polynomial.eval_le_eval (Nat.le_add_right n k)
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; omega
  · intro n k
    refine (EncPolyTime.time_ofFintype_eval_le _
      (fun p : α n × ((t : ι) × (spec n).Range t) => hsize n p.1) k).trans ?_
    have h1 : sizeBound.eval n ≤ sizeBound.eval (n + k) :=
      Polynomial.eval_le_eval (Nat.le_add_right n k)
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; omega
  · intro n k
    refine (EncPolyTime.time_ofFintype_eval_le _ (fun x => hout n x) k).trans ?_
    have h1 : Sout.eval n ≤ Sout.eval (n + k) := Polynomial.eval_le_eval (Nat.le_add_right n k)
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]; omega

/-- **Any function between polynomially-bounded-width bitvectors is polynomial time**,
hypothesis-free (the binary `finEncodingBitVec` has exact length `3 * w`). The coin-oracle
form directly backs the `IsPolyTimeFun` abstraction — e.g. a scheme's target/leakage
functions on plaintexts. -/
theorem isPolyTime_bitVecFun {a b : ℕ → ℕ} (pa pb : Polynomial ℕ)
    (ha : ∀ n, a n ≤ pa.eval n) (hb : ∀ n, b n ≤ pb.eval n)
    (f : (n : ℕ) → BitVec (a n) → BitVec (b n)) :
    OracleComp.IsPolyTime fun n x => (pure (f n x) : OracleComp coinSpec (BitVec (b n))) :=
  isPolyTime_pure_ofFintype f (fun n => finEncodingBitVec (a n))
    (fun n => finEncodingBitVec (b n)) (fun _ => .ofFinEnum coinSpec)
    (Polynomial.C 3 * pa) (fun n x => by
      rw [length_boolify_finEncodingBitVec]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      have := ha n; omega)
    (Polynomial.C 4 * pb + Polynomial.C 4) (fun n x => by
      rw [length_boolify_finEncodingOption, length_encode_finEncodingOption_some,
        length_encode_finEncodingBitVec,
        show Fintype.card (finEncodingBitVec (b n)).Γ = 2 from rfl]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      have := hb n; omega)
    (Polynomial.C 2) (fun n => by
      refine (length_boolify_finEncodingOfFinEnum default).trans ?_
      simp [Fintype.card_unique])

/-! ## Demonstrations -/

/-- Generating a uniform bitvector is polynomial time. -/
example : OracleComp.IsPolyTime fun n (_ : Unit) => uniformBitVec n := isPolyTime_uniformBitVec

/-- Bitwise negation is a polynomial-time function. -/
example : OracleComp.IsPolyTime
    fun n (x : BitVec n) => (pure (~~~x) : OracleComp coinSpec (BitVec n)) :=
  isPolyTime_bitVecFun Polynomial.X Polynomial.X (fun n => by simp) (fun n => by simp)
    (fun _ => (~~~·))

end OracleComp
