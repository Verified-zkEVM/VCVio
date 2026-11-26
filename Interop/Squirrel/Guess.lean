/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Machine
public import VCVio.OracleComp.QueryTracking.RunLog
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.EvalDist.ProbabilityBounds

/-!
# The guessing machine

CCS26's proof of Rw-Oracle (App. C.1, pp. 15–16) uses a polynomial `q(η)` bounding the number of
oracle calls of the adversary `A` (here `Machine.QueryBound`), and a machine `B` that "samples `j`
uniformly between `1` and `q(η)`, independently of the randomness used by `A` (i.e. using a part
of `ρa` further away)", and runs `A_j`, which "simulates `A` until its `j`-th oracle call, and
returns the input of that call".

* **The guessing machine.** `Machine.guess off k ha A d` reads the `k η` bits of the tape from bit
  `off η` as a number `j < 2 ^ k η` (`bitsEquiv`), runs `A` logging its queries (VCVio's
  `withQueryLog`), and returns the argument of the `j`-th query to its first input, an oracle of
  type `a → b`, or `d`'s value if there is no such query (CCS26's "default value"). Running `A`
  to the end and reading its log gives the same output as stopping at the `j`-th call.
  `Machine.run_guess` says what it computes, through the log of the run (VCVio's `runLog`).
* **Identical until bad, on one path** (`Machine.run_cons_eq_of_firstArgs`): with the oracle
  `o₁` replaced by `o₂`, a run that queried `o₁` only where the two agree is unchanged.
* **Exact uniformity.** `k` bits spell a uniform number below `2 ^ k`, not below `q`. Rounding `q`
  up to a power of two (`k = ⌈log₂ q⌉`, `Nat.clog`) costs a factor below `2`
  (`Nat.pow_clog_le_mul_add_one`). `sum_prEvent_eq_two_pow_mul` is the averaging step: when the
  events `E j` read the attacker tape only below `off`, the sum of their probabilities for
  `j < 2 ^ k` is `2 ^ k` times the probability of `E j` at the number the bits `[off, off + k)`
  spell. Its proof is one involution of (bits, tape), which swaps the drawn bits with that block
  (`Model.setBlock`).

The guess keeps read and query bounds (`Machine.ReadsBelow.guess`, `Machine.QueryBound.guess`).
The guessing bound for Rw-Oracle's attacker machine is `prEvent_exists_firstArgs_le`, in
`Interop.Squirrel.Rules.Oracle`.

## References

* [CCS26] Hérouard, Jacomme, Koutsos, Lallemand, *Secrecy in Squirrel and the Post-Compromise
  Security of a Ratchet*, CCS 2026: App. C.1.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature OracleComp OracleSpec

variable {B : Type} {D : Decl B} {M : Model D} {η : ℕ} {τs : List (Ty B)} {a b β γ : Ty B}

/-! ## The guessing machine -/

/-- `k` bits as a number below `2 ^ k`, least significant bit first: a bijection. -/
@[expose] def bitsEquiv (k : ℕ) : (Fin k → Bool) ≃ Fin (2 ^ k) :=
  (Equiv.arrowCongr (Equiv.refl (Fin k)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- The arguments of a query to the first input; tape reads and queries to the other inputs have
none. -/
@[expose] def Model.firstArg (M : Model D) {η : ℕ} {σ : Ty B} {Γ : List (Ty B)} :
    ℕ ⊕ M.InQuery η (σ :: Γ) → Option (Vals M η σ.args)
  | .inr ⟨_, .zero, q⟩ => some q
  | _ => none

/-- The arguments of the queries to the first input in a query log, oldest first. -/
@[expose] def Model.firstArgs (M : Model D) {η : ℕ} {σ : Ty B} {Γ : List (Ty B)}
    (log : QueryLog (M.Iface η (σ :: Γ))) : List (Vals M η σ.args) :=
  log.filterMap fun e => M.firstArg e.1

private theorem Model.isRight_of_firstArg {σ : Ty B} {Γ : List (Ty B)} :
    ∀ (t : ℕ ⊕ M.InQuery η (σ :: Γ)), (M.firstArg t).isSome → t.isRight = true
  | .inl _, h => absurd h (by simp [Model.firstArg])
  | .inr _, _ => rfl

/-- The guessing machine of CCS26's proof of Rw-Oracle (App. C.1, p. 15): read the `k η` bits of
the attacker tape from bit `off η` as a number `j < 2 ^ k η`; run `A`, logging its queries; and
return the argument of the `j`-th query to its first input, an oracle of type `a → b` with `a` a
Boolean or base type, or `d`'s value if `A` made at most `j` such queries. -/
@[expose] def Machine.guess {Γ : List (Ty B)} (off k : ℕ → ℕ) (ha : a.IsGround)
    (A : Machine M (.arrow a b :: Γ) γ) (d : Machine M (.arrow a b :: Γ) a.res) :
    Machine M (.arrow a b :: Γ) a.res := fun η => do
  let c ← readBits (off η) (k η)
  let r ← (A η).withQueryLog
  ((M.firstArgs r.2)[(bitsEquiv (k η) c : ℕ)]?).elim (d η)
    fun q => pure (Ty.apply (q _ .zero) (Ty.groundArgs ha))

namespace Machine

variable {Γ : List (Ty B)} {ρa : M.TapeA η}

/-- The guessing machine returns the argument of the `j`-th query to the first input of `A`'s run,
for the number `j` that the bits `[off η, off η + k η)` of the tape spell, or `d`'s value. -/
theorem run_guess (off k : ℕ → ℕ) (ha : a.IsGround) (A : Machine M (.arrow a b :: Γ) γ)
    (d : Machine M (.arrow a b :: Γ) a.res) (e : Vals M η (.arrow a b :: Γ)) :
    (A.guess off k ha d).run η ρa e =
      ((M.firstArgs (runLog (M.answer ρa e) (A η)))[(bitsEquiv (k η)
          (M.bitsAt ρa (off η) (k η)) : ℕ)]?).elim (d.run η ρa e)
        fun q => Ty.apply (q _ .zero) (Ty.groundArgs ha) := by
  simp only [run, guess, evalWithAnswerFn_bind, evalWithAnswerFn_readBits,
    evalWithAnswerFn_withQueryLog]
  cases (M.firstArgs (runLog (M.answer ρa e) (A η)))[(bitsEquiv (k η)
    (M.bitsAt ρa (off η) (k η)) : ℕ)]? <;> rfl

/-- A machine making at most `q η` input queries logs at most `q η` queries to its first input. -/
theorem QueryBound.length_firstArgs_le {σ : Ty B} {A : Machine M (σ :: Γ) γ} {q : ℕ → ℕ}
    (hA : A.QueryBound q) (ρa : M.TapeA η) (e : Vals M η (σ :: Γ)) :
    (M.firstArgs (runLog (M.answer ρa e) (A η))).length ≤ q η :=
  length_filterMap_runLog_le _ (fun e => M.firstArg e.1)
    (fun e he => M.isRight_of_firstArg e.1 he) (hA η)

/-- A machine reading below `bd` logs the same queries at two tapes that agree below `bd η`. -/
theorem ReadsBelow.runLog_eq {A : Machine M τs β} {bd : ℕ → ℕ} (hA : A.ReadsBelow bd)
    {ρa ρa' : M.TapeA η} (hρ : ∀ i < bd η, M.readBit ρa i = M.readBit ρa' i) (e : Vals M η τs) :
    runLog (M.answer ρa e) (A η) = runLog (M.answer ρa' e) (A η) :=
  runLog_eq_of_allQueriesSatisfy (fun t ht => by
    rcases t with i | q
    · exact hρ i ht
    · rfl) (hA η)

/-- **Identical until bad, on one path** (CCS26 App. C.1, step 1): a machine whose first input is
the oracle `o₁` runs as with `o₂` in its place, when its run with `o₁` queries `o₁` only at points
where the two agree. -/
theorem run_cons_eq_of_firstArgs (A : Machine M (.arrow a b :: Γ) γ)
    {o₁ o₂ : (Ty.arrow a b).Value M.carrier η} {e : Vals M η Γ}
    (h : ∀ q ∈ M.firstArgs (runLog (M.answer ρa (Env.cons o₁ e)) (A η)),
      o₁ (q _ .zero) = o₂ (q _ .zero)) :
    A.run η ρa (Env.cons o₁ e) = A.run η ρa (Env.cons o₂ e) := by
  refine evalWithAnswerFn_eq_of_forall_mem_runLog fun ent hent => ?_
  obtain ⟨t, r⟩ := ent
  rcases t with i | ⟨τ, x, q⟩
  · rfl
  · cases x with
    | zero =>
      have hq : q ∈ M.firstArgs (runLog (M.answer ρa (Env.cons o₁ e)) (A η)) :=
        List.mem_filterMap.2 ⟨_, hent, rfl⟩
      change Ty.apply (o₁ (q _ .zero)) _ = Ty.apply (o₂ (q _ .zero)) _
      rw [h q hq]
    | succ x => rfl

/-! ## Read and query bounds of the guessing machine -/

/-- The guess reads the bits it draws and what `A` and `d` read. -/
theorem ReadsBelow.guess {A : Machine M (.arrow a b :: Γ) γ}
    {d : Machine M (.arrow a b :: Γ) a.res} {bd : ℕ → ℕ} (hA : A.ReadsBelow bd)
    (hd : d.ReadsBelow bd) (off k : ℕ → ℕ) (ha : a.IsGround) (hk : ∀ η, off η + k η ≤ bd η) :
    (A.guess off k ha d).ReadsBelow bd := fun η => by
  unfold Machine.guess
  refine allQueriesSatisfy_bind ((allQueriesSatisfy_readBits _ _).mono
    (Model.tapeBelow_mono (hk η))) fun c => allQueriesSatisfy_bind
      ((allQueriesSatisfy_withQueryLog_iff _ _).2 (hA η)) fun r => ?_
  cases (M.firstArgs r.2)[(bitsEquiv (k η) c : ℕ)]? with
  | none => exact hd η
  | some q => exact allQueriesSatisfy_pure _ _

/-- The guess makes the queries of `A`, then those of `d`. -/
theorem QueryBound.guess {A : Machine M (.arrow a b :: Γ) γ}
    {d : Machine M (.arrow a b :: Γ) a.res} {q q' : ℕ → ℕ} (hA : A.QueryBound q)
    (hd : d.QueryBound q') (off k : ℕ → ℕ) (ha : a.IsGround) :
    (A.guess off k ha d).QueryBound fun η => q η + q' η := fun η => by
  unfold Machine.guess
  refine isQueryBoundP_bind_le (isQueryBoundP_readBits _ _) (fun c _ =>
    isQueryBoundP_bind_le (m := q' η) ((isQueryBoundP_withQueryLog_iff _ _ _).2 (hA η))
      (fun r _ => ?_) le_rfl) (by simp)
  cases (M.firstArgs r.2)[(bitsEquiv (k η) c : ℕ)]? with
  | none => exact hd η
  | some q => exact isQueryBoundP_pure _ _ _

end Machine

/-! ## The uniform guess -/

/-- **Averaging over drawn bits.** Let the events `E j` depend on the attacker tape only through its
bits below `off`, and let the `k` bits from `off` fit on the tape. Over uniform tapes, the sum of
the probabilities of `E j` for `j < 2 ^ k` is `2 ^ k` times the probability of `E j` at the number
`j` that the bits `[off, off + k)` spell (`bitsEquiv`). The proof is the involution of (bits,
tape) that swaps the bits with that block of the tape. -/
theorem sum_prEvent_eq_two_pow_mul (off k : ℕ) (hk : off + k ≤ M.lenA η)
    (E : ℕ → M.Tape η → Prop)
    (hE : ∀ j ρa ρa' ρh, (∀ i < off, M.readBit ρa i = M.readBit ρa' i) →
      E j (ρa, ρh) → E j (ρa', ρh)) :
    ∑ j ∈ Finset.range (2 ^ k), Pr{let ρ ← $ᵗ (M.Tape η)}[E j ρ] =
      2 ^ k * Pr{let ρ ← $ᵗ (M.Tape η)}[E (bitsEquiv k (M.bitsAt ρ.1 off k)) ρ] := by
  let σf : (Fin k → Bool) × M.Tape η → (Fin k → Bool) × M.Tape η := fun x =>
    (M.bitsAt x.2.1 off k, (M.setBlock off x.2.1 x.1, x.2.2))
  have hσ : Function.Involutive σf := fun x => by
    simp only [σf, M.bitsAt_setBlock _ _ _ hk, Model.setBlock_setBlock, Model.setBlock_bitsAt]
  -- The joint probability of `E (j c) ρ`, with `c` drawn, is that of `E (j (bits of ρ)) ρ`.
  have h1 : Pr{let x ← $ᵗ ((Fin k → Bool) × M.Tape η)}[E (bitsEquiv k x.1) x.2] =
      Pr{let ρ ← $ᵗ (M.Tape η)}[E (bitsEquiv k (M.bitsAt ρ.1 off k)) ρ] := by
    rw [← SampleableType.prEvent_uniformSample_equiv (Function.Involutive.toPerm σf hσ)]
    refine (prEvent_congr _ _ (fun x => E (bitsEquiv k (M.bitsAt x.2.1 off k)) x.2)
      fun x => ⟨hE _ _ _ _ fun i hi => M.readBit_setBlock_of_lt _ _ hi,
        hE _ _ _ _ fun i hi => (M.readBit_setBlock_of_lt _ _ hi).symm⟩).trans ?_
    rw [SampleableType.prEvent_uniformSample_prod]
    dsimp only
    exact OracleComp.prEvent_bind_const ($ᵗ (Fin k → Bool)) _
  -- The joint probability is the average over the drawn bits.
  have h2 : Pr{let x ← $ᵗ ((Fin k → Bool) × M.Tape η)}[E (bitsEquiv k x.1) x.2] =
      ∑ c : Fin k → Bool, ((2 : ENNReal) ^ k)⁻¹ *
        Pr{let ρ ← $ᵗ (M.Tape η)}[E (bitsEquiv k c) ρ] := by
    rw [SampleableType.uniformSample_prod_eq_bind, prEvent_bind_eq_sum_fintype]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [SampleableType.prEvent_uniformSample_eq_singleton_natCard]
    congr 1
    · rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      push_cast
      rfl
    · rw [show (do let b ← $ᵗ (M.Tape η); pure (c, b) : ProbComp _) =
        Prod.mk c <$> ($ᵗ (M.Tape η)) from (map_eq_bind_pure_comp _ _ _).symm, prEvent_map]
  have h3 : ∑ j ∈ Finset.range (2 ^ k), Pr{let ρ ← $ᵗ (M.Tape η)}[E j ρ] =
      ∑ c : Fin k → Bool, Pr{let ρ ← $ᵗ (M.Tape η)}[E (bitsEquiv k c) ρ] := by
    rw [Finset.sum_range fun j => Pr{let ρ ← $ᵗ (M.Tape η)}[E j ρ]]
    exact (Equiv.sum_comp (bitsEquiv k)
      fun i : Fin (2 ^ k) => Pr{let ρ ← $ᵗ (M.Tape η)}[E i ρ]).symm
  rw [h3, ← h1, h2, ← Finset.mul_sum, ← mul_assoc,
    ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
    one_mul]

end Interop.Squirrel
