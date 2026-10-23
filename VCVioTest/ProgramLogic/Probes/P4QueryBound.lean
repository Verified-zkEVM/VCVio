module

public import VCVio
public import HashSig
public meta import VCVio.ProgramLogic.Tactics
public import Mathlib.Util.CountHeartbeats

-- A probe: its proofs are measurements, not library code, so Mathlib's style set is off.
set_option linter.mathlibStandardSet false

/-!
# Probe P4: query bounds through a core reading

A *budget reading* of oracle computations: assertions are `ℕ → Prop`, indexed by the number of
queries left; a call needs a positive budget and continues at one less (`budgetSpec`, a PolyFun
`OpSpec` folded by `OpSpec.toMAlgOrdered`). `⦃ fun k => n ≤ k ⦄ oa ⦃ fun _ _ => True ⦄` is
`IsTotalQueryBound oa n` (`isTotalQueryBound_iff_triple`), and core `vcgen` steps through a `do`
program call by call, carrying the remaining budget as the state argument. An opaque sub-program
enters through its bound (`Spec.ofBound`): it needs `L` queries left and continues at every
budget `j ≥ n - L`. The verification conditions are linear arithmetic.

PolyFun's charge reading (`OpSpec.charge`, `isTotalRollBound_iff_wpFold_charge`) is not used: its
upper triple keeps the continuation under `⨆ b, …` (the `Spec.lift_upper` precondition), so
`vcgen` decomposes one call and stops. `triple_liftM_*` consume a bound; they do not prove one.

Notes: (1) `vcgen … with lia` failed on the symbolic-budget VCs (it did not use the
truncated-subtraction hypotheses) where `all_goals omega` succeeds; (2) nonlinear budgets
(`2 ^ z * L`) are `generalize`d first; (3) `Spec.bind` did not match the `layers + 2` equation of
`signFromPositionWith`, whose bind is at `Vector _ (layers + 1 + 1)`, until the goal was `change`d
to that index; (4) `fun left =>` does not parse once `VCVio.ProgramLogic.Tactics` is imported.
-/

public section

namespace VCVioTest.ProgramLogic.Probes.P4QueryBound

open OracleSpec OracleComp Std.WP PFunctor

set_option experimental.vcgen true

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {α β : Type}

/-! ## The budget reading -/

/-- The budget reading: with `n` queries left, a call needs `0 < n` and continues at `n - 1`. -/
def budgetSpec (spec : OracleSpec.{0, 0} ι) : OpSpec spec.toPFunctor (ℕ → Prop) :=
  fun _ k n => 0 < n ∧ ∀ b, k b (n - 1)

theorem budgetSpec_mono : (budgetSpec spec).Monotone :=
  fun _ _ _ h _ hn => ⟨hn.1, fun b => h b _ (hn.2 b)⟩

/-- The budget reading of oracle computations (PolyFun's `OpSpec.toWPMonad`, inlined: its
module `PolyFun.PFunctor.Free.WP.Upstream` is not built in this workspace). -/
noncomputable scoped instance (priority := 1300) instBudgetWP :
    WPMonad (OracleComp spec) (ℕ → Prop) EStack⟨⟩ :=
  letI := (budgetSpec spec).toMAlgOrdered budgetSpec_mono
  MAlgOrdered.toWPMonad

open scoped VCVioTest.ProgramLogic.Probes.P4QueryBound

theorem wp_budget (oa : OracleComp spec α) (Q : α → ℕ → Prop) (E : EStack⟨⟩) :
    wp oa Q E = FreeM.wpFold (budgetSpec spec) oa Q :=
  FreeM.toMAlgOrdered_μ_bind_pure _ budgetSpec_mono oa Q

/-- With every leaf satisfied, the budget fold is the total query bound. -/
theorem wpFold_budget_true_iff (oa : OracleComp spec α) (n : ℕ) :
    FreeM.wpFold (budgetSpec spec) oa (fun _ _ => True) n ↔ IsTotalQueryBound oa n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => exact iff_of_true trivial trivial
  | query_bind t mx ih =>
    rw [isTotalQueryBound_query_bind_iff]
    exact and_congr_right fun _ => forall_congr' fun u => ih u (n - 1)

/-- The budget reading's triple at the trivial postcondition is a total query bound. -/
theorem isTotalQueryBound_iff_triple (oa : OracleComp spec α) (n : ℕ) :
    IsTotalQueryBound oa n ↔ ⦃ fun k => n ≤ k ⦄ oa ⦃ fun _ _ => True ⦄ := by
  rw [Triple.iff, wp_budget]
  exact ⟨fun h k hk => (wpFold_budget_true_iff oa k).2 (h.mono hk),
    fun h => (wpFold_budget_true_iff oa n).1 (h n le_rfl)⟩

/-- The exact rule of a primitive query, with lattice connectives so that `vcgen` splits it. -/
@[spec]
theorem Spec.query (t : spec.Domain) (Q : spec.Range t → ℕ → Prop) {E : EStack⟨⟩} :
    ⦃ Lean.Order.meet (fun n => 0 < n) (Lean.Order.iInf fun u => fun n => Q u (n - 1)) ⦄
      (query t : OracleComp spec (spec.Range t)) ⦃ Q; E ⦄ := by
  constructor
  rw [wp_budget]
  intro n h
  simp only [MAlgOrdered.meet_eq_inf, MAlgOrdered.iInf_eq_iInf, Pi.inf_apply, iInf_apply,
    inf_Prop_eq, iInf_Prop_eq] at h
  exact h

/-- A program within budget `L` runs from any budget `n ≥ L` and leaves at least `n - L`. -/
theorem wpFold_budget_of_isTotalQueryBound {x : OracleComp spec α} {L : ℕ}
    (h : IsTotalQueryBound x L) (Q : α → ℕ → Prop) (n : ℕ) (hn : L ≤ n)
    (hQ : ∀ a j, n - L ≤ j → Q a j) : FreeM.wpFold (budgetSpec spec) x Q n := by
  induction x using OracleComp.inductionOn generalizing n L with
  | pure x => exact hQ x n (Nat.sub_le n L)
  | query_bind t mx ih =>
    rw [isTotalQueryBound_query_bind_iff] at h
    exact ⟨by omega, fun u => ih u (h.2 u) (n - 1) (by omega) fun a j hj => hQ a j (by omega)⟩

/-- An opaque sub-program within budget `L`, as a rule `vcgen` splits: it needs `L` queries left
and continues at every budget `j ≥ n - L`. Not registered; `vcgen [Spec.ofBound h]`. -/
theorem Spec.ofBound {x : OracleComp spec α} {L : ℕ} (h : IsTotalQueryBound x L)
    (Q : α → ℕ → Prop) {E : EStack⟨⟩} :
    ⦃ Lean.Order.meet (fun n => L ≤ n) (Lean.Order.iInf fun a => Lean.Order.iInf fun j =>
        Lean.Order.himp (fun n => n - L ≤ j) fun _ => Q a j) ⦄
      x ⦃ Q; E ⦄ := by
  constructor
  rw [wp_budget]
  intro n hn
  simp only [MAlgOrdered.meet_eq_inf, MAlgOrdered.iInf_eq_iInf, Pi.inf_apply, inf_Prop_eq,
    _root_.iInf_apply, iInf_Prop_eq, Lean.Order.himp_apply, Lean.Order.himp_prop_eq_imp] at hn
  exact wpFold_budget_of_isTotalQueryBound h Q n hn.1 hn.2

theorem toy (t : spec.Domain) :
    ⦃ fun k => 2 ≤ k ⦄ (do let a ← query t; let b ← query t; pure (a, b) : OracleComp spec _)
      ⦃ fun _ _ => True ⦄ := by
  vcgen with lia

theorem toy_ofBound (x : OracleComp spec α) (y : α → OracleComp spec β) (hx : IsTotalQueryBound x 3)
    (hy : ∀ a, IsTotalQueryBound (y a) 4) :
    ⦃ fun k => 7 ≤ k ⦄ (do let a ← x; y a) ⦃ fun _ _ => True ⦄ := by
  vcgen [Spec.ofBound hx, Spec.ofBound (hy _)] with lia

/-! ## Merkle traversal bounds -/

section Merkle

open PerfectMerkleTree

variable {Y : Type}

/-- Copied verbatim (it is `private` upstream). -/
theorem tree_query_budget_succ (z leafBudget nodeBudget : ℕ) :
    2 * (2 ^ z * leafBudget + (2 ^ z - 1) * nodeBudget) + nodeBudget =
      2 ^ (z + 1) * leafBudget + (2 ^ (z + 1) - 1) * nodeBudget := by
  have hpow : 0 < 2 ^ z := pow_pos (by decide) _
  rw [pow_succ, Nat.mul_comm (2 ^ z) 2]
  have hcoeff : 2 * (2 ^ z - 1) + 1 = 2 * 2 ^ z - 1 := by omega
  calc
    2 * (2 ^ z * leafBudget + (2 ^ z - 1) * nodeBudget) + nodeBudget =
        (2 * 2 ^ z) * leafBudget + (2 * (2 ^ z - 1) + 1) * nodeBudget := by ring
    _ = (2 * 2 ^ z) * leafBudget + (2 * 2 ^ z - 1) * nodeBudget := by rw [hcoeff]

#count_heartbeats in
/-- `PerfectMerkleTree.isTotalQueryBound_merkleRootM`, copied verbatim (binders `left`/`right`
renamed: the tactic imports make `left` a token). -/
theorem merkleRootM_old
    (leaf : ℕ → OracleComp spec Y)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y)
    (leafBudget nodeBudget z t : ℕ)
    (hleaf : ∀ i, IsTotalQueryBound (leaf i) leafBudget)
    (hnode : ∀ h i l r, IsTotalQueryBound (nodeHash h i l r) nodeBudget) :
    IsTotalQueryBound (merkleRootM leaf nodeHash z t)
      (2 ^ z * leafBudget + (2 ^ z - 1) * nodeBudget) := by
  induction z generalizing t with
  | zero => simpa [merkleRootM] using hleaf t
  | succ z ih =>
      simp only [merkleRootM]
      have hleft := ih (2 * t)
      have hright := ih (2 * t + 1)
      have hboth := isTotalQueryBound_bind hleft fun l =>
        isTotalQueryBound_bind hright fun r => hnode (z + 1) t l r
      refine hboth.mono ?_
      rw [← tree_query_budget_succ]
      omega

#count_heartbeats in
/-- The same bound through the budget reading. -/
theorem merkleRootM_new
    (leaf : ℕ → OracleComp spec Y)
    (nodeHash : ℕ → ℕ → Y → Y → OracleComp spec Y)
    (leafBudget nodeBudget z t : ℕ)
    (hleaf : ∀ i, IsTotalQueryBound (leaf i) leafBudget)
    (hnode : ∀ h i l r, IsTotalQueryBound (nodeHash h i l r) nodeBudget) :
    IsTotalQueryBound (merkleRootM leaf nodeHash z t)
      (2 ^ z * leafBudget + (2 ^ z - 1) * nodeBudget) := by
  induction z generalizing t with
  | zero => simpa [merkleRootM] using hleaf t
  | succ z ih =>
    rw [isTotalQueryBound_iff_triple, ← tree_query_budget_succ]
    generalize 2 ^ z * leafBudget + (2 ^ z - 1) * nodeBudget = B at ih ⊢
    vcgen [merkleRootM, Spec.ofBound (ih _), Spec.ofBound (hnode _ _ _ _)]
    all_goals omega

end Merkle

/-! ## HashSig: XMSS sign-then-recover and the hypertree signing loop -/

section HashSig

open SLHDSA SLHDSA.GeneralHypertree

variable {p : Params}

#count_heartbeats in
/-- `SLHDSA.GeneralHypertree.xmssSignRecoverPairM_isTotalQueryBound`, copied verbatim. -/
theorem xmssSignRecoverPairM_old (core : CorePrimitives p)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (idx : ℕ) :
    IsTotalQueryBound ((do
      let sig ← xmssSignM core msg sk pk adrs idx
      let root ← xmssPkFromSigM core idx sig msg pk adrs
      return (sig, root)) :
        OracleComp (publicHashSpec core) (XmssSig p core × core.Y))
      (xmssCycleQueryBound p) := by
  have hbound := isTotalQueryBound_bind
    (xmssSignM_isTotalQueryBound core msg sk pk adrs idx) fun sig =>
      isTotalQueryBound_bind
        (xmssPkFromSigM_isTotalQueryBound core idx sig msg pk adrs) fun root =>
          show IsTotalQueryBound
            (pure (sig, root) : OracleComp (publicHashSpec core) _) 0 from trivial
  unfold xmssCycleQueryBound
  have hpartition := sum_chainStepsCore_add_sum_complement core msg
  simpa [← Nat.add_assoc, hpartition, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound

#count_heartbeats in
theorem xmssSignRecoverPairM_new (core : CorePrimitives p)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (idx : ℕ) :
    IsTotalQueryBound ((do
      let sig ← xmssSignM core msg sk pk adrs idx
      let root ← xmssPkFromSigM core idx sig msg pk adrs
      return (sig, root)) :
        OracleComp (publicHashSpec core) (XmssSig p core × core.Y))
      (xmssCycleQueryBound p) := by
  rw [isTotalQueryBound_iff_triple, xmssCycleQueryBound,
    ← sum_chainStepsCore_add_sum_complement core msg]
  vcgen [Spec.ofBound (xmssSignM_isTotalQueryBound core msg sk pk adrs idx),
    Spec.ofBound (xmssPkFromSigM_isTotalQueryBound core idx _ msg pk adrs)]
  all_goals omega

#count_heartbeats in
/-- `SLHDSA.GeneralHypertree.signFromPositionM_isTotalQueryBound`, copied verbatim. -/
theorem signFromPositionM_old (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (sk : core.SkSeed) (pk : core.PkSeed)
    (recoverFinal : Bool) (pos : LayerPosition vp) (layers : ℕ)
    (hremaining : pos.layer.val + layers = vp.params.d) (msg : core.Y) :
    IsTotalQueryBound
      (signFromPositionM vp core sk pk recoverFinal pos layers hremaining msg :
        OracleComp (publicHashSpec core) (Vector (XmssSig vp.params core) layers))
      (signLoopQueryBound vp.params recoverFinal layers) := by
  induction layers using Nat.twoStepInduction generalizing recoverFinal pos msg with
  | zero => trivial
  | one =>
      cases recoverFinal with
      | false =>
          simpa [signFromPositionM, signFromPositionWith, xmssSignM,
            signLoopQueryBound] using
            isTotalQueryBound_bind
              (xmssSignM_isTotalQueryBound_coarse core msg sk pk pos.toAdrs pos.leaf.val)
              (fun sig => show IsTotalQueryBound
                (pure #v[sig] : OracleComp (publicHashSpec core) _) 0 from trivial)
      | true =>
          have hbound := isTotalQueryBound_bind
            (xmssSignRecoverPairM_isTotalQueryBound core msg sk pk pos.toAdrs pos.leaf.val)
            (fun sigAndRoot => show IsTotalQueryBound
              (pure #v[sigAndRoot.1] : OracleComp (publicHashSpec core) _) 0 from trivial)
          simpa [signFromPositionM, signFromPositionWith, xmssSignM, xmssPkFromSigM,
            signLoopQueryBound, bind_assoc] using hbound
  | more layers _ ih =>
      let next := pos.next (by omega)
      have hbound := isTotalQueryBound_bind
        (xmssSignRecoverPairM_isTotalQueryBound core msg sk pk pos.toAdrs pos.leaf.val)
        (fun pair => isTotalQueryBound_bind
          (ih (recoverFinal := false) (pos := next)
            (hremaining := by simp [next]; omega) (msg := pair.2))
          (fun rest => show IsTotalQueryBound
            (pure (rest.insertIdx 0 pair.1) : OracleComp (publicHashSpec core) _) 0 from trivial))
      simpa [signFromPositionM, signFromPositionWith, xmssSignM, xmssPkFromSigM,
        signLoopQueryBound, next, bind_assoc] using hbound

#count_heartbeats in
theorem signFromPositionM_new (vp : ValidatedParams)
    (core : CorePrimitives vp.params) (sk : core.SkSeed) (pk : core.PkSeed)
    (recoverFinal : Bool) (pos : LayerPosition vp) (layers : ℕ)
    (hremaining : pos.layer.val + layers = vp.params.d) (msg : core.Y) :
    IsTotalQueryBound
      (signFromPositionM vp core sk pk recoverFinal pos layers hremaining msg :
        OracleComp (publicHashSpec core) (Vector (XmssSig vp.params core) layers))
      (signLoopQueryBound vp.params recoverFinal layers) := by
  induction layers using Nat.twoStepInduction generalizing recoverFinal pos msg with
  | zero => trivial
  | one =>
    rw [isTotalQueryBound_iff_triple, signFromPositionM, signFromPositionWith]
    simp only [xmssSignWith_publicHash_eq_xmssSignM, xmssPkFromSigWith_publicHash_eq_xmssPkFromSigM]
    vcgen [Spec.ofBound (xmssSignM_isTotalQueryBound core msg sk pk _ _),
      Spec.ofBound (xmssPkFromSigM_isTotalQueryBound core _ _ msg pk _)]
    all_goals
      have := sum_chainStepsCore_add_sum_complement core msg
      cases recoverFinal <;> simp_all [signLoopQueryBound, xmssCycleQueryBound, xmssSignQueryBound] <;>
        omega
  | more layers _ ih =>
    have hfold : ∀ rf pos l h msg, signFromPositionWith vp core (PublicHash.f core pk)
        (PublicHash.tl core pk) (PublicHash.h core pk) sk pk rf pos l h msg =
          (signFromPositionM vp core sk pk rf pos l h msg : OracleComp (publicHashSpec core) _) :=
      fun _ _ _ _ _ => rfl
    rw [isTotalQueryBound_iff_triple]
    change Triple (signFromPositionM vp core sk pk recoverFinal pos (layers + 1 + 1) hremaining msg :
      OracleComp (publicHashSpec core) (Vector _ (layers + 1 + 1))) _ _ _
    vcgen [signFromPositionM, signFromPositionWith, xmssSignWith_publicHash_eq_xmssSignM,
      xmssPkFromSigWith_publicHash_eq_xmssPkFromSigM, hfold,
      Spec.ofBound (xmssSignM_isTotalQueryBound core msg sk pk _ _),
      Spec.ofBound (xmssPkFromSigM_isTotalQueryBound core _ _ msg pk _), Spec.ofBound (ih _ _ _ _)]
    all_goals
      have := sum_chainStepsCore_add_sum_complement core msg
      simp only [signLoopQueryBound, xmssCycleQueryBound] at *
      omega

end HashSig

end VCVioTest.ProgramLogic.Probes.P4QueryBound
