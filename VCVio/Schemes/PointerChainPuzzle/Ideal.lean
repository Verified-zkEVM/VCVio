/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.Schemes.PointerChainPuzzle.Path
public import VCVio.OracleComp.QueryTracking.RandomOracle.DependentTable
public import VCVio.EvalDist.Monad.Disagreement.Measure

/-!
# Masked links and programmed path answers for the pointer-chain puzzle

The first two game hops of the delay proof of the pointer-chain puzzle (`scheme`), in the lazy
random oracle model.

## The link change of variables

For a fixed salt and fixed oracles, the links `xs` and the pair of the first link and the masked
links `z_i = μ_i + x_{i+1}` determine each other (`linkEquiv`, the bijection `maskLinks`). The
generator `genMasked` draws the salt, the first link and the masked links uniformly and unmasks
each later link from the mask answer of the chain before it; `maskedScheme` is the puzzle with this
generator. Against every cache of the random oracle the two generators have the same output
distribution (`evalDist_genMasked_run'`), so the two puzzles have the same delay advantage
(`delayAdvantage_maskedScheme`). The proof answers the hash queries from a full answer table
(`OracleComp.evalDist_simulateQ_romImpl_run'_eq_completeTable`), and needs the context type to be
finite so that the points are.

## The programming theorem

A labelling `ℓ : Labels n m S L` assigns a value to every path value; `labelPuzzle` is the puzzle
committing to its key label. `Bad` holds for the cache `c` left by the preprocessing phase when
(a) two distinct path values share a path input, or (b) a path input is already in `c`.
`programmedCache` writes each label at its path input over `c`; off `Bad` it answers each path
input with its label (`programmedCache_pathInput`).

Against the lazy random oracle, the generator's fresh path answers are presampled as a labelling,
which turns its path queries into the deterministic run `presetRun`
(`evalDist_run_queryPath_bind`); off `Bad`, that run reaches the programmed cache
(`presetRun_order_of_not_bad`). The delay experiment of `maskedScheme` is therefore the draw of a
`Seed` (the preprocessing state and lazy cache, the salt, the first and masked links and the
latent labels) followed by `realRest`, and `programmedExperiment` draws the same seed and runs the
online phase from the programmed cache, returning whether the adversary wins and whether `Bad`
holds. The two agree off `Bad`, so the delay advantage and the programmed winning probability
differ by at most the probability of `Bad` in the programmed experiment, on either side
(`delayAdvantage_maskedScheme_le`, `programmedExperiment_win_le`) and in absolute value
(`abs_delayAdvantage_maskedScheme_sub_le`, and `abs_delayAdvantage_scheme_sub_le` for `scheme`
through the link change of variables).
-/

public section

open OracleSpec OracleComp MeasureTheory

/-! ## The lazy random oracle with uniform forwarding against a full table -/

namespace OracleComp

/-! ### Helpers for stateful handlers -/

/-- A single-point round, answered by the rounds of a point handler, is that handler's answer. -/
lemma simulateQ_add_batch_queryPoint {ι : Type} {spec : OracleSpec.{0, 0} ι}
    {m : Type → Type} [Monad m] [LawfulMonad m] (impl₁ : QueryImpl unifSpec m)
    (impl₂ : QueryImpl spec m) (t : ι) :
    simulateQ (impl₁ + impl₂.batch) (queryPoint t) = impl₂ t := by
  simp only [queryPoint, queryRound, queryRound₂, simulateQ_map, simulateQ_spec_query,
    QueryImpl.add_apply_inr, Functor.map_map]
  change (fun a => (splitAnswers (fun _ : Fin 1 => t) Fin.elim0 a).1 0) <$> impl₂.batch [t] = _
  simp only [QueryImpl.batch_cons, QueryImpl.batch_nil, map_pure, bind_pure_comp]
  refine (Functor.map_map _ _ _).trans ((congrArg (· <$> impl₂ t) ?_).trans (id_map _))
  funext a
  rfl

/-- A lifted `ProbComp`, run beside uniform forwarding, samples and leaves the cache. -/
lemma run_simulateQ_unifFwdImpl_add_liftM {ι τ : Type} {spec : OracleSpec.{0, 0} ι}
    {spec' : OracleSpec.{0, 0} τ} (impl : QueryImpl spec' (StateT spec.QueryCache ProbComp))
    {α : Type} (oa : ProbComp α) (c : spec.QueryCache) :
    (simulateQ (unifFwdImpl spec + impl) (liftM oa : OracleComp (unifSpec + spec') α)).run c =
      (·, c) <$> oa := by
  rw [show simulateQ (unifFwdImpl spec + impl) (liftM oa : OracleComp (unifSpec + spec') α) =
      simulateQ (unifFwdImpl spec) oa from QueryImpl.simulateQ_add_liftComp_left _ _ oa,
    unifFwdImpl.simulateQ_run]

/-- Running a bind through a stateful handler runs the continuation from the reached state. -/
lemma run_simulateQ_bind {ι σ α β : Type} {spec : OracleSpec.{0, 0} ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (oa : OracleComp spec α)
    (f : α → OracleComp spec β) (s : σ) :
    (simulateQ impl (oa >>= f)).run s =
      (simulateQ impl oa).run s >>= fun p => (simulateQ impl (f p.1)).run p.2 := by
  rw [simulateQ_bind, StateT.run_bind]

/-- `run_simulateQ_bind` for the output alone. -/
lemma run'_simulateQ_bind {ι σ α β : Type} {spec : OracleSpec.{0, 0} ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (oa : OracleComp spec α)
    (f : α → OracleComp spec β) (s : σ) :
    (simulateQ impl (oa >>= f)).run' s =
      (simulateQ impl oa).run s >>= fun p => (simulateQ impl (f p.1)).run' p.2 := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

/-- A uniform draw, transported along an equality of types, is uniform. -/
lemma evalDist_cast_uniformSample {X Y : Type} [SampleableType X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] (h : X = Y) :
    𝒟[cast h <$> ($ᵗ X)] = ProbabilityTheory.uniformOn Set.univ := by
  subst h
  exact (congrArg (fun mx => 𝒟[mx]) (id_map _)).trans SampleableType.evalDist_uniformSample

/-! ### Uniform forwarding against a full table -/

section Table

variable {ι : Type} [DecidableEq ι] [Finite ι] {spec : OracleSpec.{0, 0} ι}
  [∀ t, SampleableType (spec.Range t)] [SampleableType ((t : ι) → spec.Range t)]

/-- Running `oa` in the random oracle model from the cache `c` has the output distribution of
sampling a full answer table `g` uniformly and answering every hash query from `g`, overlaid by
`c`, while uniform queries are sampled as they come. -/
theorem evalDist_simulateQ_romImpl_run'_eq_completeTable {α : Type} [MeasurableSpace α]
    (oa : OracleComp (unifSpec + spec) α) (c : spec.QueryCache) :
    𝒟[(simulateQ spec.romImpl oa).run' c] =
      𝒟[$ᵗ ((t : ι) → spec.Range t) >>= fun g =>
          simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (completeTable c g))) oa] := by
  classical
  let : ∀ t, MeasurableSpace (spec.Range t) := fun _ => ⊤
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a =>
      simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
      rw [OracleComp.evalDist_bind_const]
  | query_bind t k ih =>
      rcases t with n | t
      · have hred :
            (simulateQ spec.romImpl (liftM ((unifSpec + spec).query (.inl n)) >>= k)).run' c =
            (unifSpec.query n : ProbComp _) >>= fun u => (simulateQ spec.romImpl (k u)).run' c := by
          rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind,
            roSim.run_apply_inl]
          simp [StateT.run'_eq]
        have heval : ∀ g : (t : ι) → spec.Range t,
            simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (completeTable c g)))
                (liftM ((unifSpec + spec).query (.inl n)) >>= k) =
              (unifSpec.query n : ProbComp _) >>= fun u =>
                simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (completeTable c g))) (k u) :=
          fun g => by simp [unifFwdAnswerImpl]
        rw [hred]
        simp_rw [heval]
        exact (evalDist_bind_congr_of_support _ _ _ fun u _ => ih u c).trans
          (evalDist_bind_bind_swap_of_countable (α := Fin (n + 1)) _ _ _)
      · have hred :
            (simulateQ spec.romImpl (liftM ((unifSpec + spec).query (.inr t)) >>= k)).run' c =
            (spec.randomOracle t).run c >>= fun p => (simulateQ spec.romImpl (k p.1)).run' p.2 := by
          rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
          rfl
        have heval : ∀ g : (t : ι) → spec.Range t,
            simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (completeTable c g)))
                (liftM ((unifSpec + spec).query (.inr t)) >>= k) =
              simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (completeTable c g)))
                (k (completeTable c g t)) :=
          fun g => by simp [unifFwdAnswerImpl]; rfl
        rw [hred]
        simp_rw [heval]
        rcases hc : c t with _ | u
        · rw [QueryImpl.withCaching_run_none _ hc, map_eq_bind_pure_comp]
          simp only [Function.comp, bind_assoc, pure_bind]
          set ψ : ((t : ι) → spec.Range t) → ProbComp α := fun g =>
            simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (completeTable c g)))
              (k (completeTable c g t)) with hψ
          have hfun : ∀ u : spec.Range t, (fun g : (t : ι) → spec.Range t =>
                simulateQ (unifFwdAnswerImpl (QueryImpl.ofFn (completeTable (c.cacheQuery t u) g)))
                  (k u)) = fun g => ψ (Function.update g t u) := by
            intro u
            funext g
            simp only [hψ]
            rw [completeTable_cacheQuery, ← completeTable_update_of_none c g hc u,
              Function.update_self]
          refine (evalDist_bind_congr_of_support _ _ _ fun u _ =>
            (ih u (c.cacheQuery t u)).trans (by rw [hfun u])).trans ?_
          exact evalDist_bind_bind_update_dependent t _ _
            SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample ψ
        · rw [QueryImpl.withCaching_run_some _ hc, pure_bind, ih u c]
          have h : ∀ g : (t : ι) → spec.Range t, completeTable c g t = u :=
            fun g => by simp [completeTable, hc]
          simp_rw [h]

end Table

end OracleComp

namespace PointerChainPuzzle

variable {n m : ℕ} {S L Salt Ctx : Type}

/-! ## Links and masked links -/

section Links

variable (m : ℕ) (mkCtx : Salt → Ctx) (O : Oracles n S L Salt Ctx) [AddCommGroup L]

/-- The link of chain `k` recovered from the first link `x` and the masked links `z` against the
oracles `O`: `x_0 = x` and `x_{k+1} = z_k - μ_k`, where `μ_k` is the mask of the end of chain `k`
started at `x_k`. -/
@[expose]
def unmaskLink (salt : Salt) (x : L) (z : Fin (n - 1) → L) : ℕ → L
  | 0 => x
  | k + 1 =>
      if h : k < n - 1 then
        z ⟨k, h⟩ - O.mask (mkCtx salt)
          (chainState mkCtx O salt (chainOf ⟨k, h⟩) (unmaskLink salt x z k) m)
      else x

/-- The links recovered from the first link and the masked links (`unmaskLink`). -/
@[expose]
def unmaskLinks (salt : Salt) (x : L) (z : Fin (n - 1) → L) : Fin n → L :=
  fun i => unmaskLink m mkCtx O salt x z i

/-- The first link and the masked links `z_i = μ_i + x_{i+1}` of the links `xs` against the
oracles `O`, as published by the honest puzzle. -/
@[expose]
def maskLinks [NeZero n] (salt : Salt) (xs : Fin n → L) : L × (Fin (n - 1) → L) :=
  (xs 0, fun i => O.mask (mkCtx salt) (chainEnd m mkCtx O salt xs (chainOf i)) + xs (nextChain i))

lemma maskLinks_eq [NeZero n] (initAcc : Ctx → S) (salt : Salt) (xs : Fin n → L) :
    maskLinks m mkCtx O salt xs =
      ((honestPuzzle m mkCtx initAcc O salt xs).firstLink,
        (honestPuzzle m mkCtx initAcc O salt xs).maskedLinks) := rfl

lemma unmaskLink_maskLinks [NeZero n] (salt : Salt) (xs : Fin n → L) (k : ℕ) (hk : k < n) :
    unmaskLink m mkCtx O salt (maskLinks m mkCtx O salt xs).1 (maskLinks m mkCtx O salt xs).2 k =
      xs ⟨k, hk⟩ := by
  induction k with
  | zero => exact congrArg xs (Fin.ext (by simp))
  | succ k ih =>
      have h : k < n - 1 := by omega
      simp only [unmaskLink, h, ↓reduceDIte, ih (by omega)]
      exact add_sub_cancel_left _ _

/-- For fixed oracles and salt, the links and the pair of the first link and the masked links
determine each other: the map is triangular, each masked link `z_i = μ_i + x_{i+1}` depending on
the links up to `x_{i+1}`, and `x ↦ μ + x` is a bijection of `L`. -/
@[expose]
def linkEquiv [NeZero n] (salt : Salt) : (Fin n → L) ≃ L × (Fin (n - 1) → L) where
  toFun := maskLinks m mkCtx O salt
  invFun p := unmaskLinks m mkCtx O salt p.1 p.2
  left_inv xs := funext fun i => unmaskLink_maskLinks m mkCtx O salt xs i i.2
  right_inv p := by
    obtain ⟨x, z⟩ := p
    refine Prod.ext rfl (funext fun i => ?_)
    change O.mask _ (chainState mkCtx O salt _ (unmaskLink m mkCtx O salt x z i) m) +
      unmaskLink m mkCtx O salt x z (i + 1) = z i
    simp only [unmaskLink, i.2, ↓reduceDIte]
    exact add_sub_cancel _ _

lemma linkEquiv_apply [NeZero n] (salt : Salt) (xs : Fin n → L) :
    linkEquiv m mkCtx O salt xs = maskLinks m mkCtx O salt xs := rfl

lemma linkEquiv_symm_apply [NeZero n] (salt : Salt) (p : L × (Fin (n - 1) → L)) :
    (linkEquiv m mkCtx O salt).symm p = unmaskLinks m mkCtx O salt p.1 p.2 := rfl

end Links

/-! ## Labellings -/

instance PathValue.instSampleableTypeVal [SampleableType S] [SampleableType L] :
    (v : PathValue n m) → SampleableType (v.Val S L)
  | .state .. => inferInstanceAs (SampleableType S)
  | .mask _ => inferInstanceAs (SampleableType L)
  | .acc _ => inferInstanceAs (SampleableType S)
  | .key => inferInstanceAs (SampleableType S)
  | .commit => inferInstanceAs (SampleableType S)

/-- A labelling of the path values: one value of the type of each path value. -/
abbrev Labels (n m : ℕ) (S L : Type) := (v : PathValue n m) → v.Val S L

namespace Labels

/-- Labellings as a product of state and link families. -/
@[expose]
def equivProd :
    Labels n m S L ≃ (Fin n → Fin (m + 1) → S) × (Fin (n - 1) → L) × (Fin n → S) × S × S where
  toFun ℓ := (fun i k => ℓ (.state i k), fun i => ℓ (.mask i), fun i => ℓ (.acc i), ℓ .key,
    ℓ .commit)
  invFun p v := match v with
    | .state i k => p.1 i k
    | .mask i => p.2.1 i
    | .acc i => p.2.2.1 i
    | .key => p.2.2.2.1
    | .commit => p.2.2.2.2
  left_inv ℓ := funext fun v => by cases v <;> rfl
  right_inv _ := rfl

instance [SampleableType S] [SampleableType L] : SampleableType (Labels n m S L) :=
  SampleableType.ofEquiv equivProd.symm

/-- The labelling with every state `a` and every link `x`. -/
@[expose]
def const (a : S) (x : L) : Labels n m S L
  | .state .. => a
  | .mask _ => x
  | .acc _ => a
  | .key => a
  | .commit => a

end Labels

/-! ## The order of the path values -/

namespace PathValue

/-- Every path value: the states chain by chain, the masks, the accumulators, the key and the
commitment. -/
@[expose]
def all (n m : ℕ) : List (PathValue n m) :=
  (List.finRange n).flatMap (fun i => (List.finRange (m + 1)).map (.state i)) ++
    (List.finRange (n - 1)).map .mask ++ (List.finRange n).map .acc ++ [.key, .commit]

lemma mem_all (v : PathValue n m) : v ∈ all n m := by
  cases v <;> simp [all]

lemma nodup_all : (all n m).Nodup := by
  simp only [all, List.nodup_append, List.nodup_flatMap, List.nodup_cons, List.nodup_nil]
  refine ⟨⟨⟨⟨fun i _ => (List.nodup_finRange _).map fun _ _ h => by cases h; rfl,
    (List.nodup_finRange n).pairwise_of_forall_ne fun i _ j _ hij => ?_⟩,
    (List.nodup_finRange _).map fun _ _ h => by cases h; rfl, ?_⟩,
    (List.nodup_finRange _).map fun _ _ h => by cases h; rfl, ?_⟩, by simp, ?_⟩
  · simp only [Function.onFun, List.disjoint_left, List.mem_map]
    rintro _ ⟨_, _, rfl⟩ ⟨_, _, h⟩
    cases h
    exact hij rfl
  all_goals intro a; cases a <;> simp

/-- The path values in the order of the rounds in which the honest solver receives them
(`PathValue.rho`). -/
@[expose]
def order (n m : ℕ) : List (PathValue n m) :=
  (all n m).insertionSort fun v w => v.rho ≤ w.rho

lemma mem_order (v : PathValue n m) : v ∈ order n m :=
  (List.perm_insertionSort _ _).symm.subset (mem_all v)

lemma nodup_order : (order n m).Nodup :=
  (List.perm_insertionSort _ _).nodup_iff.mpr nodup_all

lemma pairwise_order : (order n m).Pairwise fun v w => v.rho ≤ w.rho := by
  have : Std.Total fun v w : PathValue n m => v.rho ≤ w.rho := ⟨fun _ _ => le_total _ _⟩
  have : IsTrans (PathValue n m) fun v w => v.rho ≤ w.rho := ⟨fun _ _ _ => le_trans⟩
  exact List.pairwise_insertionSort _ _

lemma rho_lt_of_mem_preds [NeZero n] {v w : PathValue n m} (h : w ∈ v.preds) :
    w.rho < v.rho := by
  by_cases hv : v = firstStart
  · subst hv
    simp [(preds_eq_empty_iff _).mpr rfl] at h
  · rw [rho_eq_sup_preds hv]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := rho) h)

/-- In a list of path values ordered by `rho`, no predecessor of the head occurs. -/
lemma not_mem_of_mem_preds [NeZero n] {v w : PathValue n m} {vs : List (PathValue n m)}
    (hs : (v :: vs).Pairwise fun v w => v.rho ≤ w.rho) (hw : w ∈ v.preds) : w ∉ v :: vs := by
  have hlt := rho_lt_of_mem_preds hw
  rintro (_ | ⟨_, hw'⟩)
  · exact lt_irrefl _ hlt
  · exact absurd ((List.pairwise_cons.mp hs).1 w hw') (not_le.mpr hlt)

end PathValue

/-! ## Puzzles, path inputs and Bad from a labelling -/

section Labelled

/-- The puzzle with the salt, the first link `x`, the masked links `z` and the commitment
`ℓ .commit`. -/
@[expose]
def labelPuzzle (salt : Salt) (x : L) (z : Fin (n - 1) → L) (ℓ : Labels n m S L) :
    Puzzle n S L Salt :=
  ⟨salt, ℓ .commit, x, z⟩

variable (m : ℕ) (mkCtx : Salt → Ctx) (initAcc : Ctx → S)

variable [NeZero n] [AddCommGroup L]

/-- The path inputs depend on the puzzle only through its salt, first link and masked links. -/
lemma pathInput_eq_of_eq {P P' : Puzzle n S L Salt} (hs : P.salt = P'.salt)
    (hx : P.firstLink = P'.firstLink) (hz : P.maskedLinks = P'.maskedLinks) :
    pathInput m mkCtx initAcc P = pathInput m mkCtx initAcc P' := by
  funext ν v
  rcases v with ⟨⟨_ | i, hi⟩, ⟨_ | k, hk⟩⟩ | i | ⟨_ | i, hi⟩ | _ | _ <;>
    simp [pathInput, hs, hx, hz]

/-- The path inputs of a puzzle do not depend on its commitment. -/
lemma pathInput_labelPuzzle (salt : Salt) (x : L) (z : Fin (n - 1) → L) (ν ν' : Labels n m S L) :
    pathInput m mkCtx initAcc (labelPuzzle salt x z ν) =
      pathInput m mkCtx initAcc (labelPuzzle salt x z ν') :=
  pathInput_eq_of_eq m mkCtx initAcc rfl rfl rfl

/-- `Bad` for the generator, for the cache `c` left by the preprocessing phase, a puzzle and a
labelling: (a) two distinct path values have the same path input, or (b) a path input is already
in `c`. -/
@[expose]
def Bad (c : (oracleSpec n S L Salt Ctx).QueryCache) (P : Puzzle n S L Salt)
    (ℓ : Labels n m S L) : Prop :=
  (∃ v w, v ≠ w ∧ pathInput m mkCtx initAcc P ℓ v = pathInput m mkCtx initAcc P ℓ w) ∨
    ∃ v, (c (pathInput m mkCtx initAcc P ℓ v)).isSome

instance [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
    (c : (oracleSpec n S L Salt Ctx).QueryCache) (P : Puzzle n S L Salt) (ℓ : Labels n m S L) :
    Decidable (Bad m mkCtx initAcc c P ℓ) := by
  unfold Bad
  infer_instance

variable [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]

/-- Write the label `ℓ v` at the path input of each path value `v` of `vs`, in order. -/
@[expose]
def programCache (P : Puzzle n S L Salt) (ℓ : Labels n m S L) :
    List (PathValue n m) → (oracleSpec n S L Salt Ctx).QueryCache →
      (oracleSpec n S L Salt Ctx).QueryCache
  | [], c => c
  | v :: vs, c => programCache P ℓ vs
      (c.cacheQuery (pathInput m mkCtx initAcc P ℓ v)
        (cast (range_pathInput m mkCtx initAcc P ℓ v).symm (ℓ v)))

/-- The programmed cache: the cache `c` left by the preprocessing phase, extended by the label
`ℓ v` at the path input of every path value `v`. -/
@[expose]
def programmedCache (c : (oracleSpec n S L Salt Ctx).QueryCache) (P : Puzzle n S L Salt)
    (ℓ : Labels n m S L) : (oracleSpec n S L Salt Ctx).QueryCache :=
  programCache m mkCtx initAcc P ℓ (PathValue.order n m) c

end Labelled

/-! ## The generator with masked links -/

section Generator

variable (m : ℕ) (mkCtx : Salt → Ctx) (initAcc : Ctx → S) [NeZero n] [AddCommGroup L]

/-- Query the path values `vs` in order, one per round, writing each answer into the labelling:
the path input of each value is formed from the puzzle `P` and the labelling so far. -/
@[expose]
def queryPath (P : Puzzle n S L Salt) :
    List (PathValue n m) → Labels n m S L → RoundComp n S L Salt Ctx (Labels n m S L)
  | [], ν => pure ν
  | v :: vs, ν => do
      let u ← queryPoint (pathInput m mkCtx initAcc P ν v)
      queryPath P vs (Function.update ν v (cast (range_pathInput m mkCtx initAcc P ν v) u))

/-- The generator on a salt, a first link `x` and masked links `z`: it follows the path values in
the order in which the honest solver receives them (`PathValue.order`), so that each link
`x_{i+1} = z_i - μ_i` is unmasked by the mask answer `μ_i` of chain `i`, and publishes the
answer at the commitment input. The initial labelling is overwritten before it is read. -/
@[expose]
def genMaskedWith (salt : Salt) (x : L) (z : Fin (n - 1) → L) :
    RoundComp n S L Salt Ctx (Puzzle n S L Salt × S) := do
  let ν₀ : Labels n m S L := Labels.const (initAcc (mkCtx salt)) x
  let ν ← queryPath m mkCtx initAcc (labelPuzzle salt x z ν₀) (PathValue.order n m) ν₀
  return (labelPuzzle salt x z ν, ν .key)

/-- The generator with masked links: draw the salt, the first link and the masked links, and
derive the links from them with the mask answers. -/
@[expose]
def genMasked [SampleableType Salt] [SampleableType L] :
    RoundComp n S L Salt Ctx (Puzzle n S L Salt × S) := do
  let salt ← $ᵗ Salt
  let p ← $ᵗ (L × (Fin (n - 1) → L))
  genMaskedWith m mkCtx initAcc salt p.1 p.2

end Generator

/-- The pointer-chain puzzle with the generator `genMasked`. -/
@[expose]
def maskedScheme (n m : ℕ) [NeZero n] (mkCtx : Salt → Ctx) (initAcc : Ctx → S) [AddCommGroup L]
    [DecidableEq S] [SampleableType Salt] [SampleableType L] :
    TimeLockPuzzle (oracleSpec n S L Salt Ctx) (Puzzle n S L Salt) S where
  gen := genMasked m mkCtx initAcc
  solve := solve m mkCtx initAcc

/-! ## Against fixed oracles -/

lemma Oracles.cast_toImpl_run_congr (O : Oracles n S L Salt Ctx) {a b : Point n S L Salt Ctx}
    (hab : a = b) {X : Type} (ha : (oracleSpec n S L Salt Ctx).Range a = X)
    (hb : (oracleSpec n S L Salt Ctx).Range b = X) :
    cast ha (O.toImpl a).run = cast hb (O.toImpl b).run := by
  subst hab
  rfl

lemma Oracles.simulateQ_liftM (O : Oracles n S L Salt Ctx) {α : Type} (oa : ProbComp α) :
    simulateQ (QueryImpl.batch' (unifFwdAnswerImpl O.toImpl))
      (liftM oa : RoundComp n S L Salt Ctx α) = oa :=
  (QueryImpl.simulateQ_add_liftComp_left _ _ oa).trans (simulateQ_id' oa)

section Fixed

variable {m : ℕ} {mkCtx : Salt → Ctx} {initAcc : Ctx → S} (O : Oracles n S L Salt Ctx)
  [NeZero n] [AddCommGroup L]

/-- The oracles `O` answering every point, rounds point by point. -/
local notation "T" => QueryImpl.batch' (unifFwdAnswerImpl (Oracles.toImpl O))

variable (m mkCtx initAcc) in
/-- The labelling `queryPath` computes against the oracles `O`. -/
@[expose]
def fixedPath (P : Puzzle n S L Salt) : List (PathValue n m) → Labels n m S L → Labels n m S L
  | [], ν => ν
  | v :: vs, ν => fixedPath P vs (Function.update ν v
      (cast (range_pathInput m mkCtx initAcc P ν v)
        (O.toImpl (pathInput m mkCtx initAcc P ν v)).run))

lemma simulateQ_queryPath (P : Puzzle n S L Salt) (vs : List (PathValue n m))
    (ν : Labels n m S L) :
    simulateQ T (queryPath m mkCtx initAcc P vs ν) = pure (fixedPath m mkCtx initAcc O P vs ν) := by
  induction vs generalizing ν with
  | nil => rfl
  | cons v vs ih =>
      rw [queryPath, simulateQ_bind, simulateQ_queryPoint, pure_bind]
      exact ih _

/-- Along a list ordered by `rho`, `fixedPath` writes the labelling `h` when each answer is the
value of `h` as soon as the labelling agrees with `h` on the predecessors. -/
lemma fixedPath_eq (P : Puzzle n S L Salt) (h : Labels n m S L)
    (hh : ∀ v (ν : Labels n m S L), (∀ w ∈ v.preds, ν w = h w) →
      cast (range_pathInput m mkCtx initAcc P ν v)
        (O.toImpl (pathInput m mkCtx initAcc P ν v)).run = h v)
    {vs : List (PathValue n m)} (hs : vs.Pairwise fun v w => v.rho ≤ w.rho) (hnd : vs.Nodup)
    {ν : Labels n m S L} (hν : ∀ w ∉ vs, ν w = h w) :
    fixedPath m mkCtx initAcc O P vs ν = h := by
  induction vs generalizing ν with
  | nil => exact funext fun w => hν w List.not_mem_nil
  | cons v vs ih =>
      refine ih (List.pairwise_cons.mp hs).2 (List.nodup_cons.mp hnd).2 fun w hw => ?_
      by_cases hwv : w = v
      · subst hwv
        rw [Function.update_self]
        exact hh w ν fun w' hw' => hν w' (PathValue.not_mem_of_mem_preds hs hw')
      · rw [Function.update_of_ne hwv]
        exact hν w (by simp [hwv, hw])

/-- Against the oracles `O`, following the path values in order from the masked links of the links
`xs` computes the honest path values of `xs`. -/
lemma fixedPath_order (salt : Salt) (xs : Fin n → L) (ν ν' : Labels n m S L) :
    fixedPath m mkCtx initAcc O
        (labelPuzzle salt (maskLinks m mkCtx O salt xs).1 (maskLinks m mkCtx O salt xs).2 ν')
        (PathValue.order n m) ν =
      honestValue m mkCtx initAcc O salt xs := by
  refine fixedPath_eq O _ _ (fun v ν hν => ?_) PathValue.pairwise_order PathValue.nodup_order
    fun w hw => absurd (PathValue.mem_order w) hw
  rw [honestValue_eq_answer m mkCtx initAcc O salt xs v]
  refine O.cast_toImpl_run_congr ?_ _ _
  rw [pathInput_congr m mkCtx initAcc _ v hν]
  exact congrFun (congrFun (pathInput_eq_of_eq m mkCtx initAcc rfl rfl rfl) _) v

/-- Against the oracles `O`, the generator on the masked links `p` returns the honest puzzle and
key of the links `p` determines (`linkEquiv`). -/
lemma simulateQ_genMaskedWith (salt : Salt) (p : L × (Fin (n - 1) → L)) :
    simulateQ T (genMaskedWith m mkCtx initAcc salt p.1 p.2) =
      pure (honestPuzzle m mkCtx initAcc O salt ((linkEquiv m mkCtx O salt).symm p),
        honestKey m mkCtx initAcc O salt ((linkEquiv m mkCtx O salt).symm p)) := by
  obtain ⟨xs, rfl⟩ := (linkEquiv m mkCtx O salt).surjective p
  rw [Equiv.symm_apply_apply, genMaskedWith, simulateQ_bind, simulateQ_queryPath, pure_bind,
    simulateQ_pure, linkEquiv_apply, fixedPath_order]
  rfl

/-- Against the oracles `O`, the generator with masked links has the output distribution of the
generator, whatever follows it. -/
lemma evalDist_simulateQ_genMasked_bind [SampleableType Salt] [SampleableType L] {β : Type}
    [MeasurableSpace β] (k : Puzzle n S L Salt × S → ProbComp β) :
    𝒟[simulateQ T (genMasked m mkCtx initAcc) >>= k] =
      𝒟[simulateQ T (gen m mkCtx initAcc) >>= k] := by
  simp only [genMasked, gen, simulateQ_bind, bind_assoc, O.simulateQ_liftM,
    simulateQ_genMaskedWith, simulateQ_genWith, pure_bind]
  refine evalDist_bind_congr_of_support _ _ _ fun salt _ => ?_
  let : MeasurableSpace (Fin n → L) := ⊤
  let : MeasurableSpace (L × (Fin (n - 1) → L)) := ⊤
  exact evalDist_bind_bijective_uniform_cross _ _ SampleableType.evalDist_uniformSample
    SampleableType.evalDist_uniformSample _ (linkEquiv m mkCtx O salt).symm.bijective
    fun xs => k (honestPuzzle m mkCtx initAcc O salt xs, honestKey m mkCtx initAcc O salt xs)

end Fixed

/-! ## The link change of variables -/

instance [Finite S] [Finite L] [Finite Salt] [Finite Ctx] : Finite (Point n S L Salt Ctx) := by
  refine Finite.of_injective (β := (Ctx × Fin n × L) ⊕ (Salt × Fin n × S) ⊕ (Ctx × S) ⊕ (S × S) ⊕
    (Ctx × S) ⊕ (Ctx × S))
    (fun
      | .start ctx i x => .inl (ctx, i, x)
      | .step salt i s => .inr (.inl (salt, i, s))
      | .mask ctx y => .inr (.inr (.inl (ctx, y)))
      | .acc a y => .inr (.inr (.inr (.inl (a, y))))
      | .key ctx a => .inr (.inr (.inr (.inr (.inl (ctx, a)))))
      | .commit ctx k => .inr (.inr (.inr (.inr (.inr (ctx, k)))))) ?_
  intro a b h
  cases a <;> cases b <;> simp_all

section Change

variable (m : ℕ) (mkCtx : Salt → Ctx) (initAcc : Ctx → S) [NeZero n] [AddCommGroup L]
  [SampleableType S] [SampleableType L] [SampleableType Salt] [Finite Ctx]
  [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]

/-- From every cache of the random oracle, the generator with masked links has the output
distribution of the generator. -/
theorem evalDist_genMasked_run' [MeasurableSpace (Puzzle n S L Salt × S)]
    (c : (oracleSpec n S L Salt Ctx).QueryCache) :
    𝒟[(simulateQ (oracleSpec n S L Salt Ctx).romImpl
        (simulateQ (oracleSpec n S L Salt Ctx).unbatch (genMasked m mkCtx initAcc))).run' c] =
      𝒟[(simulateQ (oracleSpec n S L Salt Ctx).romImpl
        (simulateQ (oracleSpec n S L Salt Ctx).unbatch (gen m mkCtx initAcc))).run' c] := by
  let : Fintype (Point n S L Salt Ctx) := Fintype.ofFinite _
  let : ∀ t, Fintype ((oracleSpec n S L Salt Ctx).Range t) := fun _ => Fintype.ofFinite _
  let := SampleableType.piOfFintype (oracleSpec n S L Salt Ctx).Range
  rw [evalDist_simulateQ_romImpl_run'_eq_completeTable,
    evalDist_simulateQ_romImpl_run'_eq_completeTable]
  refine evalDist_bind_congr_of_support _ _ _ fun g _ => ?_
  rw [QueryImpl.simulateQ_simulateQ_unbatch, QueryImpl.simulateQ_simulateQ_unbatch,
    ← Oracles.toImpl_ofImpl (QueryImpl.ofFn (completeTable c g))]
  simpa only [bind_pure] using evalDist_simulateQ_genMasked_bind (Oracles.ofImpl _) pure

/-- **Link change of variables.** The pointer-chain puzzle and the puzzle with masked links
have the same delay advantage against every adversary. -/
theorem delayAdvantage_maskedScheme
    (adv : TimeLockPuzzle.Adversary (oracleSpec n S L Salt Ctx) (Puzzle n S L Salt) S) :
    (maskedScheme n m mkCtx initAcc).delayAdvantage adv =
      (scheme n m mkCtx initAcc).delayAdvantage adv := by
  let : Fintype (Point n S L Salt Ctx) := Fintype.ofFinite _
  let : ∀ t, Fintype ((oracleSpec n S L Salt Ctx).Range t) := fun _ => Fintype.ofFinite _
  let := SampleableType.piOfFintype (oracleSpec n S L Salt Ctx).Range
  rw [TimeLockPuzzle.delayAdvantage_eq, TimeLockPuzzle.delayAdvantage_eq,
    ProbCompRuntime.rom_evalDist, ProbCompRuntime.rom_evalDist,
    evalDist_simulateQ_romImpl_run'_eq_completeTable,
    evalDist_simulateQ_romImpl_run'_eq_completeTable]
  congr 1
  refine evalDist_bind_congr_of_support _ _ _ fun g _ => ?_
  simp only [TimeLockPuzzle.delayExperiment, maskedScheme, scheme, simulateQ_bind,
    QueryImpl.simulateQ_simulateQ_unbatch]
  rw [← Oracles.toImpl_ofImpl (QueryImpl.ofFn (completeTable ∅ g))]
  exact evalDist_bind_congr_of_support _ _ _ fun σ _ =>
    evalDist_simulateQ_genMasked_bind (Oracles.ofImpl _) _

end Change

/-! ## Presampled labels

Against the lazy random oracle, each path query of the generator is answered from the cache or by
a fresh uniform answer. Drawing the fresh answers in advance as a labelling `ℓ` turns the path
queries into the deterministic run `presetRun`. -/

section Presample

variable [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]

/-- Answer the path value `v` at the point `t`: from the cache `c` when `t` is cached, and
otherwise with the label `ℓ v`, which is then cached. The labelling `ν` records the answer at
`v`. -/
@[expose]
def presetAt (ℓ : Labels n m S L) (v : PathValue n m) (ν : Labels n m S L)
    (c : (oracleSpec n S L Salt Ctx).QueryCache) (t : Point n S L Salt Ctx)
    (ht : (oracleSpec n S L Salt Ctx).Range t = v.Val S L) :
    Labels n m S L × (oracleSpec n S L Salt Ctx).QueryCache :=
  match c t with
  | some u => (Function.update ν v (cast ht u), c)
  | none => (Function.update ν v (ℓ v), c.cacheQuery t (cast ht.symm (ℓ v)))

lemma presetAt_congr {ℓ : Labels n m S L} {v : PathValue n m} {ν : Labels n m S L}
    {c : (oracleSpec n S L Salt Ctx).QueryCache} {t t' : Point n S L Salt Ctx} (h : t = t')
    (ht : (oracleSpec n S L Salt Ctx).Range t = v.Val S L)
    (ht' : (oracleSpec n S L Salt Ctx).Range t' = v.Val S L) :
    presetAt ℓ v ν c t ht = presetAt ℓ v ν c t' ht' := by
  subst h
  rfl

lemma presetAt_of_none {ℓ : Labels n m S L} {v : PathValue n m} {ν : Labels n m S L}
    {c : (oracleSpec n S L Salt Ctx).QueryCache} {t : Point n S L Salt Ctx}
    {ht : (oracleSpec n S L Salt Ctx).Range t = v.Val S L} (h : c t = none) :
    presetAt ℓ v ν c t ht =
      (Function.update ν v (ℓ v), c.cacheQuery t (cast ht.symm (ℓ v))) := by
  rw [presetAt, h]

lemma presetAt_of_some {ℓ : Labels n m S L} {v : PathValue n m} {ν : Labels n m S L}
    {c : (oracleSpec n S L Salt Ctx).QueryCache} {t : Point n S L Salt Ctx}
    {ht : (oracleSpec n S L Salt Ctx).Range t = v.Val S L} {u : (oracleSpec n S L Salt Ctx).Range t}
    (h : c t = some u) :
    presetAt ℓ v ν c t ht = (Function.update ν v (cast ht u), c) := by
  rw [presetAt, h]

lemma presetAt_update {ℓ : Labels n m S L} {v w : PathValue n m} (hvw : v ≠ w) (a : w.Val S L)
    (ν : Labels n m S L) (c : (oracleSpec n S L Salt Ctx).QueryCache) (t : Point n S L Salt Ctx)
    (ht : (oracleSpec n S L Salt Ctx).Range t = v.Val S L) :
    presetAt (Function.update ℓ w a) v ν c t ht = presetAt ℓ v ν c t ht := by
  simp only [presetAt, Function.update_of_ne hvw]

variable (m : ℕ) (mkCtx : Salt → Ctx) (initAcc : Ctx → S) [NeZero n] [AddCommGroup L]

/-- One step of `queryPath` with the fresh answers presampled as the labelling `ℓ`. -/
@[expose]
def presetStep (P : Puzzle n S L Salt) (ℓ : Labels n m S L) (v : PathValue n m)
    (s : Labels n m S L × (oracleSpec n S L Salt Ctx).QueryCache) :
    Labels n m S L × (oracleSpec n S L Salt Ctx).QueryCache :=
  presetAt ℓ v s.1 s.2 (pathInput m mkCtx initAcc P s.1 v) (range_pathInput m mkCtx initAcc P s.1 v)

/-- `queryPath` with the fresh answers presampled as the labelling `ℓ`. -/
@[expose]
def presetRun (P : Puzzle n S L Salt) (ℓ : Labels n m S L) :
    List (PathValue n m) → Labels n m S L × (oracleSpec n S L Salt Ctx).QueryCache →
      Labels n m S L × (oracleSpec n S L Salt Ctx).QueryCache
  | [], s => s
  | v :: vs, s => presetRun P ℓ vs (presetStep m mkCtx initAcc P ℓ v s)

/-- The presampled run does not read the labels of path values outside its list. -/
lemma presetRun_update {P : Puzzle n S L Salt} {ℓ : Labels n m S L} {w : PathValue n m}
    {vs : List (PathValue n m)} (hw : w ∉ vs) (a : w.Val S L)
    (s : Labels n m S L × (oracleSpec n S L Salt Ctx).QueryCache) :
    presetRun m mkCtx initAcc P (Function.update ℓ w a) vs s =
      presetRun m mkCtx initAcc P ℓ vs s := by
  induction vs generalizing s with
  | nil => rfl
  | cons v vs ih =>
      rw [List.mem_cons, not_or] at hw
      simp only [presetRun, presetStep, presetAt_update (Ne.symm hw.1)]
      exact ih hw.2 _

lemma presetRun_congr {P P' : Puzzle n S L Salt}
    (h : pathInput m mkCtx initAcc P = pathInput m mkCtx initAcc P') (ℓ : Labels n m S L)
    (vs : List (PathValue n m)) (s : Labels n m S L × (oracleSpec n S L Salt Ctx).QueryCache) :
    presetRun m mkCtx initAcc P ℓ vs s = presetRun m mkCtx initAcc P' ℓ vs s := by
  induction vs generalizing s with
  | nil => rfl
  | cons v vs ih =>
      simp only [presetRun, presetStep]
      rw [presetAt_congr (congrFun (congrFun h s.1) v) _
        (range_pathInput m mkCtx initAcc P' s.1 v)]
      exact ih _

/-- Along path values ordered by `rho` whose path inputs under `ℓ` are distinct and uncached, the
presampled run writes `ℓ` and programs the cache with it. -/
lemma presetRun_eq_programCache (P : Puzzle n S L Salt) (ℓ : Labels n m S L)
    {vs : List (PathValue n m)} (hs : vs.Pairwise fun v w => v.rho ≤ w.rho) (hnd : vs.Nodup)
    (hinj : ∀ v ∈ vs, ∀ w ∈ vs, v ≠ w →
      pathInput m mkCtx initAcc P ℓ v ≠ pathInput m mkCtx initAcc P ℓ w)
    {ν : Labels n m S L} (hν : ∀ w ∉ vs, ν w = ℓ w) {c : (oracleSpec n S L Salt Ctx).QueryCache}
    (hc : ∀ v ∈ vs, c (pathInput m mkCtx initAcc P ℓ v) = none) :
    presetRun m mkCtx initAcc P ℓ vs (ν, c) = (ℓ, programCache m mkCtx initAcc P ℓ vs c) := by
  induction vs generalizing ν c with
  | nil => exact Prod.ext (funext fun w => hν w List.not_mem_nil) rfl
  | cons v vs ih =>
      obtain ⟨hv, hnd'⟩ := List.nodup_cons.mp hnd
      have hpath : pathInput m mkCtx initAcc P ν v = pathInput m mkCtx initAcc P ℓ v :=
        pathInput_congr m mkCtx initAcc P v fun w hw =>
          hν w (PathValue.not_mem_of_mem_preds hs hw)
      rw [presetRun, presetStep, presetAt_congr hpath _ (range_pathInput m mkCtx initAcc P ℓ v),
        presetAt_of_none (hc v List.mem_cons_self), programCache]
      refine ih (List.pairwise_cons.mp hs).2 hnd'
        (fun a ha b hb => hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
        (fun w hw => ?_) (fun w hw => ?_)
      · by_cases hwv : w = v
        · subst hwv
          exact Function.update_self _ _ _
        · rw [Function.update_of_ne hwv]
          exact hν w (by simp [hwv, hw])
      · rw [QueryCache.cacheQuery_of_ne _ _ (hinj w (List.mem_cons_of_mem _ hw) v List.mem_cons_self
          fun h => hv (h ▸ hw))]
        exact hc w (List.mem_cons_of_mem _ hw)

/-- Off `Bad`, the presampled run of all path values in order writes `ℓ` and leaves the
programmed cache. -/
lemma presetRun_order_of_not_bad {c : (oracleSpec n S L Salt Ctx).QueryCache}
    {P : Puzzle n S L Salt} {ℓ : Labels n m S L} (hbad : ¬Bad m mkCtx initAcc c P ℓ)
    (ν : Labels n m S L) :
    presetRun m mkCtx initAcc P ℓ (PathValue.order n m) (ν, c) =
      (ℓ, programmedCache m mkCtx initAcc c P ℓ) :=
  presetRun_eq_programCache m mkCtx initAcc P ℓ PathValue.pairwise_order PathValue.nodup_order
    (fun v _ w _ hvw h => hbad (Or.inl ⟨v, w, hvw, h⟩))
    (fun w hw => absurd (PathValue.mem_order w) hw)
    (fun v _ => Option.not_isSome_iff_eq_none.mp fun h => hbad (Or.inr ⟨v, h⟩))

lemma programCache_apply_of_forall_ne (P : Puzzle n S L Salt) (ℓ : Labels n m S L)
    {vs : List (PathValue n m)} {t : Point n S L Salt Ctx}
    (h : ∀ w ∈ vs, pathInput m mkCtx initAcc P ℓ w ≠ t)
    (c : (oracleSpec n S L Salt Ctx).QueryCache) :
    programCache m mkCtx initAcc P ℓ vs c t = c t := by
  induction vs generalizing c with
  | nil => rfl
  | cons w ws ih =>
      rw [programCache, ih (fun u hu => h u (List.mem_cons_of_mem _ hu)),
        QueryCache.cacheQuery_of_ne _ _ (h w List.mem_cons_self).symm]

lemma programCache_pathInput (P : Puzzle n S L Salt) (ℓ : Labels n m S L)
    {vs : List (PathValue n m)} (hnd : vs.Nodup)
    (hinj : ∀ v ∈ vs, ∀ w ∈ vs, v ≠ w →
      pathInput m mkCtx initAcc P ℓ v ≠ pathInput m mkCtx initAcc P ℓ w)
    {v : PathValue n m} (hv : v ∈ vs) (c : (oracleSpec n S L Salt Ctx).QueryCache) :
    programCache m mkCtx initAcc P ℓ vs c (pathInput m mkCtx initAcc P ℓ v) =
      some (cast (range_pathInput m mkCtx initAcc P ℓ v).symm (ℓ v)) := by
  induction vs generalizing c with
  | nil => exact absurd hv List.not_mem_nil
  | cons w ws ih =>
      obtain ⟨hw, hnd'⟩ := List.nodup_cons.mp hnd
      rw [programCache]
      by_cases hvw : v = w
      · subst hvw
        rw [programCache_apply_of_forall_ne m mkCtx initAcc P ℓ (fun u hu =>
          hinj u (List.mem_cons_of_mem _ hu) v List.mem_cons_self fun h => hw (h ▸ hu)),
          QueryCache.cacheQuery_self]
      · exact ih hnd' (fun a ha b hb => hinj a (List.mem_cons_of_mem _ ha) b
          (List.mem_cons_of_mem _ hb)) ((List.mem_cons.mp hv).resolve_left hvw) _

/-- Off `Bad`, the programmed cache answers the path input of every path value with its label. -/
theorem programmedCache_pathInput {c : (oracleSpec n S L Salt Ctx).QueryCache}
    {P : Puzzle n S L Salt} {ℓ : Labels n m S L} (hbad : ¬Bad m mkCtx initAcc c P ℓ)
    (v : PathValue n m) :
    programmedCache m mkCtx initAcc c P ℓ (pathInput m mkCtx initAcc P ℓ v) =
      some (cast (range_pathInput m mkCtx initAcc P ℓ v).symm (ℓ v)) :=
  programCache_pathInput m mkCtx initAcc P ℓ PathValue.nodup_order
    (fun v _ w _ hvw h => hbad (Or.inl ⟨v, w, hvw, h⟩)) (PathValue.mem_order v) c

/-- The lazy random oracle answering the points of every round. -/
local notation "H" => unifFwdImpl (oracleSpec n S L Salt Ctx) +
  QueryImpl.batch (OracleSpec.randomOracle (spec := oracleSpec n S L Salt Ctx))

/-- Against the lazy random oracle from the cache `c`, the path queries of the distinct path
values `vs` are the presampled run on a uniform labelling. -/
theorem evalDist_run_queryPath_bind [SampleableType S] [SampleableType L] {β : Type}
    [MeasurableSpace β] (P : Puzzle n S L Salt) {vs : List (PathValue n m)} (hvs : vs.Nodup)
    (ν : Labels n m S L) (c : (oracleSpec n S L Salt Ctx).QueryCache)
    (k : Labels n m S L × (oracleSpec n S L Salt Ctx).QueryCache → ProbComp β) :
    𝒟[(simulateQ H (queryPath m mkCtx initAcc P vs ν)).run c >>= k] =
      𝒟[$ᵗ (Labels n m S L) >>= fun ℓ => k (presetRun m mkCtx initAcc P ℓ vs (ν, c))] := by
  let : ∀ v : PathValue n m, MeasurableSpace (v.Val S L) := fun _ => ⊤
  induction vs generalizing ν c with
  | nil =>
      simp only [queryPath, presetRun, simulateQ_pure, StateT.run_pure, pure_bind]
      rw [OracleComp.evalDist_bind_const]
  | cons v vs ih =>
      obtain ⟨hv, hvs'⟩ := List.nodup_cons.mp hvs
      have hr := range_pathInput m mkCtx initAcc P ν v
      rw [queryPath, simulateQ_bind, StateT.run_bind, simulateQ_add_batch_queryPoint, bind_assoc]
      rcases hc : c (pathInput m mkCtx initAcc P ν v) with _ | u
      · rw [QueryImpl.withCaching_run_none _ hc, bind_map_left]
        have hupd : ∀ (u : (oracleSpec n S L Salt Ctx).Range (pathInput m mkCtx initAcc P ν v))
            (ℓ : Labels n m S L),
            k (presetRun m mkCtx initAcc P ℓ vs (Function.update ν v (cast hr u),
              c.cacheQuery (pathInput m mkCtx initAcc P ν v) u)) =
            k (presetRun m mkCtx initAcc P (Function.update ℓ v (cast hr u)) (v :: vs) (ν, c)) := by
          intro u ℓ
          simp only [presetRun, presetStep, presetAt_of_none hc, Function.update_self, cast_cast,
            cast_eq]
          rw [presetRun_update m mkCtx initAcc hv]
        calc _ = 𝒟[$ᵗ ((oracleSpec n S L Salt Ctx).Range (pathInput m mkCtx initAcc P ν v)) >>=
                fun u => $ᵗ (Labels n m S L) >>= fun ℓ =>
                  k (presetRun m mkCtx initAcc P (Function.update ℓ v (cast hr u)) (v :: vs)
                    (ν, c))] :=
              evalDist_bind_congr_of_support _ _ _ fun u _ =>
                (ih hvs' (Function.update ν v (cast hr u))
                  (c.cacheQuery (pathInput m mkCtx initAcc P ν v) u)).trans (by simp_rw [hupd])
          _ = 𝒟[(cast hr <$>
                ($ᵗ ((oracleSpec n S L Salt Ctx).Range (pathInput m mkCtx initAcc P ν v)))) >>=
                fun w => $ᵗ (Labels n m S L) >>= fun ℓ =>
                  k (presetRun m mkCtx initAcc P (Function.update ℓ v w) (v :: vs) (ν, c))] := by
              rw [bind_map_left]
          _ = _ := evalDist_bind_bind_update_dependent v _ _ (evalDist_cast_uniformSample hr)
              SampleableType.evalDist_uniformSample
              fun ℓ => k (presetRun m mkCtx initAcc P ℓ (v :: vs) (ν, c))
      · rw [QueryImpl.withCaching_run_some _ hc, pure_bind, ih hvs']
        simp only [presetRun, presetStep, presetAt_of_some hc]

end Presample

/-! ## The programmed experiment

The delay experiment of `maskedScheme`, with the generator's fresh answers presampled, is a draw of
a `Seed` followed by the online phase. The programmed experiment draws the same seed, programs the
cache with the labels and runs the online phase from the programmed cache; the two agree off
`Bad`. -/

/-- The random choices of the delay experiment before the online phase: the preprocessing state
and cache, the salt, the first link, the masked links and the labelling. -/
structure Seed (n m : ℕ) (S L Salt Ctx State : Type) where
  /-- The state the preprocessing phase hands to the online phase. -/
  state : State
  /-- The cache left by the preprocessing phase. -/
  cache : (oracleSpec n S L Salt Ctx).QueryCache
  /-- The salt. -/
  salt : Salt
  /-- The first link. -/
  firstLink : L
  /-- The masked links. -/
  maskedLinks : Fin (n - 1) → L
  /-- The labelling of the path values. -/
  labels : Labels n m S L

/-- The puzzle of a seed, committing to its key label. -/
@[expose]
def Seed.puzzle {State : Type} (s : Seed n m S L Salt Ctx State) : Puzzle n S L Salt :=
  labelPuzzle s.salt s.firstLink s.maskedLinks s.labels

section Programmed

variable [DecidableEq S] [DecidableEq L] [DecidableEq Salt] [DecidableEq Ctx]
  [SampleableType S] [SampleableType L]
  (adv : TimeLockPuzzle.Adversary (oracleSpec n S L Salt Ctx) (Puzzle n S L Salt) S)

/-- Run the preprocessing phase of `adv` lazily from the empty cache, then draw the salt, the
first link, the masked links and the labelling uniformly. -/
@[expose]
def seed (m : ℕ) [SampleableType Salt] : ProbComp (Seed n m S L Salt Ctx adv.State) := do
  let s ← (simulateQ (oracleSpec n S L Salt Ctx).romImpl adv.preprocess).run ∅
  let salt ← $ᵗ Salt
  let p ← $ᵗ (L × (Fin (n - 1) → L))
  let ℓ ← $ᵗ (Labels n m S L)
  return ⟨s.1, s.2, salt, p.1, p.2, ℓ⟩

/-- Run the online phase of `adv` on the state `σ` and the puzzle `P` in the random oracle model
from the cache `c`, and report whether it returns `key`. -/
@[expose]
def onlineWin (σ : adv.State) (P : Puzzle n S L Salt) (key : S)
    (c : (oracleSpec n S L Salt Ctx).QueryCache) : ProbComp Bool :=
  (simulateQ (oracleSpec n S L Salt Ctx).romImpl (do
    let key' ← simulateQ (oracleSpec n S L Salt Ctx).unbatch (adv.online σ P)
    return decide (key' = key))).run' c

variable (m : ℕ) (mkCtx : Salt → Ctx) (initAcc : Ctx → S) [NeZero n] [AddCommGroup L]

/-- The delay experiment of `maskedScheme` after the seed: the generator's path values are the
presampled run on the labels, and the online phase runs from the cache it reaches. -/
@[expose]
def realRest (s : Seed n m S L Salt Ctx adv.State) : ProbComp Bool :=
  let ν₀ : Labels n m S L := Labels.const (initAcc (mkCtx s.salt)) s.firstLink
  let r := presetRun m mkCtx initAcc (labelPuzzle s.salt s.firstLink s.maskedLinks ν₀) s.labels
    (PathValue.order n m) (ν₀, s.cache)
  onlineWin adv s.state (labelPuzzle s.salt s.firstLink s.maskedLinks r.1) (r.1 .key) r.2

/-- The programmed experiment after the seed: the online phase runs from the programmed cache and
the result reports whether it returns the key label, and whether `Bad` holds. -/
@[expose]
def programmedRest (s : Seed n m S L Salt Ctx adv.State) : ProbComp (Bool × Bool) :=
  (·, decide (Bad m mkCtx initAcc s.cache s.puzzle s.labels)) <$>
    onlineWin adv s.state s.puzzle (s.labels .key)
      (programmedCache m mkCtx initAcc s.cache s.puzzle s.labels)

/-- The programmed experiment: the generator draws independent labels for the path values and
programs the cache with them. It returns whether the adversary wins and whether `Bad` holds. -/
@[expose]
def programmedExperiment [SampleableType Salt] : ProbComp (Bool × Bool) :=
  seed adv m >>= programmedRest adv m mkCtx initAcc

/-- Off `Bad`, the delay experiment and the programmed experiment agree after the seed. -/
lemma realRest_eq_of_not_bad (s : Seed n m S L Salt Ctx adv.State)
    (h : ¬Bad m mkCtx initAcc s.cache s.puzzle s.labels) :
    realRest adv m mkCtx initAcc s = Prod.fst <$> programmedRest adv m mkCtx initAcc s := by
  simp only [realRest, programmedRest]
  rw [presetRun_congr m mkCtx initAcc
    (pathInput_labelPuzzle m mkCtx initAcc s.salt s.firstLink s.maskedLinks _ s.labels),
    presetRun_order_of_not_bad m mkCtx initAcc
      (P := labelPuzzle s.salt s.firstLink s.maskedLinks s.labels) h, Functor.map_map]
  exact (id_map _).symm

variable [SampleableType Salt]

/-- The delay experiment of `maskedScheme` is the seed followed by `realRest`. -/
theorem evalDist_delayExperiment_maskedScheme :
    𝒟[(simulateQ (oracleSpec n S L Salt Ctx).romImpl
        ((maskedScheme n m mkCtx initAcc).delayExperiment adv)).run' ∅] =
      𝒟[seed adv m >>= realRest adv m mkCtx initAcc] := by
  simp only [TimeLockPuzzle.delayExperiment, maskedScheme, seed, bind_assoc, pure_bind]
  rw [run'_simulateQ_bind]
  refine evalDist_bind_congr_of_support _ _ _ fun s _ => ?_
  rw [run'_simulateQ_bind, OracleSpec.simulateQ_romImpl_simulateQ_unbatch, genMasked,
    run_simulateQ_bind, run_simulateQ_unifFwdImpl_add_liftM, bind_assoc, bind_map_left]
  refine evalDist_bind_congr_of_support _ _ _ fun salt _ => ?_
  rw [run_simulateQ_bind, run_simulateQ_unifFwdImpl_add_liftM, bind_assoc, bind_map_left]
  refine evalDist_bind_congr_of_support _ _ _ fun p _ => ?_
  simp only [genMaskedWith]
  rw [run_simulateQ_bind, bind_assoc]
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  exact evalDist_run_queryPath_bind m mkCtx initAcc _ PathValue.nodup_order _ _ _

/-- The delay advantage of `maskedScheme` is the probability that `realRest` wins after the
seed. -/
lemma delayAdvantage_maskedScheme_eq :
    (maskedScheme n m mkCtx initAcc).delayAdvantage adv =
      Pr{let b ← seed adv m >>= realRest adv m mkCtx initAcc}[b = true] := by
  rw [TimeLockPuzzle.delayAdvantage_eq, ProbCompRuntime.rom_evalDist,
    evalDist_delayExperiment_maskedScheme, prEvent_eq_evalDist_singleton]

/-- Winning in the programmed experiment is winning in `programmedRest` after the seed. -/
lemma prEvent_programmedExperiment_win :
    Pr{let r ← programmedExperiment adv m mkCtx initAcc}[r.1 = true] =
      Pr{let b ← seed adv m >>= fun s =>
        Prod.fst <$> programmedRest adv m mkCtx initAcc s}[b = true] := by
  rw [← map_bind, Functor.map_map]
  rfl

/-- `Bad` in the programmed experiment is `Bad` on the seed. -/
lemma prEvent_programmedExperiment_bad :
    Pr{let r ← programmedExperiment adv m mkCtx initAcc}[r.2 = true] =
      Pr{let s ← seed adv m}[Bad m mkCtx initAcc s.cache s.puzzle s.labels] := by
  rw [programmedExperiment, map_bind, map_eq_bind_pure_comp]
  refine prEvent_bind_congr_of_support _ _ _ fun s _ => ?_
  simp only [programmedRest, Functor.map_map, Function.comp_def, prEvent_def,
    OracleComp.evalDist_map_const, evalDist_pure, decide_eq_true_eq]

/-- **Programming theorem**, one side: the delay advantage of `maskedScheme` is at most the
winning probability in the programmed experiment plus the probability of `Bad` there. -/
theorem delayAdvantage_maskedScheme_le :
    (maskedScheme n m mkCtx initAcc).delayAdvantage adv ≤
      Pr{let r ← programmedExperiment adv m mkCtx initAcc}[r.1 = true] +
        Pr{let r ← programmedExperiment adv m mkCtx initAcc}[r.2 = true] := by
  rw [delayAdvantage_maskedScheme_eq, prEvent_programmedExperiment_win,
    prEvent_programmedExperiment_bad]
  have := prEvent_bind_le_add_of_disagree (mx := seed adv m)
    (my := realRest adv m mkCtx initAcc)
    (oc := fun s => Prod.fst <$> programmedRest adv m mkCtx initAcc s) (q := fun b => b = true)
    (D := fun s => Bad m mkCtx initAcc s.cache s.puzzle s.labels) (ε₂ := 0) le_rfl
    fun s _ hs => by rw [realRest_eq_of_not_bad adv m mkCtx initAcc s hs, add_zero]
  rwa [add_zero] at this

/-- **Programming theorem**, the other side: the winning probability in the programmed experiment
is at most the delay advantage of `maskedScheme` plus the probability of `Bad`. -/
theorem programmedExperiment_win_le :
    Pr{let r ← programmedExperiment adv m mkCtx initAcc}[r.1 = true] ≤
      (maskedScheme n m mkCtx initAcc).delayAdvantage adv +
        Pr{let r ← programmedExperiment adv m mkCtx initAcc}[r.2 = true] := by
  rw [delayAdvantage_maskedScheme_eq, prEvent_programmedExperiment_win,
    prEvent_programmedExperiment_bad]
  have := prEvent_bind_le_add_of_disagree (mx := seed adv m)
    (my := fun s => Prod.fst <$> programmedRest adv m mkCtx initAcc s)
    (oc := realRest adv m mkCtx initAcc) (q := fun b => b = true)
    (D := fun s => Bad m mkCtx initAcc s.cache s.puzzle s.labels) (ε₂ := 0) le_rfl
    fun s _ hs => by rw [← realRest_eq_of_not_bad adv m mkCtx initAcc s hs, add_zero]
  rwa [add_zero] at this

/-- **Programming theorem**: the delay advantage of `maskedScheme` and the winning probability in
the programmed experiment differ by at most the probability of `Bad` in the programmed
experiment. -/
theorem abs_delayAdvantage_maskedScheme_sub_le :
    |((maskedScheme n m mkCtx initAcc).delayAdvantage adv).toReal -
        (Pr{let r ← programmedExperiment adv m mkCtx initAcc}[r.1 = true]).toReal| ≤
      (Pr{let r ← programmedExperiment adv m mkCtx initAcc}[r.2 = true]).toReal := by
  have ha : (maskedScheme n m mkCtx initAcc).delayAdvantage adv ≠ ⊤ := by
    rw [delayAdvantage_maskedScheme_eq]
    exact prEvent_ne_top _
  have h₁ := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨prEvent_ne_top _, prEvent_ne_top _⟩)
    (delayAdvantage_maskedScheme_le adv m mkCtx initAcc)
  have h₂ := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ha, prEvent_ne_top _⟩)
    (programmedExperiment_win_le adv m mkCtx initAcc)
  rw [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)] at h₁
  rw [ENNReal.toReal_add ha (prEvent_ne_top _)] at h₂
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

/-- The programming theorem for the pointer-chain puzzle itself, through the link change of
variables. -/
theorem abs_delayAdvantage_scheme_sub_le [Finite Ctx] :
    |((scheme n m mkCtx initAcc).delayAdvantage adv).toReal -
        (Pr{let r ← programmedExperiment adv m mkCtx initAcc}[r.1 = true]).toReal| ≤
      (Pr{let r ← programmedExperiment adv m mkCtx initAcc}[r.2 = true]).toReal := by
  rw [← delayAdvantage_maskedScheme m mkCtx initAcc adv]
  exact abs_delayAdvantage_maskedScheme_sub_le adv m mkCtx initAcc

end Programmed

end PointerChainPuzzle
