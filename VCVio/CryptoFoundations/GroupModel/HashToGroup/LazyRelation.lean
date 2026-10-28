/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.GroupModel.HashToGroup.LazyExecution
public import VCVio.CryptoFoundations.GroupModel.HashToGroup.Relation

/-! # Normalized collisions for bounded lazy hash-to-group interactions

Arbitrary hash labels are assigned distinct challenge slots on first use. A hash-query budget
bounds the required table; private coins are unrestricted. Fixed inputs occupy independently
sampled challenge coordinates. The relation reduction returns the transported merged difference.
-/

public section

namespace GroupModel.HashToGroup

open OracleComp OracleSpec Interaction
open scoped ENNReal

variable {Label F G : Type} {n q : ℕ}

/-- Execute a certified interaction with fixed inputs, an honest lazy hash oracle, and private
coins. The output retains every chronological label/reply pair, including repeated queries. -/
@[expose] def lazyExecution [DecidableEq Label] [SampleableType G]
    [CommSemiring F] [AddCommMonoid G] [Module F G] (fixed : Fin n → G)
    (A : Adversary F (fun _ : Unit => G) Unit (CoinQuery Label)
      (CoinReply (fun _ => Unit)) Unit) :
    ProbComp (Explained F Unit (fun _ : Unit => G) × List (Label × G)) :=
  (fun z => (z.1, z.2.2)) <$> (simulateQ SlotRenaming.honest
    (rawProgram (A.main ⟨(), fun _ => List.ofFn fixed⟩))).run (∅, [])

/-- The honest normalized-collision trial samples the fixed inputs independently and then runs
the adversary with a lazy hash oracle on its arbitrary label type. -/
@[expose] noncomputable def lazyTrial [DecidableEq Label] [SampleableType G]
    [CommSemiring F] [AddCommMonoid G] [Module F G] (n : ℕ)
    (A : Adversary F (fun _ : Unit => G) Unit (CoinQuery Label)
      (CoinReply (fun _ => Unit)) Unit) :
    ProbComp (Explained F Unit (fun _ : Unit => G) × List (Label × G)) := do
  let fixed ← $ᵗ (Fin n → G)
  lazyExecution fixed A

/-- Execute the same adversary against a fixed reduction basis, using the right-hand
coordinates as first-use hash slots and the left-hand coordinates as fixed inputs. -/
@[expose] def slotExecution [DecidableEq Label] [SampleableType G]
    [CommSemiring F] [AddCommMonoid G] [Module F G] (B : Origin n (Fin q) → G)
    (A : Adversary F (fun _ : Unit => G) Unit (CoinQuery Label)
      (CoinReply (fun _ => Unit)) Unit) :
    ProbComp (Explained F Unit (fun _ : Unit => G) × SlotRenaming.State Label G q) :=
  SlotRenaming.tableRun
    (rawProgram (A.main ⟨(), fun _ => List.ofFn (fun i => B (.inl i))⟩))
    (fun i => B (.inr i))

/-- A syntactic budget on hash calls for every possible fixed input. Private coin requests
have a left-summand index in the raw interface and therefore do not contribute to `q`. -/
@[expose] def HashQueryBound [CommSemiring F] [AddCommMonoid G] [Module F G]
    (n q : ℕ) (A : Adversary F (fun _ : Unit => G) Unit (CoinQuery Label)
      (CoinReply (fun _ => Unit)) Unit) : Prop :=
  ∀ fixed : Fin n → G,
    IsQueryBoundP (rawProgram (A.main ⟨(), fun _ => List.ofFn fixed⟩)) (fun t => t.isRight) q

/-- The named lazy-oracle relation finder runs first-use slot routing and returns the
substituted difference of the two output representations over the finite challenge basis. -/
@[expose] def lazyRelationReduction [DecidableEq Label] [SampleableType G]
    [CommRing F] [AddCommGroup G] [Module F G]
    (A : Adversary F (fun _ : Unit => G) Unit (CoinQuery Label)
      (CoinReply (fun _ => Unit)) Unit) :
    DiscreteLogRelation.Adversary F G (Origin n (Fin q)) unifSpec := fun B =>
  (fun z => slotDifference z.2.slotOf (receiptOrigins n z.2.log) z.1) <$> slotExecution B A

private theorem slotExecution_rows [DecidableEq Label] [SampleableType G]
    [CommSemiring F] [AddCommMonoid G] [Module F G] (B : Origin n (Fin q) → G)
    (A : Adversary F (fun _ : Unit => G) Unit (CoinQuery Label)
      (CoinReply (fun _ => Unit)) Unit) (hb : HashQueryBound n q A) (z)
    (hz : z ∈ support (slotExecution B A)) :
    ((receiptOrigins n z.2.log).map (slotRow (F := F) z.2.slotOf)).map (basisMap B) =
      List.ofFn (fun i => B (.inl i)) ++ z.2.log.map Prod.snd := by
  have hn := SlotRenaming.tableRun_no_overflow _ _ (hb (fun i => B (.inl i))) z hz
  have hr := SlotRenaming.tableRun_receipts _ _ z hz
  simp only [receiptOrigins, List.map_append, List.map_ofFn, List.map_map]
  congr 1
  · congr 1
    funext i
    exact basisMap_single B (.inl i)
  · apply List.map_congr_left
    intro p hp
    obtain ⟨i, hi⟩ := hn.2 p.1 (List.mem_map_of_mem hp)
    have hv := hr p hp
    change (SlotRenaming.cache z.2 (QueryCache.ofFn fun i => some (B (.inr i)))) p.1 =
      some p.2 at hv
    simp only [SlotRenaming.cache, QueryCache.ofFn_apply, hi, Option.some.injEq] at hv
    simp only [Function.comp_apply, slotRow, hi, basisMap_single, hv]

private theorem slotExecution_nonzero [DecidableEq Label] [SampleableType G]
    [CommRing F] [AddCommGroup G] [Module F G] (B : Origin n (Fin q) → G)
    (A : Adversary F (fun _ : Unit => G) Unit (CoinQuery Label)
      (CoinReply (fun _ => Unit)) Unit) (hb : HashQueryBound n q A) (z)
    (hz : z ∈ support (slotExecution B A))
    (hc : NormalizedCollision (receiptOrigins n z.2.log) z.1) :
    slotDifference z.2.slotOf (receiptOrigins n z.2.log) z.1 ≠ 0 := by
  have hv := SlotRenaming.tableRun_assigned _ _ z hz
  have hn := SlotRenaming.tableRun_no_overflow _ _ (hb (fun i => B (.inl i))) z hz
  apply slotDifference_ne_zero z.2.slotOf hv.injective _ ?_ z.1 hc
  intro l hl
  have hm : l ∈ z.2.log.map Prod.fst := by
    simpa [receiptOrigins, List.mem_map] using hl
  obtain ⟨i, hi⟩ := hn.2 l hm
  simp [hi]

/-- A normalized collision in a bounded slot execution yields a nontrivial relation over the
`n + q` challenge coordinates. No receipt-level cancellation term is needed. -/
theorem slotExecution_relation [DecidableEq Label] [SampleableType G]
    [CommRing F] [AddCommGroup G] [Module F G] (B : Origin n (Fin q) → G)
    (A : Adversary F (fun _ : Unit => G) Unit (CoinQuery Label)
      (CoinReply (fun _ => Unit)) Unit) (hb : HashQueryBound n q A) (z)
    (hz : z ∈ support (slotExecution B A))
    (hc : NormalizedCollision (receiptOrigins n z.2.log) z.1) :
    slotDifference z.2.slotOf (receiptOrigins n z.2.log) z.1 ≠ 0 ∧
      basisMap B (slotDifference z.2.slotOf (receiptOrigins n z.2.log) z.1) = 0 := by
  refine ⟨slotExecution_nonzero B A hb z hz hc, ?_⟩
  have hv := tableRun_rawProgram_valid (List.ofFn fun i => B (.inl i))
    (fun i => B (.inr i)) _ (A.algebraic _) z hz
  obtain ⟨a, b, g, ha, hg, _⟩ := hc
  have hv' := hv ()
  simp only [ha, hg, List.forall₂_cons, List.forall₂_nil_right_iff, and_true] at hv'
  simp [slotDifference, ha, map_sub, basisMap_transport, slotExecution_rows B A hb z hz,
    hv'.1.2, hv'.2.2]

private theorem split_sample_bijective [SMul F G] (g : G)
    (hg : Function.Bijective (· • g : F → G)) :
    Function.Bijective (fun x : Origin n (Fin q) → F =>
      ((fun i => x (.inl i) • g), (fun i => x (.inr i) • g))) := by
  constructor
  · intro x y h
    funext i
    apply hg.injective
    cases i with
    | inl i => exact congrFun (congrArg Prod.fst h) i
    | inr i => exact congrFun (congrArg Prod.snd h) i
  · rintro ⟨a, b⟩
    choose x hx using fun i : Origin n (Fin q) => hg.surjective (Sum.elim a b i)
    refine ⟨x, Prod.ext (funext fun i => hx (.inl i)) (funext fun i => hx (.inr i))⟩

/-- The honest lazy trial equals execution with independent challenge coordinates for fixed
inputs and first-use hash slots. This is a joint law of output and label/reply provenance. -/
theorem lazyTrial_eq_slotTrial [DecidableEq Label] [SampleableType F] [SampleableType G]
    [CommSemiring F] [AddCommMonoid G] [Module F G]
    (n q : ℕ) (g : G) (hg : Function.Bijective (· • g : F → G))
    (A : Adversary F (fun _ : Unit => G) Unit (CoinQuery Label)
      (CoinReply (fun _ => Unit)) Unit) :
    lazyTrial n A =ᵈ (do
      let x ← $ᵗ (Origin n (Fin q) → F)
      (fun z : Explained F Unit (fun _ : Unit => G) × SlotRenaming.State Label G q =>
        (z.1, z.2.log)) <$> slotExecution (fun i => x i • g) A) := by
  let f : (Fin n → G) × (Fin q → G) →
      ProbComp (Explained F Unit (fun _ : Unit => G) × List (Label × G)) := fun pair =>
    (fun z => (z.1, z.2.log)) <$> SlotRenaming.tableRun
      (rawProgram (A.main ⟨(), fun _ => List.ofFn pair.1⟩)) pair.2
  have hs := (SampleableType.map_uniformSample_evalDistEq_of_bijective
    (split_sample_bijective (n := n) (q := q) g hg)).bind_left f
  have hl := EvalDistEq.bind_right ($ᵗ (Fin n → G)) (fun fixed =>
    SlotRenaming.simulateQ_honest_eq_uniform_table (q := q)
      (rawProgram (A.main ⟨(), fun _ => List.ofFn fixed⟩)))
  apply hl.trans
  simpa only [SampleableType.uniformSample_prod_eq_bind, bind_assoc, pure_bind,
    bind_map_left, f, slotExecution] using hs.symm

/-- Normalized collisions against the honest lazy oracle reduce to the shared relation
experiment over exactly `n` fixed-input coordinates and `q` first-use hash slots. The explicit
budget counts every hash query and excludes private coins. -/
theorem lazyTrial_le_relation [DecidableEq Label] [SampleableType F] [SampleableType G]
    [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (n q : ℕ) (g : G) (hg : Function.Bijective (· • g : F → G))
    (A : Adversary F (fun _ : Unit => G) Unit (CoinQuery Label)
      (CoinReply (fun _ => Unit)) Unit) (hb : HashQueryBound n q A) :
    Pr{let z ← lazyTrial n A}[NormalizedCollision (receiptOrigins n z.2) z.1] ≤
      Pr{let b ← (DiscreteLogRelation.plainExperiment g
        (lazyRelationReduction (n := n) (q := q) A))}[b = true] := by
  rw [(lazyTrial_eq_slotTrial n q g hg A).prEvent_eq]
  let trial := do
    let x ← $ᵗ (Origin n (Fin q) → F)
    let z ← slotExecution (fun i => x i • g) A
    pure (x, z)
  have he : Pr{let w ← trial}[
        slotDifference w.2.2.slotOf (receiptOrigins n w.2.2.log) w.2.1 ≠ 0 ∧
        basisMap (fun i => w.1 i • g)
          (slotDifference w.2.2.slotOf (receiptOrigins n w.2.2.log) w.2.1) = 0] =
      Pr{let b ← (DiscreteLogRelation.plainExperiment g
        (lazyRelationReduction (n := n) (q := q) A))}[b = true] := by
    simp only [DiscreteLogRelation.plainExperiment, DiscreteLogRelation.experiment,
      DiscreteLogRelation.plainAdversary, StateT.run'_eq, DiscreteLogRelation.map_run_plainImpl]
    let : MeasurableSpace (Origin n (Fin q) → F) := ⊤
    simp [trial, lazyRelationReduction, basisMap, prEvent_norm,
      prEvent_bind_bind_eq_lintegral_of_discrete, SampleableType.evalDist_uniformSample]
  rw [← he]
  have hwin : Pr{let z ← (do
      let x ← $ᵗ (Origin n (Fin q) → F)
      (fun z : Explained F Unit (fun _ : Unit => G) × SlotRenaming.State Label G q =>
        (z.1, z.2.log)) <$> slotExecution (fun i => x i • g) A)}[
          NormalizedCollision (receiptOrigins n z.2) z.1] =
      Pr{let w ← trial}[NormalizedCollision (receiptOrigins n w.2.2.log) w.2.1] := by
    simp [trial, prEvent_norm]
  rw [hwin]
  apply prEvent_mono_of_support
  intro w hw hc
  simp only [trial, mem_support_bind_iff] at hw
  obtain ⟨x, _, z, hz, hw⟩ := hw
  simp only [support_pure, Set.mem_singleton_iff] at hw
  subst w
  exact slotExecution_relation _ A hb z hz hc

/-- Honest lazy normalized collisions have a single hidden-mask loss `1 / |F|` against the
named DLog reduction. Its relation stage uses independently programmed coordinates for every
fixed input and fresh hash slot; adaptivity and private coins are covered by the joint
simulation and the relation theorem's conditional-independence argument. -/
theorem lazyTrial_le_dlog [DecidableEq Label] [SampleableType F] [SampleableType G]
    [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G]
    (n q : ℕ) (g : G) (hg : Function.Bijective (· • g : F → G))
    (A : Adversary F (fun _ : Unit => G) Unit (CoinQuery Label)
      (CoinReply (fun _ => Unit)) Unit) (hb : HashQueryBound n q A) :
    Pr{let z ← lazyTrial n A}[NormalizedCollision (receiptOrigins n z.2) z.1] ≤
      Pr{let b ← (DiffieHellman.dlogExperiment g
        (DiscreteLogRelation.plainReduction
          (lazyRelationReduction (n := n) (q := q) A)))}[b = true] + 1 / Fintype.card F := by
  classical
  exact (lazyTrial_le_relation n q g hg A hb).trans
    (DiscreteLogRelation.experiment_le _ () g hg _)

end GroupModel.HashToGroup
