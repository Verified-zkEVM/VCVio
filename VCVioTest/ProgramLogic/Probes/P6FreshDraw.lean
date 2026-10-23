module

public import VCVio
public meta import VCVio.ProgramLogic.Tactics
public import Mathlib.Util.CountHeartbeats

-- A probe: its proofs are measurements, not library code, so Mathlib's style set is off.
set_option linter.mathlibStandardSet false

/-!
# Probe P6: a single fresh draw

`Pr{let a ← prefix; let x ← $ᵗ F}[P a x] ≤ d / |F|` when every `P a` accepts at most `d` points.
-/

public section

open ENNReal Std.WP OrderDual OracleSpec OracleComp

namespace VCVioTest.ProgramLogic.Probes.P6FreshDraw

set_option experimental.vcgen true

/-! ## The upper reading (minimal port of 49f365a74's `Upper.lean`) -/

namespace Upper

variable {ι : Type} {spec : OracleSpec ι} [OracleSpec.AnswerMeasure spec] {α : Type}

open scoped OracleComp.Lower in
noncomputable scoped instance (priority := 1300) instWP :
    Std.WP.WPMonad (OracleComp spec) ℝ≥0∞ᵒᵈ EStack⟨⟩ᵒᵈ :=
  ExactWPMonad.dual

open scoped VCVioTest.ProgramLogic.Probes.P6FreshDraw.Upper

theorem triple_iff (oa : OracleComp spec α) (pre : ℝ≥0∞ᵒᵈ) (post : α → ℝ≥0∞ᵒᵈ)
    (epost : EStack⟨⟩ᵒᵈ) :
    Triple oa pre post epost ↔
      OracleComp.ProgramLogic.wp oa (fun a => ofDual (post a)) ≤ ofDual pre :=
  Triple.iff

/-- An upper bound on an event is a triple with the event's indicator as postcondition. -/
theorem prEvent_le_iff_triple (mx : OracleComp spec Prop) (ε : ℝ≥0∞) :
    prEvent mx ≤ ε ↔ ⦃ toDual ε ⦄ mx ⦃ fun P => toDual (OracleComp.ProgramLogic.propInd P) ⦄ := by
  rw [OracleComp.ProgramLogic.prEvent_eq_wp]
  exact (triple_iff mx _ _ _).symm

theorem rel_iff (a b : ℝ≥0∞ᵒᵈ) : Lean.Order.PartialOrder.rel a b ↔ ofDual b ≤ ofDual a :=
  Iff.rfl

theorem iInf_eq {κ : Type _} (f : κ → ℝ≥0∞ᵒᵈ) :
    Lean.Order.iInf f = toDual (⨆ i, ofDual (f i)) :=
  Lean.Order.PartialOrder.rel_antisymm
    (show (⨆ i, ofDual (f i)) ≤ ofDual (Lean.Order.iInf f) from
      iSup_le fun i => Lean.Order.iInf_le f i)
    (Lean.Order.le_iInf f _ fun i => le_iSup (fun i => ofDual (f i)) i)

/-- An opaque prefix, bounded by its largest value on its support. -/
theorem Spec.ofSupport (oa : OracleComp spec α) (post : α → ℝ≥0∞ᵒᵈ) {epost : EStack⟨⟩ᵒᵈ} :
    Triple oa (Lean.Order.iInf fun a : {a // a ∈ support oa} => post a.1) post epost := by
  rw [triple_iff, iInf_eq, ofDual_toDual]
  exact OracleComp.ProgramLogic.wp_le_const_of_support oa fun x hx =>
    le_iSup (fun a : {a // a ∈ support oa} => ofDual (post a.1)) ⟨x, hx⟩

/-- The exact rule of a finite uniform draw. -/
theorem Spec.uniformSample_avg (β : Type) [SampleableType β] [Fintype β] (post : β → ℝ≥0∞ᵒᵈ)
    {epost : EStack⟨⟩ᵒᵈ} :
    Triple ($ᵗ β) (toDual ((∑ x, ofDual (post x)) / Fintype.card β)) post epost := by
  rw [triple_iff, ofDual_toDual, OracleComp.Lower.wp_uniformSample_eq_tsum, tsum_fintype,
    Nat.card_eq_fintype_card]

end Upper

open scoped VCVioTest.ProgramLogic.Probes.P6FreshDraw.Upper

variable {α F : Type} [SampleableType F] [Fintype F]

#count_heartbeats in
/-- Baseline: the measure-level bind rule and the finite uniform law. -/
theorem fresh_old (pre : ProbComp α) (P : α → F → Prop) [∀ a, DecidablePred (P a)] (d : ℕ)
    (h : ∀ a, (Finset.univ.filter (P a)).card ≤ d) :
    Pr{let a ← pre; let x ← $ᵗ F}[P a x] ≤ d / Fintype.card F := by
  have := prEvent_bind_le_of_forall_le pre (fun a => $ᵗ F >>= fun x => pure (P a x)) id
    (ε := d / Fintype.card F) fun a => by
      simpa using ENNReal.div_le_div_right (by exact_mod_cast h a) _
  simpa using this

#count_heartbeats in
/-- Through the upper reading: the prefix by its support, the draw by its average. -/
theorem fresh_new (pre : ProbComp α) (P : α → F → Prop) [∀ a, DecidablePred (P a)] (d : ℕ)
    (h : ∀ a, (Finset.univ.filter (P a)).card ≤ d) :
    Pr{let a ← pre; let x ← $ᵗ F}[P a x] ≤ d / Fintype.card F := by
  rw [Upper.prEvent_le_iff_triple]
  vcgen [Upper.Spec.ofSupport pre, Upper.Spec.uniformSample_avg]
  simp only [Upper.rel_iff, ofDual_toDual, OracleComp.ProgramLogic.propInd_eq_ite, Finset.sum_boole]
  gcongr
  exact_mod_cast h _

/-! ## Two fresh draws (findings, not proofs)

For `Pr{let a ← pre; let x ← $ᵗ F; let y ← $ᵗ F}[P a x ∨ R a x y] ≤ (d + e) / |F|`:

* `vcgen [Upper.Spec.ofSupport pre, Upper.Spec.uniformSample_avg]` leaves
  `(∑ x, ofDual (wp ((fun y => P a x ∨ R a x y) <$> $ᵗ F) …)) / |F|`: the averaging rule keeps
  the second draw under the first draw's sum, and `vcgen` does not descend into it.
* A bad-event bind rule (`Spec.bind_of_bad` of 49f365a74, specialised to a uniform draw)
  `Triple ($ᵗ β >>= f) (toDual (d / |β| + ε)) post` from `#{bad} ≤ d`, `post ≤ 1` and
  `∀ x, ¬bad x → Triple (f x) (toDual ε) post`, passed as
  `vcgen [Spec.ofSupport pre, Spec.uniformSample_bind_of_bad (bad := P _) (hd := hP _), …]`,
  *is* consumed: `vcgen` turns the triple premise into a goal and continues into `f x` under
  `¬bad x`. But the hole in `bad := P _` becomes a schematic variable abstracted over the
  continuation only, never over the prefix value `a` that `Spec.ofSupport` introduces later, so
  the hypothesis reads `¬P (?m f) x` and cannot be closed. A per-call-site argument that depends
  on earlier binders (as `frames`/`until` patterns allow) is what is missing.
-/

end VCVioTest.ProgramLogic.Probes.P6FreshDraw
