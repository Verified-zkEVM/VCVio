/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kobi Gurkan, Quang Dao
-/

module
public import VCVio.Schemes.Schnorr.AGM.Reduction

/-! # Soundness of the single-pass Schnorr extractor

Certified algebraicity preserves the interpretation of chronological signing commitments.
Freshness excludes programmed signing entries at the forgery point. Every accepted execution
whose first live hash denominator is nonzero therefore returns the secret scalar.
-/

public section

open OracleComp OracleSpec GroupModel.Interaction GroupModel.LinearFunctional

namespace Schnorr.AGM.Reduction

variable {F G M : Type}

/-- Every read preserves the received basis and signing history and returns the
challenge of the retained cache entry. Its representation is fixed on a miss. -/
private theorem read_spec [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]
    (g pk : G) (s : State F G M) (hs : s.Valid g pk)
    (key : M × G) (a : AffineForm F) (ha : evalPoint a g pk = key.2)
    (c : F) (s' : State F G M) (h : (c, s') ∈ support ((read key a).run s)) :
    s'.Valid g pk ∧ s'.representations = s.representations ∧
      s'.signed = s.signed ∧ s'.malformed = s.malformed ∧
      ∃ e, s'.cache key = some e ∧ e.challenge = c := by
  cases hc : s.cache key with
  | some e =>
      simp only [read, StateT.run, hc, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨hs, rfl, rfl, rfl, e, hc, rfl⟩
  | none =>
      simp only [read, StateT.run, hc] at h
      change (c, s') ∈ support (do let d ← $ᵗ F; pure (d, record s key a d)) at h
      rw [mem_support_bind_iff] at h
      obtain ⟨d, _, hd⟩ := h
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hd
      rcases hd with ⟨rfl, rfl⟩
      exact ⟨record_valid g pk s hs key a ha c, rfl, rfl, rfl,
        ⟨c, some a⟩, by simp [record], rfl⟩

/-- Freshness excludes simulator-programmed entries. A valid accepting signature
therefore extracts from the first live hash representation whenever bad is false. -/
private theorem cached_extract [Field F] [AddCommGroup G] [Module F G]
    (g : G) (hg : Function.Injective (fun x : F => x • g))
    (x : F) (s : State F G M) (hs : s.Valid g (x • g))
    (m : M) (R : G) (c z : F) (e : Entry F)
    (he : s.cache (m, R) = some e) (hc : e.challenge = c)
    (hfresh : m ∉ s.signed) (hv : z • g = R + c • (x • g)) (hb : s.bad = false) :
    (match e.representation with
      | some a => (z - a.const) / (a.lin + c)
      | none => 0) = x := by
  have h := hs (m, R) e he
  cases hr : e.representation with
  | none => exact (hfresh (by simpa only [hr] using h)).elim
  | some a =>
      simp only [hr] at h ⊢
      apply Schnorr.AGM.extract g hg x c z a
      · simpa only [h.1] using hv
      · simpa only [hc] using h.2 hb

/-- The final hash query participates in the same first-representation rule. -/
private theorem finish_sound [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]
    (g : G) (hg : Function.Injective (fun x : F => x • g))
    (x : F) (s : State F G M) (hs : s.Valid g (x • g))
    (out : Explained F (M × F) (Group G))
    (hout : out.Valid (representedBasis g (x • g) s.representations))
    (answer : Bool × F) (s' : State F G M)
    (h : (answer, s') ∈ support ((finish g (x • g) out).run s))
    (hwin : answer.1 = true) (hbad : s'.bad = false) : answer.2 = x := by
  cases hgroups : out.value.groups () with
  | nil =>
      simp only [finish, hgroups, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at h
      rw [h.1] at hwin
      cases hwin
  | cons R rest =>
      cases rest with
      | cons R' rest =>
          simp only [finish, hgroups, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at h
          rw [h.1] at hwin
          cases hwin
      | nil =>
          obtain ⟨coeff, hcoeff, _, heval⟩ :=
            valid_singleton g (x • g) R s.representations out hout hgroups
          simp only [finish, hgroups, hcoeff, StateT.run_bind, StateT.run_get,
            pure_bind, StateT.run_pure] at h
          rw [mem_support_bind_iff] at h
          obtain ⟨⟨c, t⟩, ht, hresult⟩ := h
          simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hresult
          rcases hresult with ⟨ha, rfl⟩
          subst answer
          have hread := read_spec g (x • g) s hs
            (out.value.data.1, R) (flatten coeff s.representations) heval c s' ht
          obtain ⟨e, he, hc⟩ := hread.2.2.2.2
          have hw : out.value.data.1 ∉ s'.signed ∧
              out.value.data.2 • g = R + c • (x • g) := by
            simpa using (Bool.and_eq_true_iff.mp hwin).2
          simp only [he]
          have hsol := cached_extract g hg x s' hread.1 out.value.data.1 R c out.value.data.2
            e he hc hw.1 hw.2 hbad
          cases e with
          | mk ec er => cases er <;> exact hsol


private theorem handler_spec [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]
    (g pk : G) (s : State F G M) (hs : s.Valid g pk)
    (q : Explained F (Request M) (Group G))
    (hq : q.Valid (representedBasis g pk s.representations))
    (reply : Message (Reply F M q.value.data) (Group G)) (t : State F G M)
    (h : (reply, t) ∈ support ((handler g pk q).run s)) :
    t.Valid g pk ∧ representedBasis g pk t.representations =
      extend (representedBasis g pk s.representations) reply.groups := by
  rcases q with ⟨⟨request, groups⟩, coeffs⟩
  cases request with
  | random n =>
      simp only [handler, StateT.run] at h
      rw [mem_support_bind_iff] at h
      obtain ⟨v, _, h⟩ := h
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      by_cases he : groups () = []
      · simp only [he]
        exact ⟨hs, by funext u; simp [extend]⟩
      · simp only [he]
        exact ⟨rejected_valid g pk s hs, by funext u; simp [rejected, extend]⟩
  | hash m =>
      simp only [handler, StateT.run] at h
      split at h
      · rename_i R coeff hR hcoeff
        obtain ⟨co, hco, _, heval⟩ := valid_singleton g pk R s.representations
          ⟨⟨Request.hash m, groups⟩, coeffs⟩ hq hR
        have hco' : co = coeff := List.singleton_injective (hco.symm.trans hcoeff)
        subst co
        rw [mem_support_bind_iff] at h
        obtain ⟨⟨c, st⟩, hc, h⟩ := h
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have hr := read_spec g pk s hs (m, R) (flatten coeff s.representations) heval c t hc
        refine ⟨hr.1, ?_⟩
        rw [hr.2.1]
        funext u
        simp [extend, scalarReply]
      · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact ⟨rejected_valid g pk s hs, by funext u; simp [rejected, extend, scalarReply]⟩
  | sign m =>
      by_cases he : groups () = []
      · simp only [handler, StateT.run, he, ne_eq, not_true_eq_false, ite_false] at h
        rw [mem_support_bind_iff] at h
        obtain ⟨c, _, h⟩ := h
        rw [mem_support_bind_iff] at h
        obtain ⟨z, _, h⟩ := h
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact ⟨signedState_valid g pk s hs m c z, signedState_basis g pk s m c z⟩
      · simp only [handler, StateT.run, he, ne_eq, not_false_eq_true, ite_true,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact ⟨rejected_valid g pk s hs, by funext u; simp [rejected, extend, scalarReply]⟩

/-- The algebraicity certificate applies on every adaptive reply path. -/
private theorem simulate_valid [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]
    (g pk : G)
    (program : OracleComp (explainedSpec F (Group G) (Request M) (Reply F M))
      (Explained F (M × F) (Group G)))
    (s : State F G M) (hs : s.Valid g pk)
    (halg : IsAlgebraic (representedBasis g pk s.representations) program)
    (out : Explained F (M × F) (Group G)) (t : State F G M)
    (h : (out, t) ∈ support ((simulateQ (handler g pk) program).run s)) :
    t.Valid g pk ∧ out.Valid (representedBasis g pk t.representations) := by
  induction program using OracleComp.inductionOn generalizing s out t with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨hs, halg⟩
  | query_bind q next ih =>
      obtain ⟨hq, hn⟩ := (isAlgebraic_query _ _ _).mp halg
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at h
      rw [mem_support_bind_iff] at h
      obtain ⟨⟨reply, st⟩, hr, h⟩ := h
      have hstep := handler_spec g pk s hs q hq reply st hr
      exact ih reply st hstep.1 (by rw [hstep.2]; exact hn reply) out t h

/-- In the actual named reduction, every accepted nonbad run returns the secret. -/
theorem run_extract [Field F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [DecidableEq M] [SampleableType F]
    (g : G) (hg : Function.Injective (fun x : F => x • g))
    (x : F) (adv : Schnorr.AlgebraicAdversary F G M) (answer : Bool × F) (t : State F G M)
    (h : (answer, t) ∈ support (run g (x • g) adv))
    (hwin : answer.1 = true) (hbad : t.bad = false) : answer.2 = x := by
  simp only [run, StateT.run_bind] at h
  rw [mem_support_bind_iff] at h
  obtain ⟨⟨out, st⟩, hr, h⟩ := h
  have hsim := simulate_valid g (x • g) (adv.main (initial g (x • g))) {}
    (initial_valid g (x • g)) (by simpa using adv.algebraic (initial g (x • g))) out st hr
  exact finish_sound g hg x st hsim.1 out hsim.2 answer t h hwin hbad

end Schnorr.AGM.Reduction
