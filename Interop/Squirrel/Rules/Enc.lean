/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Interop.Squirrel.Avoids
public import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA.OneTime
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.OracleComp.EvalDist.Measure

/-!
# Encryption from one-time IND-CPA

BC14's axiom EncCCA1 (§7, Fig. 2; sound by Prop. 3) where the secret key is never used to decrypt:
if an asymmetric encryption scheme is IND-CPA secure, the encryptions of two messages under a
fresh key and fresh coins are indistinguishable, next to the public key and a context that uses
the secret key only through the public key:

```
pk(nk), enc(m₀; r, pk(nk)), u⃗ ∼ pk(nk), enc(m₁; r, pk(nk)), u⃗
```

It differs from EncCCA1 in three ways. There is no decryption, so IND-CPA replaces IND-CCA1. Both
sides use the same coin name, which is BC14's pair `r, r′` up to name renaming. And BC14's guard
`if EQL(u, u′) then … else u″`, which compares lengths, becomes a side condition: the two
messages have equal length (`lenOf`) at every tape (`EncSymbols.EqualLength`), so the guard always
takes its first branch. This is how LICS23's G.CCA1 (Prop. 19), the real-or-zero form of the rule,
gets equal lengths: its second message `zero (len m)` has the length of the first in every model.
The reduction submits only pairs of equal length (`EncSymbols.encReduction_isAdmissible`), so the
IND-CPA hypothesis is about adversaries the standard game admits, and a scheme that leaks lengths
can meet it.

* `EncSymbols D` names the scheme in a declaration: a key name `nk` and a coin name `r`, each at
  an honest constant index, and honest symbols `pkOf`, `encOf` and `lenOf`.
* `EncSymbols.scheme E M η` is the scheme a model implements: key generation draws the key
  coordinate's coin and applies `pkOf` to its sample, and encryption draws the coin coordinate's
  coin and applies `encOf`.
* The messages and the context are terms with one free variable standing for the public key,
  closed by substituting `pk(nk)` (`EncSymbols.challenge`). This is BC14's constraint that the
  secret key occur only in decryption position, with no decryption: `nk` occurs only under `pk`.
* The freshness conditions are syntactic: neither the messages nor the context use the key name
  or the coin name (`FTerm.AvoidsNames`, `Vec.AvoidsNames` at `EncSymbols.IsSecret`). They are
  decidable, and with the distinctness of the two names they are `EncInstance.Syntactic`, which
  `decide` checks on concrete instances. What they give is that the messages and the context read
  neither the key coordinate nor the coin coordinate of the honest tape
  (`FTerm.denote_update_eq_of_avoidsNames`).
* `EncSymbols.encReduction` is the named reduction. Given the public key it draws both tapes
  itself, evaluates the messages and the context at the public key, and runs the distinguisher's
  machine (`Machine.simulate`) with the attacker tape it drew, answering its input queries from the
  public key, the challenge ciphertext and the context's values. It never inverts the public key.
  If the messages it evaluates have different lengths it submits the first twice. Its last step
  returns the machine's run (`EncSymbols.encReduction_distinguish`, from `Machine.simulate_ofVals`),
  so the proof computes with the distinguisher's denotation (`Machine.test`).

`EncSymbols.advantage_challenge` is the concrete statement: at every `η` the distinguisher's
advantage between the two challenge vectors equals the one-time IND-CPA advantage of the
reduction, with factor one. The coupling is
`SampleableType.prEvent_uniformSample_prod_update_update`: the game's key and coins, written into
the reduction's own honest tape, give a uniform tape.

`Valid.equiv_enc` is the rule, from the IND-CPA hypothesis for the image of the class under the
reduction. The runtime `ProbCompRuntime.probComp` imposes no time or query bound, so the
hypothesis bounds every image of an admitted distinguisher, however slow: efficiency enters only
through the class `C`, as a hypothesis on the reductions of its members.

## References

* [BC14] Bana, Comon-Lundh, *A Computationally Complete Symbolic Attacker for Equivalence
  Properties*, CCS 2014: §7, Fig. 2 and Prop. 3.
* [LICS23] Baelde, Koutsos, Lallemand, *A Higher-Order Indistinguishability Logic for
  Cryptographic Reasoning*, LICS 2023: Prop. 19.
-/

public section

namespace Interop.Squirrel

open IPFunctor IPFunctor.ScopedSignature AsymmEncAlg

variable {B : Type} {D : Decl B}

/-- The symbols of an asymmetric encryption scheme in a declaration: a key name and a coin name,
each at an honest constant index, the public key of a key, the encryption of a message with coins
under a public key, and the length of a message, which encryption may reveal. -/
structure EncSymbols (D : Decl B) where
  /-- The index type of the key name. -/
  keyIdx : Ty B
  /-- The type of keys. -/
  keyTy : Ty B
  /-- The index type of the coin name. -/
  coinIdx : Ty B
  /-- The type of encryption coins. -/
  coinTy : Ty B
  /-- The type of public keys. -/
  pkTy : Ty B
  /-- The type of messages. -/
  msgTy : Ty B
  /-- The type of ciphertexts. -/
  cTy : Ty B
  /-- The type of message lengths. -/
  lenTy : Ty B
  /-- The key name `nk`. -/
  nk : D.Name keyIdx keyTy
  /-- The index at which the key name is read. -/
  ik : D.Fn keyIdx
  /-- The coin name `r`. -/
  nr : D.Name coinIdx coinTy
  /-- The index at which the coin name is read. -/
  ir : D.Fn coinIdx
  /-- The public key of a key. -/
  pkOf : D.Fn (.arrow keyTy pkTy)
  /-- Encryption of a message with coins under a public key. -/
  encOf : D.Fn (.arrow msgTy (.arrow coinTy (.arrow pkTy cTy)))
  /-- The length of a message (BC14's `EQL` compares it). -/
  lenOf : D.Fn (.arrow msgTy lenTy)

namespace EncSymbols

variable (E : EncSymbols D)

/-- The key name with its types. -/
abbrev keyName : (a : Ty B) × (b : Ty B) × D.Name a b := ⟨_, _, E.nk⟩

/-- The coin name with its types. -/
abbrev coinName : (a : Ty B) × (b : Ty B) × D.Name a b := ⟨_, _, E.nr⟩

/-- The key name and the coin name: the names that the messages and the context may not use. -/
abbrev IsSecret (n : (a : Ty B) × (b : Ty B) × D.Name a b) : Prop :=
  n = E.keyName ∨ n = E.coinName

/-- The coordinate of the honest tape that the key reads. -/
abbrev keySlot (M : Model D) (η : ℕ) : M.Slot η := ⟨E.keyName, M.fn η E.ik⟩

/-- The coordinate of the honest tape that the coins read. -/
abbrev coinSlot (M : Model D) (η : ℕ) : M.Slot η := ⟨E.coinName, M.fn η E.ir⟩

/-! ## Syntax -/

/-- The public key `pk(nk)`. -/
@[expose] def pkTerm : FTerm D [] E.pkTy :=
  FTerm.app (FTerm.fn E.pkOf) (FTerm.name E.nk (FTerm.fn E.ik))

/-- The coins `r`. -/
@[expose] def coinTerm : FTerm D [] E.coinTy := FTerm.name E.nr (FTerm.fn E.ir)

/-- The encryption of `m` with the coins `r` under `pk(nk)`. -/
@[expose] def encTerm (m : FTerm D [] E.msgTy) : FTerm D [] E.cTy :=
  FTerm.app (FTerm.app (FTerm.app (FTerm.fn E.encOf) m) E.coinTerm) E.pkTerm

/-- The challenge vector `pk(nk), enc(m{x ↦ pk(nk)}; r, pk(nk)), u⃗{x ↦ pk(nk)}`, for a message and
a context whose free variable `x` stands for the public key. -/
@[expose] def challenge {τs : List (Ty B)} (m : FTerm D [.loc E.pkTy] E.msgTy)
    (u : Vec D [.loc E.pkTy] τs) : Vec D [] (E.pkTy :: E.cTy :: τs) :=
  Env.cons E.pkTerm (Env.cons (E.encTerm (m.substOne E.pkTerm))
    fun _ x => (u _ x).substOne E.pkTerm)

/-! ## Semantics -/

/-- The public key at `η` that an honest tape determines: `pkOf` of the key coordinate's sample. -/
@[expose] def pkVal (M : Model D) (η : ℕ) (ρh : M.TapeH η) : E.pkTy.Value M.carrier η :=
  M.fn η E.pkOf (M.sample η E.keyTy (ρh (E.keySlot M η)))

/-- The two messages have the same length at every tape, read at the tape's public key. This is
BC14's guard `EQL(u, u′)` holding surely, as in LICS23's G.CCA1, whose second message
`zero (len m)` has the length of the first in every model. -/
@[expose] def EqualLength (M : Model D) (m₀ m₁ : FTerm D [.loc E.pkTy] E.msgTy) : Prop :=
  ∀ η (ρ : M.Tape η), M.fn η E.lenOf (FTerm.evalAt M η ρ m₀ (E.pkVal M η ρ.2)) =
    M.fn η E.lenOf (FTerm.evalAt M η ρ m₁ (E.pkVal M η ρ.2))

/-- The scheme a model implements at `η`: key generation draws a key coin and applies `pkOf` to
its sample, and encryption draws a coin and applies `encOf`. There is no secret key, and
decryption, which the IND-CPA game never runs, rejects every ciphertext. -/
@[expose] def scheme (M : Model D) (η : ℕ) :
    AsymmEncAlg ProbComp (E.msgTy.Value M.carrier η) (E.pkTy.Value M.carrier η) Unit
      (E.cTy.Value M.carrier η) where
  keygen := do
    let kc ← $ᵗ (M.Coin η E.keyTy)
    pure (M.fn η E.pkOf (M.sample η E.keyTy kc), ())
  encrypt pk m := do
    let rc ← $ᵗ (M.Coin η E.coinTy)
    pure (M.fn η E.encOf m (M.sample η E.coinTy rc) pk)
  decrypt _ _ := pure none

/-- **The reduction** from a distinguishing machine of the challenge vectors to a one-time
IND-CPA adversary. Given the public key, it draws both tapes, evaluates the two messages at the
public key and keeps the key and the tapes; given the ciphertext, it evaluates the context at the
public key and runs the machine `A` (`Machine.simulate`) with the attacker tape it drew, answering
its input queries from the public key, the ciphertext and the context's values. If the two
messages have different lengths it submits the first one twice, so the game is asked only about
pairs of equal length (`encReduction_isAdmissible`); under `EqualLength` this never happens. -/
@[expose] noncomputable def encReduction {M : Model D} {τs : List (Ty B)}
    (m₀ m₁ : FTerm D [.loc E.pkTy] E.msgTy) (u : Vec D [.loc E.pkTy] τs)
    (A : Machine M (E.pkTy :: E.cTy :: τs) .bool) (η : ℕ) :
    IND_CPA_OneTime_Adversary (E.scheme M η) where
  State := E.pkTy.Value M.carrier η × M.Tape η
  chooseMessages pk := do
    let ρ ← $ᵗ (M.Tape η)
    pure (FTerm.evalAt M η ρ m₀ pk,
      @ite _ (M.fn η E.lenOf (FTerm.evalAt M η ρ m₀ pk) =
          M.fn η E.lenOf (FTerm.evalAt M η ρ m₁ pk)) (Classical.propDecidable _)
        (FTerm.evalAt M η ρ m₁ pk) (FTerm.evalAt M η ρ m₀ pk), (pk, ρ))
  distinguish st c := A.simulate η st.2.1
    (InputImpl.ofVals (Env.cons st.1 (Env.cons c fun _ x => FTerm.evalAt M η st.2 (u _ x) st.1)))

variable {E}

/-- The reduction's last step returns the machine's run on the public key, the ciphertext and the
context's values: the fusion of its input answers into the run (`Machine.simulate_ofVals`). -/
theorem encReduction_distinguish {M : Model D} {τs : List (Ty B)}
    (m₀ m₁ : FTerm D [.loc E.pkTy] E.msgTy) (u : Vec D [.loc E.pkTy] τs)
    (A : Machine M (E.pkTy :: E.cTy :: τs) .bool) (η : ℕ)
    (st : (E.encReduction m₀ m₁ u A η).State) (c : E.cTy.Value M.carrier η) :
    (E.encReduction m₀ m₁ u A η).distinguish st c =
      pure (A.test η (Env.cons st.1 (Env.cons c fun _ x => FTerm.evalAt M η st.2 (u _ x) st.1))
        st.2.1) :=
  Machine.simulate_ofVals A _ _

/-- The reduction submits only pairs of messages of equal length: it is admissible for the
leakage `lenOf`. -/
theorem encReduction_isAdmissible {M : Model D} {τs : List (Ty B)}
    (m₀ m₁ : FTerm D [.loc E.pkTy] E.msgTy) (u : Vec D [.loc E.pkTy] τs)
    (A : Machine M (E.pkTy :: E.cTy :: τs) .bool) (η : ℕ) :
    (E.encReduction m₀ m₁ u A η).IsAdmissible (M.fn η E.lenOf) := by
  intro pk z hz
  obtain ⟨ρ, -, hz⟩ := (mem_support_bind_iff _ _ _).1 hz
  obtain rfl := (mem_support_pure_iff _ _).1 hz
  dsimp only
  split_ifs with h
  · exact h
  · rfl

/-- The challenge vector at `(η, ρ)`: the public key of the key coordinate's sample, the
encryption of the message read at that public key with the coin coordinate's sample, and the
context read at that public key. -/
theorem rv_challenge {M : Model D} (C : AdvClass M) {τs : List (Ty B)}
    (m : FTerm D [.loc E.pkTy] E.msgTy) (u : Vec D [.loc E.pkTy] τs)
    (env : Env (Kind.Value M) []) (η : ℕ) (ρ : M.Tape η) :
    Vec.rv M C (E.challenge m u) env η ρ =
      Env.cons (E.pkVal M η ρ.2)
        (Env.cons (M.fn η E.encOf (FTerm.evalAt M η ρ m (E.pkVal M η ρ.2))
            (M.sample η E.coinTy (ρ.2 (E.coinSlot M η))) (E.pkVal M η ρ.2))
          fun _ x => FTerm.evalAt M η ρ (u _ x) (E.pkVal M η ρ.2)) := by
  funext τ x
  cases x with
  | zero => rfl
  | succ x =>
    cases x with
    | zero =>
      exact congrArg (fun y => M.fn η E.encOf y _ _)
        (FTerm.denote_substOne_apply M C m E.pkTerm env η ρ)
    | succ x => exact FTerm.denote_substOne_apply M C (u _ x) E.pkTerm env η ρ

/-- One branch of the game is an event of the uniform tape: the game's key coin and encryption
coin, written into the reduction's honest tape, make it uniform. -/
private theorem prEvent_experiment (hkr : E.keyName ≠ E.coinName) {M : Model D} (C : AdvClass M)
    {τs : List (Ty B)} {m₀ m₁ : FTerm D [.loc E.pkTy] E.msgTy} {u : Vec D [.loc E.pkTy] τs}
    (hm₀ : m₀.AvoidsNames E.IsSecret) (hm₁ : m₁.AvoidsNames E.IsSecret)
    (hu : u.AvoidsNames E.IsSecret) (hlen : E.EqualLength M m₀ m₁)
    (A : Machine M (E.pkTy :: E.cTy :: τs) .bool) (env : Env (Kind.Value M) []) (η : ℕ)
    (b : Bool) :
    Pr{let z ← IND_CPA_OneTime_Experiment (E.encReduction m₀ m₁ u A η) b}[z = true] =
      Pr{let ρ ← $ᵗ (M.Tape η)}[
        A.test η (Vec.rv M C (E.challenge (if b then m₀ else m₁) u) env η ρ) ρ.1 = true] := by
  classical
  have := D.finite_names
  have : ∀ n : (a : Ty B) × (b : Ty B) × D.Name a b, Finite (n.1.Value M.carrier η) :=
    fun n => M.finite_index η n.2.2
  have key := SampleableType.prEvent_uniformSample_prod_update_update (β := M.TapeA η)
    (R := fun k : M.Slot η => M.Coin η k.1.2.1) (E.keySlot M η) (E.coinSlot M η)
    (fun ρ : M.Tape η =>
      A.test η (Vec.rv M C (E.challenge (if b then m₀ else m₁) u) env η ρ) ρ.1 = true)
  refine Eq.trans ?_ key
  simp only [IND_CPA_OneTime_Experiment, scheme, encReduction, Machine.simulate_ofVals,
    prEvent_norm]
  refine congrArg prEvent (bind_congr fun kc => bind_congr fun ρ => ?_)
  refine congrArg (· <$> _) (funext fun rc => ?_)
  have hks : E.keySlot M η ≠ E.coinSlot M η := fun h => hkr (congrArg Sigma.fst h)
  have hk : Function.update (Function.update ρ.2 (E.keySlot M η) kc) (E.coinSlot M η) rc
      (E.keySlot M η) = kc := by
    rw [Function.update_of_ne hks, Function.update_self]
  have hr : Function.update (Function.update ρ.2 (E.keySlot M η) kc) (E.coinSlot M η) rc
      (E.coinSlot M η) = rc := Function.update_self _ _ _
  have hav : ∀ {τ : Ty B} {t : FTerm D [.loc E.pkTy] τ}, t.AvoidsNames E.IsSecret → ∀ x,
      FTerm.evalAt M η (ρ.1, Function.update (Function.update ρ.2 (E.keySlot M η) kc)
        (E.coinSlot M η) rc) t x = FTerm.evalAt M η ρ t x := fun ht x => by
    rw [FTerm.evalAt, FTerm.evalAt,
      FTerm.denote_update_eq_of_avoidsNames ht M ρ.1 _ (k := E.coinSlot M η) (Or.inr rfl),
      FTerm.denote_update_eq_of_avoidsNames ht M ρ.1 _ (k := E.keySlot M η) (Or.inl rfl)]
  have hg := hlen η (ρ.1, Function.update (Function.update ρ.2 (E.keySlot M η) kc)
    (E.coinSlot M η) rc)
  simp only [pkVal, hk, hav hm₀, hav hm₁] at hg
  simp only [rv_challenge, pkVal, hk, hr, hav (hu _ _), ite_eq_left hg]
  cases b <;> simp [hav hm₀, hav hm₁] <;> rfl

/-- **The concrete statement.** At every `η`, a distinguisher's advantage between the two
challenge vectors is the one-time IND-CPA advantage of `encReduction`, with factor one. -/
theorem advantage_challenge (hkr : E.keyName ≠ E.coinName) {M : Model D} (C : AdvClass M)
    {τs : List (Ty B)} {m₀ m₁ : FTerm D [.loc E.pkTy] E.msgTy} {u : Vec D [.loc E.pkTy] τs}
    (hm₀ : m₀.AvoidsNames E.IsSecret) (hm₁ : m₁.AvoidsNames E.IsSecret)
    (hu : u.AvoidsNames E.IsSecret) (hlen : E.EqualLength M m₀ m₁)
    (A : Machine M (E.pkTy :: E.cTy :: τs) .bool) (env : Env (Kind.Value M) []) (η : ℕ) :
    advantage A.test (Vec.rv M C (E.challenge m₀ u) env) (Vec.rv M C (E.challenge m₁ u) env) η =
      IND_CPA_OneTime_Advantage (E.scheme M η) ProbCompRuntime.probComp
        (E.encReduction m₀ m₁ u A η) := by
  rw [IND_CPA_OneTime_Advantage_eq_boolDist, MeasureTheory.Measure.boolDist,
    ← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton,
    prEvent_experiment hkr C hm₀ hm₁ hu hlen A env η,
    prEvent_experiment hkr C hm₀ hm₁ hu hlen A env η]
  rfl

end EncSymbols

/-- **Encryption from one-time IND-CPA** (BC14 §7, axiom EncCCA1 without decryption, Prop. 3;
LICS23 G.CCA1, Prop. 19, in left-or-right form):

```
pk(nk), enc(m₀; r, pk(nk)), u⃗ ∼ pk(nk), enc(m₁; r, pk(nk)), u⃗
```

where the messages and the context are closed by substituting `pk(nk)` for their free variable.

* The key and coin names are distinct (`hkr`), and the messages and the context use neither
  (`hm₀`, `hm₁`, `hu`): `nk` occurs only under `pk`, and `r` is fresh. These are syntactic and
  decidable.
* In every admitted model the two messages have equal length at every tape (`hlen`,
  `EncSymbols.EqualLength`): BC14's guard `EQL(m₀, m₁)` holds surely.
* `hcpa` is the assumption, about the image of the class under the named reduction
  `EncSymbols.encReduction`: every admitted machine, run by the reduction, becomes a one-time
  IND-CPA adversary of negligible advantage against the scheme the model implements.
* `ProbCompRuntime.probComp` imposes no time or query bound on the reduction, so `hcpa` asserts
  security against the reductions of every admitted distinguisher, however slow. Efficiency
  enters only through the class: `hcpa` is plausible only when `C` admits efficient machines and
  the reduction preserves efficiency.

The proof is `EncSymbols.advantage_challenge`, an equality at every `η`. -/
theorem Valid.equiv_enc (E : EncSymbols D) (hkr : E.keyName ≠ E.coinName)
    {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M} {Θ : List (Form D [])}
    {τs : List (Ty B)} {m₀ m₁ : FTerm D [.loc E.pkTy] E.msgTy} {u : Vec D [.loc E.pkTy] τs}
    {ho : Ty.IndistOrder (E.pkTy :: E.cTy :: τs)}
    (hm₀ : m₀.AvoidsNames E.IsSecret) (hm₁ : m₁.AvoidsNames E.IsSecret)
    (hu : u.AvoidsNames E.IsSecret) (hlen : ∀ M, R M → E.EqualLength M m₀ m₁)
    (hcpa : ∀ M : Model D, M.RespectsLabels → R M →
      ∀ A : Machine M (E.pkTy :: E.cTy :: τs) .bool, (C M).mem A →
        negligible fun η => IND_CPA_OneTime_Advantage (E.scheme M η) ProbCompRuntime.probComp
          (E.encReduction m₀ m₁ u A η)) :
    Valid R C Θ (.equiv (E.challenge m₀ u) (E.challenge m₁ u) ho) := by
  intro M hl hRM env _
  exact Form.holds_equiv.2 fun A hA => negligible_of_le
    (fun η => (EncSymbols.advantage_challenge hkr (C M) hm₀ hm₁ hu (hlen M hRM) A env η).le)
    (hcpa M hl hRM A hA)

/-! ## Instances, for derivations -/

/-- An instance of the encryption rule: the scheme's symbols, two messages and a context. -/
structure EncInstance (D : Decl B) where
  /-- The scheme's symbols. -/
  E : EncSymbols D
  /-- The types of the context. -/
  τs : List (Ty B)
  /-- The first message, with the public key free. -/
  m₀ : FTerm D [.loc E.pkTy] E.msgTy
  /-- The second message, with the public key free. -/
  m₁ : FTerm D [.loc E.pkTy] E.msgTy
  /-- The context, with the public key free. -/
  u : Vec D [.loc E.pkTy] τs
  /-- The vectors of the conclusion have order at most one. -/
  order : Ty.IndistOrder (E.pkTy :: E.cTy :: τs)

/-- The syntactic side conditions of `Valid.equiv_enc` for an instance: distinct key and coin
names, which neither the messages nor the context use. For names with decidable equality they
are decidable, and `decide` checks them. -/
@[expose] def EncInstance.Syntactic (e : EncInstance D) : Prop :=
  e.E.keyName ≠ e.E.coinName ∧ e.m₀.AvoidsNames e.E.IsSecret ∧
    e.m₁.AvoidsNames e.E.IsSecret ∧ e.u.AvoidsNames e.E.IsSecret

instance EncInstance.decidableSyntactic [DecidableEq ((a : Ty B) × (b : Ty B) × D.Name a b)]
    (e : EncInstance D) : Decidable e.Syntactic :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The semantic hypotheses of `Valid.equiv_enc` for an instance: equal lengths in every admitted
model, and one-time IND-CPA security against the reductions of the admitted distinguishers. -/
@[expose] def EncInstance.Holds (R : Model D → Prop) (C : ∀ M : Model D, AdvClass M)
    (e : EncInstance D) : Prop :=
  (∀ M, R M → e.E.EqualLength M e.m₀ e.m₁) ∧
    ∀ M : Model D, M.RespectsLabels → R M →
      ∀ A : Machine M (e.E.pkTy :: e.E.cTy :: e.τs) .bool, (C M).mem A →
        negligible fun η => IND_CPA_OneTime_Advantage (e.E.scheme M η) ProbCompRuntime.probComp
          (e.E.encReduction e.m₀ e.m₁ e.u A η)

/-- The encryption rule at an instance whose side conditions hold. -/
theorem EncInstance.valid {R : Model D → Prop} {C : ∀ M : Model D, AdvClass M}
    {Θ : List (Form D [])} (e : EncInstance D) (hs : e.Syntactic) (h : e.Holds R C) :
    Valid R C Θ (.equiv (e.E.challenge e.m₀ e.u) (e.E.challenge e.m₁ e.u) e.order) :=
  Valid.equiv_enc e.E hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 h.1 h.2

end Interop.Squirrel
