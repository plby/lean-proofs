import ErdosProblems.Erdos118.SingletonBodyReplay

/-!
Deferred replay for every actual target body parameter, with a separate
singleton branch. The parameter is fixed when the source marker is chosen.
-/

namespace Erdos118.OptionalBodyReplay

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays

inductive Prepared (H : Set ℕ) (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (right : Bool) (E : BodyDecision) (T : State) (P : Pending) where
  | singleton (data : SingletonBodyReplay.Prepared H B o right E T P)
  | positive (data : DeferredBodyReplay.Prepared H B o right E T P)

def Prepared.bound {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending} :
    Prepared H B o right E T P → ℕ
  | .singleton Z => Z.bound
  | .positive Z => Z.bound

theorem Prepared.lastRoot {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) : P.roots = [] := by
  cases Z with
  | singleton Z => exact Z.lastRoot
  | positive Z => exact Z.lastRoot

theorem Prepared.exactSlots {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) : ExactSlots.Exact (.leaf P) := by
  cases Z with
  | singleton Z => exact Z.exactSlots
  | positive Z => exact Z.exactSlots

def LabelShape (P : Pending) (Q : Position) : Prop :=
  Q.label = [P.position.entries.length] ∨
    1 < Q.label.length ∧ P.position.label.getLastD 0 ∈ Q.label ∧
      ∀ j ∈ Q.label, P.position.entries.length < j → P.position.label.getLastD 0 ≤ j

theorem fire {H : Set ℕ} (hH : H.Infinite) {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (hne : P.leaves ≠ []) :
    ∃ l : ℕ, ∃ A : BodyResponses.Setup E.stem l,
      A.position.ordinary = P.position.ordinary ∧
      A.position.entries = P.position.entries ∧ A.position.size = P.position.size ∧
      LabelShape P A.position ∧ Blue H B o right (.leaf (applyBody E A)) T ∧
      OtherBlue H B o right (.leaf (applyBody E A)) T := by
  cases Z with
  | singleton Z =>
    obtain ⟨hord, hlabel, _, hb, hh⟩ := SingletonBodyReplay.fire hH Z
    exact ⟨0, Z.setup, hord, rfl, rfl, Or.inl hlabel, hb, hh⟩
  | positive Z =>
    obtain ⟨hord, hb, hh⟩ := DeferredBodyReplay.fire hH Z hne
    have hn := Z.next_index hne
    refine ⟨Z.size, Z.setup hne, hord, rfl, rfl, Or.inr ⟨?_, hn.2⟩, hb, hh⟩
    change 1 < Z.label.length
    rw [Z.label_length]
    have h := Z.positive
    omega

theorem carry_of_run {H K : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {E : BodyDecision} {T : State} {P : Pending}
    (Z : Prepared H B o right E T P) (sourceRight : Bool) (Q : Pending) (S U : State)
    (hKH : K ⊆ H) (payoff : Completed → Completed → Bool)
    (hrun : ConservativeRuns.Run K payoff
      (pair sourceRight (.leaf P) S) (pair sourceRight (.leaf Q) U)) :
    ∃ W : Prepared H B o right E T Q, W.bound = Z.bound := by
  cases Z with
  | singleton Z =>
    obtain ⟨W, hb⟩ := SingletonBodyReplay.carry_of_run Z sourceRight Q S U hKH payoff hrun
    exact ⟨.singleton W, hb⟩
  | positive Z =>
    obtain ⟨W, hb, _⟩ := DeferredBodyReplay.carry_of_run Z sourceRight Q S U hKH payoff hrun
    exact ⟨.positive W, hb⟩

theorem prepare {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (originalRight targetRight : Bool)
    (D E : BodyDecision) (S T : State) (hD : ExactSlots.Exact (.body D)) (hR : D.roots = [])
    (hE : E.stem.ordinary = D.stem.ordinary)
    (hfirst : CommandBlue H B o originalRight (.body D) S)
    (hsecond : CommandBlue H B o targetRight (.body E) T) (d : ℕ) :
    ∃ k : ℕ, ∃ A : BodyResponses.Setup D.stem k,
      ∃ _Z : Prepared H B o targetRight E T (applyBody D A),
        ConservativeRuns.Step K (GraphPayoff.payoff B o)
          (pair originalRight (.body D) S) (pair originalRight (.leaf (applyBody D A)) S) ∧
        Blue H B o originalRight (.leaf (applyBody D A)) S ∧
        OtherBlue H B o originalRight (.leaf (applyBody D A)) S ∧
        ∀ x ∈ BodyResponses.newWord A.position, x ∈ K ∧ d < x := by
  obtain ⟨l, b, hb⟩ := body_setups B o targetRight E T hsecond
  cases l with
  | zero =>
    obtain ⟨k, A, Z, hs, hblue, hh, hf⟩ := SingletonBodyReplay.prepare hK hKH
      B o originalRight targetRight D E S T hD hR hE hfirst b hb d
    exact ⟨k, A, .singleton Z, hs, hblue, hh, hf⟩
  | succ l =>
    obtain ⟨k, A, Z, _, hs, hblue, hh, hf⟩ := DeferredBodyReplay.prepare hK hKH
      B o originalRight targetRight D E S T hD hR hE hfirst (l + 1) b (Nat.zero_lt_succ l) hb d
    exact ⟨k, A, .positive Z, hs, hblue, hh, hf⟩

end Erdos118.OptionalBodyReplay
