import ErdosProblems.Erdos118.GraphPayoff

/-!
Finite response guards extracted from actual red certificates. Conservative
runs use the concrete response selector and preserve red outcomes. Existence
of a full-order family of such runs is not assumed here.
-/

namespace Erdos118.ConservativeRuns

open LabelledExtensions DecisionStates AdaptiveGame

theorem terminal_none_of_left_response (payoff : Completed → Completed → Bool)
    (S : State × State) (n : ℕ) (R : Response S.1 (pairBound S))
    (hR : responseFor S.1 (pairBound S) n = some R) : terminalPayoff payoff S = none := by
  obtain ⟨S, T⟩ := S
  cases S <;> cases T <;> simp_all [terminalPayoff, responseFor]

theorem terminal_none_of_right_response (payoff : Completed → Completed → Bool)
    (S : State × State) (n : ℕ) (R : Response S.2 (pairBound S))
    (hR : responseFor S.2 (pairBound S) n = some R) : terminalPayoff payoff S = none := by
  obtain ⟨S, T⟩ := S
  cases S <;> cases T <;> simp_all [terminalPayoff, responseFor]

theorem red_left_bound {H : Set ℕ} (payoff : Completed → Completed → Bool)
    (S : State × State) (n : ℕ) (R : Response S.1 (pairBound S))
    (hred : RamseyGame.Outcome H (AdaptiveGame.game payoff S) false)
    (hside : allowedSide S false = true) (hR : responseFor S.1 (pairBound S) n = some R) :
    ∃ b : ℕ, ∀ a : R.family.members, (↑a.1 : Set ℕ) ⊆ H →
      (∀ x ∈ a.1, b < x) →
      RamseyGame.Outcome H (AdaptiveGame.game payoff (R.result a, S.2)) false := by
  have hnone := terminal_none_of_left_response payoff S n R hR
  rw [AdaptiveGame.game_eq] at hred
  simp only [build, hnone] at hred
  cases hred with
  | choiceFalse next h =>
    have hn := h (2 * n)
    have hmod : 2 * n % 2 = 0 := by omega
    have hdiv : 2 * n / 2 = n := by omega
    simp only [hmod, ↓reduceIte, hside, hdiv, hR] at hn
    cases hn with
    | response F next b value h => exact ⟨b, h⟩

theorem red_right_bound {H : Set ℕ} (payoff : Completed → Completed → Bool)
    (S : State × State) (n : ℕ) (R : Response S.2 (pairBound S))
    (hred : RamseyGame.Outcome H (AdaptiveGame.game payoff S) false)
    (hside : allowedSide S true = true) (hR : responseFor S.2 (pairBound S) n = some R) :
    ∃ b : ℕ, ∀ a : R.family.members, (↑a.1 : Set ℕ) ⊆ H →
      (∀ x ∈ a.1, b < x) →
      RamseyGame.Outcome H (AdaptiveGame.game payoff (S.1, R.result a)) false := by
  have hnone := terminal_none_of_right_response payoff S n R hR
  rw [AdaptiveGame.game_eq] at hred
  simp only [build, hnone] at hred
  cases hred with
  | choiceFalse next h =>
    have hn := h (2 * n + 1)
    have hmod : (2 * n + 1) % 2 ≠ 0 := by omega
    have hdiv : (2 * n + 1) / 2 = n := by omega
    simp only [hmod, ↓reduceIte, hside, hdiv, hR] at hn
    cases hn with
    | response F next b value h => exact ⟨b, h⟩

theorem left_guard_exists (H : Set ℕ) (payoff : Completed → Completed → Bool)
    (S : State × State) (n : ℕ) :
    ∃ b : ℕ, RamseyGame.Outcome H (AdaptiveGame.game payoff S) false →
      allowedSide S false = true →
      ∀ R : Response S.1 (pairBound S), responseFor S.1 (pairBound S) n = some R →
      ∀ a : R.family.members, (↑a.1 : Set ℕ) ⊆ H → (∀ x ∈ a.1, b < x) →
      RamseyGame.Outcome H (AdaptiveGame.game payoff (R.result a, S.2)) false := by
  classical
  by_cases hred : RamseyGame.Outcome H (AdaptiveGame.game payoff S) false
  · by_cases hside : allowedSide S false = true
    · cases hR : responseFor S.1 (pairBound S) n with
      | none => exact ⟨0, fun _ _ R he ↦ by simp at he⟩
      | some R =>
        obtain ⟨b, hb⟩ := red_left_bound payoff S n R hred hside hR
        refine ⟨b, fun _ _ R' he ↦ ?_⟩
        have hRR : R' = R := Option.some.inj he.symm
        subst R'
        exact hb
    · exact ⟨0, fun _ hs ↦ (hside hs).elim⟩
  · exact ⟨0, fun hr ↦ (hred hr).elim⟩

theorem right_guard_exists (H : Set ℕ) (payoff : Completed → Completed → Bool)
    (S : State × State) (n : ℕ) :
    ∃ b : ℕ, RamseyGame.Outcome H (AdaptiveGame.game payoff S) false →
      allowedSide S true = true →
      ∀ R : Response S.2 (pairBound S), responseFor S.2 (pairBound S) n = some R →
      ∀ a : R.family.members, (↑a.1 : Set ℕ) ⊆ H → (∀ x ∈ a.1, b < x) →
      RamseyGame.Outcome H (AdaptiveGame.game payoff (S.1, R.result a)) false := by
  classical
  by_cases hred : RamseyGame.Outcome H (AdaptiveGame.game payoff S) false
  · by_cases hside : allowedSide S true = true
    · cases hR : responseFor S.2 (pairBound S) n with
      | none => exact ⟨0, fun _ _ R he ↦ by simp at he⟩
      | some R =>
        obtain ⟨b, hb⟩ := red_right_bound payoff S n R hred hside hR
        refine ⟨b, fun _ _ R' he ↦ ?_⟩
        have hRR : R' = R := Option.some.inj he.symm
        subst R'
        exact hb
    · exact ⟨0, fun _ hs ↦ (hside hs).elim⟩
  · exact ⟨0, fun hr ↦ (hred hr).elim⟩

noncomputable def leftGuard (H : Set ℕ) (payoff : Completed → Completed → Bool)
    (S : State × State) (n : ℕ) : ℕ := Classical.choose (left_guard_exists H payoff S n)

noncomputable def rightGuard (H : Set ℕ) (payoff : Completed → Completed → Bool)
    (S : State × State) (n : ℕ) : ℕ := Classical.choose (right_guard_exists H payoff S n)

inductive Step (H : Set ℕ) (payoff : Completed → Completed → Bool) :
    (State × State) → (State × State) → Prop
  | left (S : State × State) (n : ℕ) (R : Response S.1 (pairBound S))
      (hside : allowedSide S false = true) (hR : responseFor S.1 (pairBound S) n = some R)
      (a : R.family.members) (supported : (↑a.1 : Set ℕ) ⊆ H)
      (large : ∀ x ∈ a.1, leftGuard H payoff S n < x) :
      Step H payoff S (R.result a, S.2)
  | right (S : State × State) (n : ℕ) (R : Response S.2 (pairBound S))
      (hside : allowedSide S true = true) (hR : responseFor S.2 (pairBound S) n = some R)
      (a : R.family.members) (supported : (↑a.1 : Set ℕ) ⊆ H)
      (large : ∀ x ∈ a.1, rightGuard H payoff S n < x) :
      Step H payoff S (S.1, R.result a)

theorem Step.preserves_red {H : Set ℕ} {payoff : Completed → Completed → Bool}
    {S T : State × State} (h : Step H payoff S T)
    (hred : RamseyGame.Outcome H (AdaptiveGame.game payoff S) false) :
    RamseyGame.Outcome H (AdaptiveGame.game payoff T) false := by
  cases h with
  | left n R hs hR a hH hlarge =>
    exact (Classical.choose_spec (left_guard_exists H payoff S n)) hred hs R hR a hH hlarge
  | right n R hs hR a hH hlarge =>
    exact (Classical.choose_spec (right_guard_exists H payoff S n)) hred hs R hR a hH hlarge

theorem Step.pairStep {H : Set ℕ} {payoff : Completed → Completed → Bool}
    {S T : State × State} (h : Step H payoff S T) : PairStep T S := by
  cases h with
  | left n R hs hR a hH hlarge => exact PairStep.left S.2 (R.step a)
  | right n R hs hR a hH hlarge => exact PairStep.right S.1 (R.step a)

def Run (H : Set ℕ) (payoff : Completed → Completed → Bool) :
    (State × State) → (State × State) → Prop := Relation.ReflTransGen (Step H payoff)

theorem Run.preserves_red {H : Set ℕ} {payoff : Completed → Completed → Bool}
    {S T : State × State} (h : Run H payoff S T)
    (hred : RamseyGame.Outcome H (AdaptiveGame.game payoff S) false) :
    RamseyGame.Outcome H (AdaptiveGame.game payoff T) false := by
  induction h with
  | refl => exact hred
  | tail hst htu ih => exact htu.preserves_red ih

theorem clear_terminal_red_of_runs (B : SimpleGraph Negative.Exact.G) (S T : Completed)
    {H : Set ℕ}
    (hin : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) false)
    (hout : RamseyGame.Outcome H (GraphPayoff.game B .outside (.initial, .initial)) false)
    (runIn : Run H (GraphPayoff.payoff B .inside)
      (.initial, .initial) (.complete S, .complete T))
    (runOut : Run H (GraphPayoff.payoff B .outside)
      (.initial, .initial) (.complete S, .complete T))
    (hroot : S.stem.root < T.stem.root) (hclear : ClearPairs.ClearPair S.stem T.stem) :
    ¬ B.Adj (GraphPayoff.vertex S) (GraphPayoff.vertex T) :=
  GraphPayoff.terminal_red_of_both B S T (runIn.preserves_red hin)
    (runOut.preserves_red hout) hroot hclear

end Erdos118.ConservativeRuns
