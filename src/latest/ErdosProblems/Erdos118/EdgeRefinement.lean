import ErdosProblems.Erdos118.ConservativeRuns

/-!
Refine an actual blue graph game to one symmetric Boolean edge class on
an infinite subalphabet. This does not exclude either refined inside case.
-/

namespace Erdos118.EdgeRefinement

open LabelledExtensions DecisionStates AdaptiveGame
open Negative Negative.Exact

theorem red_or {H : Set ℕ} (p q : Completed → Completed → Bool) (S : State × State)
    (hp : RamseyGame.Outcome H (AdaptiveGame.game p S) false)
    (hq : RamseyGame.Outcome H (AdaptiveGame.game q S) false) :
    RamseyGame.Outcome H (AdaptiveGame.game (fun U V ↦ p U V || q U V) S) false := by
  induction S using pairStep_wellFounded.induction with
  | h S ih =>
    by_cases hterm : ∃ U V : Completed, S = (.complete U, .complete V)
    · obtain ⟨U, V, rfl⟩ := hterm
      rw [AdaptiveGame.game_complete] at hp hq ⊢
      rw [RamseyGame.outcome_leaf_iff.mp hp, RamseyGame.outcome_leaf_iff.mp hq]
      exact RamseyGame.Outcome.leaf false
    · have hnone : terminalPayoff (fun U V ↦ p U V || q U V) S = none := by
        obtain ⟨S, T⟩ := S
        cases S <;> cases T <;> simp_all [terminalPayoff]
      rw [AdaptiveGame.game_eq]
      simp only [build, hnone]
      apply RamseyGame.Outcome.choiceFalse
      intro n
      by_cases heven : n % 2 = 0
      · simp only [heven, ↓reduceIte]
        by_cases hside : allowedSide S false = true
        · simp only [hside, ↓reduceIte]
          cases hR : responseFor S.1 (pairBound S) (n / 2) with
          | none => exact RamseyGame.Outcome.leaf false
          | some R =>
            obtain ⟨bp, hbp⟩ := ConservativeRuns.red_left_bound p S (n / 2) R hp hside hR
            obtain ⟨bq, hbq⟩ := ConservativeRuns.red_left_bound q S (n / 2) R hq hside hR
            apply RamseyGame.Outcome.response _ _ (max bp bq) false
            intro a ha hl
            exact ih (R.result a, S.2) (PairStep.left S.2 (R.step a))
              (hbp a ha (fun x hx ↦ (le_max_left _ _).trans_lt (hl x hx)))
              (hbq a ha (fun x hx ↦ (le_max_right _ _).trans_lt (hl x hx)))
        · simp only [hside]; exact RamseyGame.Outcome.leaf false
      · simp only [heven, ↓reduceIte]
        by_cases hside : allowedSide S true = true
        · simp only [hside, ↓reduceIte]
          cases hR : responseFor S.2 (pairBound S) (n / 2) with
          | none => exact RamseyGame.Outcome.leaf false
          | some R =>
            obtain ⟨bp, hbp⟩ := ConservativeRuns.red_right_bound p S (n / 2) R hp hside hR
            obtain ⟨bq, hbq⟩ := ConservativeRuns.red_right_bound q S (n / 2) R hq hside hR
            apply RamseyGame.Outcome.response _ _ (max bp bq) false
            intro a ha hl
            exact ih (S.1, R.result a) (PairStep.right S.1 (R.step a))
              (hbp a ha (fun x hx ↦ (le_max_left _ _).trans_lt (hl x hx)))
              (hbq a ha (fun x hx ↦ (le_max_right _ _).trans_lt (hl x hx)))
        · simp only [hside]; exact RamseyGame.Outcome.leaf false

theorem blue_summand {H : Set ℕ} (hH : H.Infinite)
    (p q : Completed → Completed → Bool) (S : State × State)
    (hblue : RamseyGame.Outcome H
      (AdaptiveGame.game (fun U V ↦ p U V || q U V) S) true) :
    ∃ K ⊆ H, K.Infinite ∧
      (RamseyGame.Outcome K (AdaptiveGame.game p S) true ∨
        RamseyGame.Outcome K (AdaptiveGame.game q S) true) := by
  obtain ⟨I, hIH, hI, a, hp⟩ := RamseyGame.dichotomy (AdaptiveGame.game p S) H hH
  cases a with
  | true => exact ⟨I, hIH, hI, Or.inl hp⟩
  | false =>
    obtain ⟨K, hKI, hK, a, hq⟩ := RamseyGame.dichotomy (AdaptiveGame.game q S) I hI
    have hKH := hKI.trans hIH
    cases a with
    | true => exact ⟨K, hKH, hK, Or.inr hq⟩
    | false =>
      have hred := red_or p q S (hp.almost_mono (RamseyGame.almostSubset_of_subset hKI)) hq
      have hblueK := hblue.almost_mono (RamseyGame.almostSubset_of_subset hKH)
      exact (RamseyGame.Outcome.not_both hK _ hblueK hred).elim

def edgeClass (B : SimpleGraph G) (color : G → G → Bool)
    (hsym : ∀ s t, color s t = color t s) (value : Bool) : SimpleGraph G where
  Adj s t := B.Adj s t ∧ color s t = value
  symm := ⟨fun s t h ↦ ⟨h.1.symm, (hsym t s).trans h.2⟩⟩
  loopless := ⟨fun _ h ↦ B.ne_of_adj h.1 rfl⟩

theorem edgeClass_cliqueFree (B : SimpleGraph G) (color : G → G → Bool)
    (hsym : ∀ s t, color s t = color t s) (value : Bool) (n : ℕ)
    (hB : B.CliqueFree n) : (edgeClass B color hsym value).CliqueFree n := by
  intro s hs
  exact hB s ⟨fun _ hx _ hy hne ↦ (hs.1 hx hy hne).1, hs.2⟩

theorem payoff_edgeClass_or (B : SimpleGraph G) (color : G → G → Bool)
    (hsym : ∀ s t, color s t = color t s) (o : GraphPayoff.Orientation)
    (S T : Completed) :
    (GraphPayoff.payoff (edgeClass B color hsym false) o S T ||
      GraphPayoff.payoff (edgeClass B color hsym true) o S T) = GraphPayoff.payoff B o S T := by
  classical
  cases hc : color (GraphPayoff.vertex S) (GraphPayoff.vertex T) <;>
    simp [GraphPayoff.payoff, edgeClass, hc]

theorem blue_edgeClass {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph G) (color : G → G → Bool)
    (hsym : ∀ s t, color s t = color t s) (o : GraphPayoff.Orientation)
    (S : State × State) (hblue : RamseyGame.Outcome H (GraphPayoff.game B o S) true) :
    ∃ K ⊆ H, K.Infinite ∧ ∃ value : Bool,
      RamseyGame.Outcome K (GraphPayoff.game (edgeClass B color hsym value) o S) true := by
  have he : (fun U V ↦ GraphPayoff.payoff (edgeClass B color hsym false) o U V ||
      GraphPayoff.payoff (edgeClass B color hsym true) o U V) = GraphPayoff.payoff B o := by
    funext U V
    exact payoff_edgeClass_or B color hsym o U V
  have hb : RamseyGame.Outcome H (AdaptiveGame.game
      (fun U V ↦ GraphPayoff.payoff (edgeClass B color hsym false) o U V ||
        GraphPayoff.payoff (edgeClass B color hsym true) o U V) S) true := by
    rw [he]
    exact hblue
  obtain ⟨K, hKH, hK, h⟩ := blue_summand hH _ _ S hb
  rcases h with h | h
  · exact ⟨K, hKH, hK, false, h⟩
  · exact ⟨K, hKH, hK, true, h⟩

end Erdos118.EdgeRefinement
