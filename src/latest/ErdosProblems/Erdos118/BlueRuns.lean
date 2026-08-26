import ErdosProblems.Erdos118.SkippedCuts

/-!
Actual completion of blue certificates, and forced handoff at selected
leaves. These statements do not synchronize three pairwise games.
-/

namespace Erdos118.BlueRuns

open LabelledExtensions LabelledFrames DecisionStates AdaptiveGame

def LeftBlue (H : Set ℕ) (payoff : Completed → Completed → Bool) (S : State × State) : Prop :=
  ∃ n : ℕ, ∃ R : Response S.1 (pairBound S), allowedSide S false = true ∧
    responseFor S.1 (pairBound S) n = some R ∧
    ∃ b : ℕ, ∀ a : R.family.members, (↑a.1 : Set ℕ) ⊆ H → (∀ x ∈ a.1, b < x) →
      RamseyGame.Outcome H (AdaptiveGame.game payoff (R.result a, S.2)) true

def RightBlue (H : Set ℕ) (payoff : Completed → Completed → Bool) (S : State × State) : Prop :=
  ∃ n : ℕ, ∃ R : Response S.2 (pairBound S), allowedSide S true = true ∧
    responseFor S.2 (pairBound S) n = some R ∧
    ∃ b : ℕ, ∀ a : R.family.members, (↑a.1 : Set ℕ) ⊆ H → (∀ x ∈ a.1, b < x) →
      RamseyGame.Outcome H (AdaptiveGame.game payoff (S.1, R.result a)) true

theorem blue_command {H : Set ℕ} (payoff : Completed → Completed → Bool)
    (S : State × State) (hnone : terminalPayoff payoff S = none)
    (hblue : RamseyGame.Outcome H (AdaptiveGame.game payoff S) true) :
    LeftBlue H payoff S ∨ RightBlue H payoff S := by
  rw [AdaptiveGame.game_eq] at hblue
  simp only [build, hnone] at hblue
  cases hblue with
  | choiceTrue next n h =>
    by_cases heven : n % 2 = 0
    · by_cases hside : allowedSide S false = true
      · cases hR : responseFor S.1 (pairBound S) (n / 2) with
        | none =>
          simp only [heven, ↓reduceIte, hside, hR] at h
          cases h
        | some R =>
          simp only [heven, ↓reduceIte, hside, hR] at h
          cases h with
          | response F next b value hb => exact Or.inl ⟨n / 2, R, hside, hR, b, hb⟩
      · simp only [heven, ↓reduceIte, hside] at h
        cases h
    · by_cases hside : allowedSide S true = true
      · cases hR : responseFor S.2 (pairBound S) (n / 2) with
        | none =>
          simp only [heven, ↓reduceIte, hside, hR] at h
          cases h
        | some R =>
          simp only [heven, ↓reduceIte, hside, hR] at h
          cases h with
          | response F next b value hb => exact Or.inr ⟨n / 2, R, hside, hR, b, hb⟩
      · simp only [heven, ↓reduceIte, hside] at h
        cases h

theorem blue_completion {H : Set ℕ} (hH : H.Infinite)
    (payoff : Completed → Completed → Bool) (S : State × State)
    (hblue : RamseyGame.Outcome H (AdaptiveGame.game payoff S) true) :
    ∃ U V : Completed, ConservativeRuns.Run H payoff S (.complete U, .complete V) ∧
      payoff U V = true := by
  induction S using pairStep_wellFounded.induction with
  | h S ih =>
    by_cases hterm : ∃ U V : Completed, S = (.complete U, .complete V)
    · obtain ⟨U, V, rfl⟩ := hterm
      rw [AdaptiveGame.game_complete] at hblue
      exact ⟨U, V, Relation.ReflTransGen.refl, RamseyGame.outcome_leaf_iff.mp hblue⟩
    · have hnone : terminalPayoff payoff S = none := by
        obtain ⟨S, T⟩ := S
        cases S <;> cases T <;> simp_all [terminalPayoff]
      rcases blue_command payoff S hnone hblue with hleft | hright
      · obtain ⟨n, R, hs, hR, b, hb⟩ := hleft
        obtain ⟨a, haH, halarge⟩ := R.family.conservative_exists hH
          (max b (ConservativeRuns.leftGuard H payoff S n))
        have hab : ∀ x ∈ a.1, b < x := fun x hx ↦ (le_max_left _ _).trans_lt (halarge x hx)
        have hag : ∀ x ∈ a.1, ConservativeRuns.leftGuard H payoff S n < x :=
          fun x hx ↦ (le_max_right _ _).trans_lt (halarge x hx)
        obtain ⟨U, V, hrun, hpay⟩ := ih (R.result a, S.2) (PairStep.left S.2 (R.step a))
          (hb a haH hab)
        exact ⟨U, V, Relation.ReflTransGen.head
          (ConservativeRuns.Step.left S n R hs hR a haH hag) hrun, hpay⟩
      · obtain ⟨n, R, hs, hR, b, hb⟩ := hright
        obtain ⟨a, haH, halarge⟩ := R.family.conservative_exists hH
          (max b (ConservativeRuns.rightGuard H payoff S n))
        have hab : ∀ x ∈ a.1, b < x := fun x hx ↦ (le_max_left _ _).trans_lt (halarge x hx)
        have hag : ∀ x ∈ a.1, ConservativeRuns.rightGuard H payoff S n < x :=
          fun x hx ↦ (le_max_right _ _).trans_lt (halarge x hx)
        obtain ⟨U, V, hrun, hpay⟩ := ih (S.1, R.result a) (PairStep.right S.1 (R.step a))
          (hb a haH hab)
        exact ⟨U, V, Relation.ReflTransGen.head
          (ConservativeRuns.Step.right S n R hs hR a haH hag) hrun, hpay⟩

theorem consecutive_left_not_blue {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph Negative.Exact.G) (o : GraphPayoff.Orientation)
    (W : State × State) (R : Response W.1 (pairBound W)) (a : R.family.members)
    (P : Pending) (hP : R.result a = .leaf P)
    (Q : Response (.leaf P) (pairBound (.leaf P, W.2))) (b : Q.family.members) :
    ¬ RamseyGame.Outcome H (GraphPayoff.game B o (Q.result b, W.2)) true := by
  intro hblue
  obtain ⟨U, V, hrun, hpay⟩ := blue_completion hH (GraphPayoff.payoff B o) _ hblue
  exact SkippedCuts.consecutive_left_not_clear W R a P hP Q b U V hrun
    ((GraphPayoff.payoff_true_iff B o U V).mp hpay).2.1

theorem consecutive_right_not_blue {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph Negative.Exact.G) (o : GraphPayoff.Orientation)
    (W : State × State) (R : Response W.2 (pairBound W)) (a : R.family.members)
    (P : Pending) (hP : R.result a = .leaf P)
    (Q : Response (.leaf P) (pairBound (W.1, .leaf P))) (b : Q.family.members) :
    ¬ RamseyGame.Outcome H (GraphPayoff.game B o (W.1, Q.result b)) true := by
  intro hblue
  obtain ⟨U, V, hrun, hpay⟩ := blue_completion hH (GraphPayoff.payoff B o) _ hblue
  exact SkippedCuts.consecutive_right_not_clear W R a P hP Q b U V hrun
    ((GraphPayoff.payoff_true_iff B o U V).mp hpay).2.1

theorem handoff_after_left {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph Negative.Exact.G) (o : GraphPayoff.Orientation)
    (W : State × State) (R : Response W.1 (pairBound W)) (a : R.family.members)
    (P : Pending) (hP : R.result a = .leaf P)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf P, W.2)) true) :
    RightBlue H (GraphPayoff.payoff B o) (.leaf P, W.2) := by
  have hnone : terminalPayoff (GraphPayoff.payoff B o) (.leaf P, W.2) = none := by
    cases W.2 <;> rfl
  rcases blue_command (GraphPayoff.payoff B o) (.leaf P, W.2) hnone hblue with hleft | hright
  · obtain ⟨n, Q, _, _, b, hb⟩ := hleft
    obtain ⟨c, hcH, hcb⟩ := Q.family.conservative_exists hH b
    exact (consecutive_left_not_blue hH B o W R a P hP Q c (hb c hcH hcb)).elim
  · exact hright

theorem handoff_after_right {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph Negative.Exact.G) (o : GraphPayoff.Orientation)
    (W : State × State) (R : Response W.2 (pairBound W)) (a : R.family.members)
    (P : Pending) (hP : R.result a = .leaf P)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (W.1, .leaf P)) true) :
    LeftBlue H (GraphPayoff.payoff B o) (W.1, .leaf P) := by
  have hnone : terminalPayoff (GraphPayoff.payoff B o) (W.1, .leaf P) = none := by
    cases W.1 <;> rfl
  rcases blue_command (GraphPayoff.payoff B o) (W.1, .leaf P) hnone hblue with hleft | hright
  · exact hleft
  · obtain ⟨n, Q, _, _, b, hb⟩ := hright
    obtain ⟨c, hcH, hcb⟩ := Q.family.conservative_exists hH b
    exact (consecutive_right_not_blue hH B o W R a P hP Q c (hb c hcH hcb)).elim

theorem not_leftBlue_complete (H : Set ℕ) (payoff : Completed → Completed → Bool)
    (T : Completed) (S : State) : ¬ LeftBlue H payoff (.complete T, S) := by
  rintro ⟨n, R, _, hR, _⟩
  simp [responseFor] at hR

theorem not_rightBlue_complete (H : Set ℕ) (payoff : Completed → Completed → Bool)
    (S : State) (T : Completed) : ¬ RightBlue H payoff (S, .complete T) := by
  rintro ⟨n, R, _, hR, _⟩
  simp [responseFor] at hR

theorem body_response_pending (D : BodyDecision) {b : ℕ}
    (R : Response (.body D) b) (a : R.family.members) :
    ∃ P : Pending, R.result a = .leaf P := by
  have h : ∀ S : State, DecisionStates.Step S (.body D) → ∃ P : Pending, S = .leaf P := by
    intro S hS
    cases hS with
    | body D A => exact ⟨applyBody D A, rfl⟩
  exact h _ (R.step a)

theorem body_complete_not_blue {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph Negative.Exact.G) (o : GraphPayoff.Orientation)
    (D : BodyDecision) (T : Completed) :
    ¬ RamseyGame.Outcome H (GraphPayoff.game B o (.body D, .complete T)) true := by
  intro hblue
  rcases blue_command (GraphPayoff.payoff B o) (.body D, .complete T) rfl hblue with hl | hr
  · obtain ⟨n, R, _, _, b, hb⟩ := hl
    obtain ⟨a, haH, hab⟩ := R.family.conservative_exists hH b
    obtain ⟨P, hP⟩ := body_response_pending D R a
    have hnext := hb a haH hab
    rw [hP] at hnext
    exact not_rightBlue_complete H (GraphPayoff.payoff B o) (.leaf P) T
      (handoff_after_left hH B o (.body D, .complete T) R a P hP hnext)
  · exact not_rightBlue_complete H (GraphPayoff.payoff B o) (.body D) T hr

theorem complete_body_not_blue {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph Negative.Exact.G) (o : GraphPayoff.Orientation)
    (T : Completed) (D : BodyDecision) :
    ¬ RamseyGame.Outcome H (GraphPayoff.game B o (.complete T, .body D)) true := by
  intro hblue
  rcases blue_command (GraphPayoff.payoff B o) (.complete T, .body D) rfl hblue with hl | hr
  · exact not_leftBlue_complete H (GraphPayoff.payoff B o) T (.body D) hl
  · obtain ⟨n, R, _, _, b, hb⟩ := hr
    obtain ⟨a, haH, hab⟩ := R.family.conservative_exists hH b
    obtain ⟨P, hP⟩ := body_response_pending D R a
    have hnext := hb a haH hab
    rw [hP] at hnext
    exact not_leftBlue_complete H (GraphPayoff.payoff B o) T (.leaf P)
      (handoff_after_right hH B o (.complete T, .body D) R a P hP hnext)

theorem complete_initial_whole_blue {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph Negative.Exact.G) (o : GraphPayoff.Orientation) (T : Completed)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (.complete T, .initial)) true) :
    ∃ b : ℕ, ∀ a : (wholeResponse (pairBound (.complete T, .initial))).family.members,
      (↑a.1 : Set ℕ) ⊆ H → (∀ x ∈ a.1, b < x) →
      RamseyGame.Outcome H (GraphPayoff.game B o
        (.complete T, (wholeResponse (pairBound (.complete T, .initial))).result a)) true := by
  rcases blue_command (GraphPayoff.payoff B o) (.complete T, .initial) rfl hblue with hl | hr
  · exact (not_leftBlue_complete H (GraphPayoff.payoff B o) T .initial hl).elim
  · obtain ⟨n, R, _, hR, b, hb⟩ := hr
    cases n with
    | zero =>
      have he : R = wholeResponse (pairBound (.complete T, .initial)) := by
        exact Option.some.inj hR.symm
      subst R
      exact ⟨b, hb⟩
    | succ k =>
      have he : R = rootResponse k (pairBound (.complete T, .initial)) := by
        simpa only [responseFor, Option.some.injEq] using hR.symm
      subst R
      obtain ⟨a, haH, hab⟩ :=
        (rootResponse k (pairBound (.complete T, .initial))).family.conservative_exists hH b
      have hnext := hb a haH hab
      exact (complete_body_not_blue hH B o T _ hnext).elim

end Erdos118.BlueRuns
