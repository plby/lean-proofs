import ErdosProblems.Erdos118.PreparedRelays

/-!
In the outside game, a last right leaf cannot finish before an unfinished
left word. A left handoff at that boundary therefore forces a final left
completion command. These statements do not assume triangle-freeness.
-/

namespace Erdos118.OutsideEndgame

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns

theorem last_right_not_rightBlue {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (S : State) (Q : Pending) (hR : Q.roots = []) (hL : Q.leaves = [])
    (hS : ¬ ∃ C : Completed, S = .complete C) :
    ¬ RightBlue H (GraphPayoff.payoff B .outside) (S, .leaf Q) := by
  intro hblue
  obtain ⟨n, R, _, hresp, b, hb⟩ := hblue
  let c := pairBound (S, .leaf Q)
  have he : R = finishResponse Q hR hL c :=
    Option.some.inj (hresp.symm.trans (SecondWhole.finish_selector Q hR hL c n))
  subst R
  obtain ⟨a, haH, hab⟩ := (finishResponse Q hR hL c).family.conservative_exists hH b
  exact EndpointOrder.outside_incomplete_complete_not_blue hH B S _ hS (hb a haH hab)

theorem body_last_not_blue {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (D : BodyDecision) (Q : Pending) (hR : Q.roots = []) (hL : Q.leaves = []) :
    ¬ RamseyGame.Outcome H (GraphPayoff.game B .outside (.body D, .leaf Q)) true := by
  intro hblue
  rcases blue_command (GraphPayoff.payoff B .outside) (.body D, .leaf Q) rfl hblue with hl | hr
  · obtain ⟨k, A, _, _, hh, _⟩ :=
      PreparedRelays.respond_body hH B .outside false D (.leaf Q) hl 0
    exact last_right_not_rightBlue hH B (.leaf (applyBody D A)) Q hR hL
      (by simp) hh
  · exact last_right_not_rightBlue hH B (.body D) Q hR hL (by simp) hr

theorem last_right_left_command {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (S : State) (Q : Pending) (hR : Q.roots = []) (hL : Q.leaves = [])
    (hS : S ≠ .initial)
    (hblue : LeftBlue H (GraphPayoff.payoff B .outside) (S, .leaf Q)) :
    ∃ P : Pending, S = .leaf P ∧ P.roots = [] ∧ P.leaves = [] := by
  cases S with
  | initial => exact (hS rfl).elim
  | complete C => exact (not_leftBlue_complete H (GraphPayoff.payoff B .outside) C
      (.leaf Q) hblue).elim
  | body D =>
    obtain ⟨k, A, _, _, hh, _⟩ :=
      PreparedRelays.respond_body hH B .outside false D (.leaf Q) hblue 0
    exact (last_right_not_rightBlue hH B (.leaf (applyBody D A)) Q hR hL
      (by simp) hh).elim
  | leaf P =>
    obtain ⟨n, R, _, _, b, hb⟩ := hblue
    obtain ⟨a, haH, hab⟩ := R.family.conservative_exists hH b
    have hnext := hb a haH hab
    rcases EndpointOrder.leaf_step_cases P (R.result a) (R.step a) with
      ⟨U, hU⟩ | ⟨D, hD⟩ | hlast
    · rw [hU] at hnext
      have hh := handoff_after_left hH B .outside (.leaf P, .leaf Q) R a U hU hnext
      exact (last_right_not_rightBlue hH B (.leaf U) Q hR hL (by simp) hh).elim
    · rw [hD] at hnext
      exact (body_last_not_blue hH B D Q hR hL hnext).elim
    · exact ⟨P, rfl, hlast⟩

theorem last_right_leftBlue {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (P Q : Pending) (hR : Q.roots = []) (hL : Q.leaves = [])
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .outside (.leaf P, .leaf Q)) true) :
    LeftBlue H (GraphPayoff.payoff B .outside) (.leaf P, .leaf Q) := by
  rcases blue_command (GraphPayoff.payoff B .outside) (.leaf P, .leaf Q) rfl hblue with hl | hr
  · exact hl
  · exact (last_right_not_rightBlue hH B (.leaf P) Q hR hL (by simp) hr).elim

end Erdos118.OutsideEndgame
