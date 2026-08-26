import ErdosProblems.Erdos118.FutureLastMarkers

/-!
In the uniform late-left-marker class, at a left last-body decision the
unchanged opposite pending word is in its last selected body but not its
last selected leaf. The same observation holds immediately before the
left word's only remaining body. Test responses do not change that word.
-/

namespace Erdos118.LateMarkerCritical

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open LastBodyRefinement LastMarkerRefinement BlueRuns

theorem remaining_leaves_label_gt_one (Q : Pending) (hne : Q.leaves ≠ []) :
    1 < Q.position.label.length := by
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil Q.leaves hne
  have hslot := Q.leafSlots.bounded j hj
  have hpos : 0 < Q.position.label.length :=
    List.length_pos_iff.mpr (List.ne_nil_of_mem Q.leafSelected)
  by_contra hn
  have hlen : Q.position.label.length = 1 := by omega
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
  have hold := Q.leafSelected
  have hnew := hslot.2.2
  rw [hx, List.mem_singleton] at hold hnew
  have hgt := hslot.1
  omega

theorem last_body_right_roots_nil {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hlate : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      lastMarker T < lastMarker S)
    (D : BodyDecision) (Q : Pending) (hD : ExactSlots.Exact (.body D)) (hDR : D.roots = [])
    (hblue : LeftBlue H (GraphPayoff.payoff B .inside) (.body D, .leaf Q)) : Q.roots = [] := by
  obtain ⟨m, A, _, hb, _, _⟩ :=
    PreparedRelays.respond_body hH B .inside false D (.leaf Q) hblue 0
  exact FutureLastMarkers.late_right_roots_nil hH B hlate (applyBody D A) Q
    (ExactSlots.step_exact (DecisionStates.Step.body D A) hD) hDR hb

theorem last_body_right_nonlast {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hlate : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      lastMarker T < lastMarker S)
    (hlabel : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (lastLabel S).length ≠ 1)
    (D : BodyDecision) (Q : Pending) (hD : ExactSlots.Exact (.body D)) (hDR : D.roots = [])
    (hblue : LeftBlue H (GraphPayoff.payoff B .inside) (.body D, .leaf Q)) :
    Q.roots = [] ∧ Q.leaves ≠ [] ∧ 1 < Q.position.label.length := by
  have hQR := last_body_right_roots_nil hH B hlate D Q hD hDR hblue
  have hQL : Q.leaves ≠ [] := by
    intro hQL
    obtain ⟨_, b, hb⟩ := InsideEndgame.last_right_body_setups hH B D Q hQR hQL hblue
    obtain ⟨A, hA⟩ := BodyResponses.setup_above D.stem 0 D.room hH b
    have hc := hb A (fun x hx ↦ (hA x hx).1) (fun x hx ↦ (hA x hx).2)
    have hne := pending_label_not_singleton hH B hlabel (applyBody D A) (.leaf Q)
      (ExactSlots.step_exact (DecisionStates.Step.body D A) hD) hDR hc
    exact hne A.label_length
  exact ⟨hQR, hQL, remaining_leaves_label_gt_one Q hQL⟩

theorem before_last_body_right_nonlast {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hlate : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      lastMarker T < lastMarker S)
    (hlabel : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (lastLabel S).length ≠ 1)
    (P Q : Pending) (c : ℕ) (hP : ExactSlots.Exact (.leaf P))
    (hPR : P.roots = [c]) (hPL : P.leaves = [])
    (hblue : LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf Q)) :
    Q.roots = [] ∧ Q.leaves ≠ [] ∧ 1 < Q.position.label.length := by
  obtain ⟨R, a, _, hb, _⟩ :=
    PreparedRelays.respond hH B .inside false (.leaf P) (.leaf Q) hblue 0
  change RamseyGame.Outcome H (GraphPayoff.game B .inside (R.result a, .leaf Q)) true at hb
  have hstep := R.step a
  generalize he : R.result a = V at hstep hb
  cases hstep with
  | leaf F j rest hF A => simp [hPL] at hF
  | nextBody F d rest hR hL A =>
    have he : d = c ∧ rest = [] := by simpa only [hPR, List.cons.injEq] using hR.symm
    have hD := ExactSlots.step_exact (DecisionStates.Step.nextBody P d rest hR hL A) hP
    have hDR : (ofStem P d rest hR A).roots = [] := he.2
    have hleft : LeftBlue H (GraphPayoff.payoff B .inside)
        (.body (ofStem P d rest hR A), .leaf Q) := by
      rcases blue_command (GraphPayoff.payoff B .inside)
          (.body (ofStem P d rest hR A), .leaf Q) rfl hb with hl | hr
      · exact hl
      · obtain ⟨n, R', hs, _⟩ := hr
        simp [allowedSide] at hs
    exact last_body_right_nonlast hH B hlate hlabel _ Q hD hDR hleft
  | finish F hR hL A => simp [hPR] at hR

end Erdos118.LateMarkerCritical
