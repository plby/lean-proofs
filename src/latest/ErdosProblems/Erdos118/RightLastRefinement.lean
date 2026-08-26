import ErdosProblems.Erdos118.TerminalCountRefinement

/-! Refine the right last-label singleton test, retaining the aligned
class and both left endpoint restrictions. Transfer the test to the
actual parameter of any right last-body response certificate. -/

namespace Erdos118.RightLastRefinement

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open LastBodyRefinement FirstBodyRefinement InsideCounts BlueRuns

theorem exists_refined {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true)
    (hfirst : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (firstLabel S).length ≠ 1)
    (hlast : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (lastLabel S).length ≠ 1)
    (halign : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S = beforeLast T) :
    ∃ K ⊆ H, K.Infinite ∧ ∃ C : SimpleGraph G, C ≤ B ∧ C.CliqueFree 3 ∧
      RamseyGame.Outcome K (GraphPayoff.game C .inside (.initial, .initial)) true ∧
      ∃ singleton : Bool, ∀ S T : Completed, GraphPayoff.payoff C .inside S T = true →
        (firstLabel S).length ≠ 1 ∧ (lastLabel S).length ≠ 1 ∧
        beforeLast S = beforeLast T ∧ ((lastLabel T).length = 1 ↔ singleton = true) := by
  obtain ⟨K, hKH, hK, C, hCB, hC, hbC, value, htest⟩ := IntrinsicAnnotations.refine_test
    hH B hB .inside hinit (fun _ T ↦ (lastLabel T).length = 1)
  refine ⟨K, hKH, hK, C, hCB, hC, hbC, value, ?_⟩
  intro S T hp
  have hpB := LastMarkerRefinement.payoff_true_mono hCB .inside S T hp
  refine ⟨hfirst S T hpB, hlast S T hpB, halign S T hpB, ?_⟩
  constructor
  · intro ht
    have he : @decide ((lastLabel T).length = 1) (Classical.propDecidable _) = true :=
      @decide_eq_true _ (Classical.propDecidable _) ht
    exact (htest S T hp).symm.trans he
  · intro hv
    exact @of_decide_eq_true _ (Classical.propDecidable _) ((htest S T hp).trans hv)

theorem right_certificate {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (singleton : Bool)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      ((lastLabel T).length = 1 ↔ singleton = true))
    (P : Pending) (D : BodyDecision) (hD : ExactSlots.Exact (.body D)) (hDR : D.roots = [])
    (t b : ℕ) (hcert : ∀ A : BodyResponses.Setup D.stem t,
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H) →
      (∀ x ∈ BodyResponses.newWord A.position, b < x) →
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf (applyBody D A))) true) :
    t = 0 ↔ singleton = true := by
  obtain ⟨A, hA⟩ := BodyResponses.setup_above D.stem t D.room hH b
  have hb := hcert A (fun x hx ↦ (hA x hx).1) (fun x hx ↦ (hA x hx).2)
  obtain ⟨S, T, hrun, hp⟩ := blue_completion hH (GraphPayoff.payoff B .inside)
    (.leaf P, .leaf (applyBody D A)) hb
  have hval := hall S T hp
  have hlabel := lastLabel_of_extension (applyBody D A) T
    (ExactSlots.step_exact (DecisionStates.Step.body D A) hD) hDR
    (SkippedCuts.run_extensions hrun).2.labels
  rw [hlabel] at hval
  change A.position.label.length = 1 ↔ singleton = true at hval
  rw [A.label_length] at hval
  have hn : t + 1 = 1 ↔ t = 0 := by omega
  exact hn.symm.trans hval

end Erdos118.RightLastRefinement
