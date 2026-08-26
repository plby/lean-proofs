import ErdosProblems.Erdos118.SingletonMiddleCompletion

/-! Exclusion of the uniform late-left-marker inside payoff class,
including both actual middle branches and their literal completions. -/

namespace Erdos118.LateMarkerExclusion

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates

theorem not_blue {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G) (hB : B.CliqueFree 3)
    (hfirst : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (FirstBodyRefinement.firstLabel S).length ≠ 1)
    (hlate : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      LastMarkerRefinement.lastMarker T < LastMarkerRefinement.lastMarker S)
    (hlast : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (LastBodyRefinement.lastLabel S).length ≠ 1) :
    ¬ RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true := by
  intro hblue
  obtain ⟨O⟩ := LateOpening.exists_opening hH B hB hblue hfirst hlate hlast
  obtain ⟨D⟩ := FirstMiddle.exists_diagram hH B O
  obtain ⟨R⟩ := SingletonMiddleRequest.exists_request hH B hB D
  obtain ⟨s, t, u, hst, hsu, htu⟩ := SingletonMiddleCompletion.triangle hH B D R
  exact hB {s, t, u} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hst, hsu, htu⟩)

end Erdos118.LateMarkerExclusion
