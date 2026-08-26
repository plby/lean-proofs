import ErdosProblems.Erdos118.FirstBodyRefinement
import ErdosProblems.Erdos118.LastMarkerRefinement

/-! Simultaneous first/last selected-label restrictions and uniform last-marker
order, with the actual initial blue certificate in the retained subgraph. -/

namespace Erdos118.EndpointRefinement

open Negative.Exact DecisionStates FirstBodyRefinement LastBodyRefinement LastMarkerRefinement

theorem exists_refined {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true) :
    ∃ K ⊆ H, K.Infinite ∧ ∃ C : SimpleGraph G, C ≤ B ∧ C.CliqueFree 3 ∧
      RamseyGame.Outcome K (GraphPayoff.game C .inside (.initial, .initial)) true ∧
      ∃ value : Bool, ∀ S T : Completed, GraphPayoff.payoff C .inside S T = true →
        (firstLabel S).length ≠ 1 ∧ (lastLabel S).length ≠ 1 ∧
          @decide (lastMarker T < lastMarker S) (Classical.propDecidable _) = value := by
  obtain ⟨I, hIH, hI, D, hDB, hD, hblueD, hfirst⟩ :=
    FirstBodyRefinement.exists_refined hH B hB hinit
  obtain ⟨K, hKI, hK, C, hCD, hC, hblueC, value, hlast⟩ :=
    LastMarkerRefinement.exists_refined hI D hD hblueD
  refine ⟨K, hKI.trans hIH, hK, C, hCD.trans hDB, hC, hblueC, value, ?_⟩
  intro S T hp
  exact ⟨hfirst S T (payoff_true_mono hCD .inside S T hp), hlast S T hp⟩

end Erdos118.EndpointRefinement
