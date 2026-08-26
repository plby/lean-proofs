import ErdosProblems.Erdos118.AlignedSingletonEnding
import ErdosProblems.Erdos118.AlignedPositiveEnding

/-! Both actual aligned last-body endings exclude the equal-count
inside class. The strict-count inside class remains separate. -/

namespace Erdos118.AlignedExclusion

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates

theorem not_blue {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G) (hB : B.CliqueFree 3)
    (hfirst : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (FirstBodyRefinement.firstLabel S).length ≠ 1)
    (hlast : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (LastBodyRefinement.lastLabel S).length ≠ 1)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      InsideCounts.beforeLast S = InsideCounts.beforeLast T) :
    ¬ RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true := by
  intro hblue
  obtain ⟨K, _, hK, E, _, hE, hbE, value, he⟩ :=
    RightLastRefinement.exists_refined hH B hB hblue hfirst hlast hall
  have hf := fun S T hp ↦ (he S T hp).1
  have hl := fun S T hp ↦ (he S T hp).2.1
  have ha := fun S T hp ↦ (he S T hp).2.2.1
  have hs := fun S T hp ↦ (he S T hp).2.2.2
  obtain ⟨O⟩ := AlignedLastOpening.exists_opening hK E hE hbE hf ha hl
  obtain ⟨F, _, _⟩ := AlignedFirstBodies.exists_pair hK E O 0
  obtain ⟨D⟩ := AlignedBridgeDiagram.exists_diagram hK E ha hl O F
  obtain ⟨T, _, _⟩ := AlignedAllBodies.exists_t_pair hK E D 0
  obtain ⟨C⟩ := AlignedAllBodies.exists_u_certificates hK E ha value hs D T
  obtain ⟨U, _, _⟩ := AlignedAllBodies.exists_u_pair hK E C 0
  have htriangle : ∃ s t u : G, E.Adj s t ∧ E.Adj s u ∧ E.Adj t u := by
    by_cases hz : D.lowerCertificate.size = 0
    · exact AlignedSingletonEnding.triangle hK E C U hz
    · exact AlignedPositiveEnding.triangle hK E C U (Nat.pos_of_ne_zero hz)
  obtain ⟨s, t, u, hst, hsu, htu⟩ := htriangle
  exact hE {s, t, u} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hst, hsu, htu⟩)

theorem exists_strict {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true) :
    ∃ K ⊆ H, K.Infinite ∧ ∃ C : SimpleGraph G, C ≤ B ∧ C.CliqueFree 3 ∧
      RamseyGame.Outcome K (GraphPayoff.game C .inside (.initial, .initial)) true ∧
      ∀ S T : Completed, GraphPayoff.payoff C .inside S T = true →
        (FirstBodyRefinement.firstLabel S).length ≠ 1 ∧
        (LastBodyRefinement.lastLabel S).length ≠ 1 ∧
        LastMarkerRefinement.lastMarker S < LastMarkerRefinement.lastMarker T ∧
        InsideCounts.beforeLast S < InsideCounts.beforeLast T := by
  obtain ⟨K, hKH, hK, C, hCB, hC, hbC, value, hall⟩ :=
    TerminalCountRefinement.exists_alternative hH B hB hinit
  cases value with
  | false => exact ⟨K, hKH, hK, C, hCB, hC, hbC, hall⟩
  | true =>
    exact (not_blue hK C hC (fun S T hp ↦ (hall S T hp).1)
      (fun S T hp ↦ (hall S T hp).2.1) (fun S T hp ↦ (hall S T hp).2.2.2) hbC).elim

end Erdos118.AlignedExclusion
