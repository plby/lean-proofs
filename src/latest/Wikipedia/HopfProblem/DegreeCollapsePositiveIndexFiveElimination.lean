import Wikipedia.HopfProblem.DegreeCollapsePositiveFiveThreeTrade
import Wikipedia.HopfProblem.DegreeCollapsePositiveIndexTwoElimination

/-!
# Only positive middle handles and the unique maximum remain

The actual five-to-three trade strictly lowers the same secondary cost
used to eliminate indices one, two, and six. It therefore eliminates
index five without reintroducing any earlier index. A native collared
state whose original boundary is homeomorphic to the standard six-sphere
has a minimal ordered presentation with only indices three, four, and
the unique maximum. Middle cancellation is a separate remaining step.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization MorseCancellation SingularMayerVietoris

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}

theorem ExcellentMorsePresentation.no_positive_index_five_of_middle_cost_minimal
    [Subsingleton (SingularHomology B 2)] (P : S.ExcellentMorsePresentation)
    (horder : ∀ p q : criticalPoints (Vector 7) P.function,
      0 < P.function p → P.function p < P.function q →
        nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q)
    (hminimal : ∀ Q : S.ExcellentMorsePresentation,
      (criticalPoints (Vector 7) P.function).ncard ≤
        (criticalPoints (Vector 7) Q.function).ncard)
    (hcost : ∀ Q : S.ExcellentMorsePresentation,
      (criticalPoints (Vector 7) Q.function).ncard =
        (criticalPoints (Vector 7) P.function).ncard →
      middleHandleReductionCost (nativeMorseCount (Vector 7) P.function) ≤
        middleHandleReductionCost (nativeMorseCount (Vector 7) Q.function))
    (q : criticalPoints (Vector 7) P.function) (hq : 0 < P.function q) :
    nativeMorseIndex (Vector 7) P.function q ≠ 5 := by
  intro hi
  obtain ⟨Q, hcard, hfive, _, hother, _⟩ := P.exists_positive_five_to_three_handle_trade
    horder (P.positive_index_seven_unique_of_minimal hminimal)
    (P.no_positive_index_six_of_middle_cost_minimal horder hminimal hcost) q hq hi
  have hmin := hcost Q hcard
  dsimp only [middleHandleReductionCost] at hmin
  have hone := hother 1 (by decide) (by decide)
  have htwo := hother 2 (by decide) (by decide)
  have hsix := hother 6 (by decide) (by decide)
  omega

theorem exists_minimal_positive_presentation_with_indices_three_and_four
    (S : CollaredSevenState B) (eBoundary : B ≃ₜ Sphere 6) :
    ∃ P : S.ExcellentMorsePresentation,
      (∀ p q : criticalPoints (Vector 7) P.function,
        0 < P.function p → P.function p < P.function q →
          nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q) ∧
      (∀ Q : S.ExcellentMorsePresentation,
        (criticalPoints (Vector 7) P.function).ncard ≤
          (criticalPoints (Vector 7) Q.function).ncard) ∧
      (∀ Q : S.ExcellentMorsePresentation,
        (criticalPoints (Vector 7) Q.function).ncard =
          (criticalPoints (Vector 7) P.function).ncard →
        middleHandleReductionCost (nativeMorseCount (Vector 7) P.function) ≤
          middleHandleReductionCost (nativeMorseCount (Vector 7) Q.function)) ∧
      ∃ m : criticalPoints (Vector 7) P.function,
        0 < P.function m ∧ nativeMorseIndex (Vector 7) P.function m = 7 ∧
        (∀ x : S.Space, P.function x ≤ P.function m) ∧
        ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
          p = m ∨ nativeMorseIndex (Vector 7) P.function p = 3 ∨
            nativeMorseIndex (Vector 7) P.function p = 4 := by
  let : Subsingleton (SingularHomology (Sphere 6) 2) :=
    SphereHomology.unitSphere_homology_subsingleton 5 2 (by decide) (by decide)
  let : Subsingleton (SingularHomology B 2) :=
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
      eBoundary.toHomotopyEquiv 2).injective.subsingleton
  obtain ⟨P, horder, hminimal, hcost, m, hm, him, hmax, hmiddle⟩ :=
    S.exists_minimal_positive_presentation_with_indices_three_through_five eBoundary
  refine ⟨P, horder, hminimal, hcost, m, hm, him, hmax, ?_⟩
  intro p hp
  rcases hmiddle p hp with he | ⟨hlo, hhi⟩
  · exact Or.inl he
  · have hfive := P.no_positive_index_five_of_middle_cost_minimal horder hminimal hcost p hp
    exact Or.inr (by omega)

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
