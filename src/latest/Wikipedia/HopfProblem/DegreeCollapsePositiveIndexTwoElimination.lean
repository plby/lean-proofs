import Wikipedia.HopfProblem.DegreeCollapsePositiveTwoFourTrade
import Wikipedia.HopfProblem.DegreeCollapsePositiveIndexSixElimination

/-!
# Eliminate every positive index-two handle while retaining the outer-index elimination

Among presentations with minimal total critical count, minimize the sum
of counts in indices one, two, five, and six. The actual one-to-three,
two-to-four, and six-to-four trades each strictly lower this same cost.
The original boundary supplies simple connectivity and second-homology
vanishing. Only indices three through five and the unique maximum remain.
The dual five-to-three trade and middle cancellation remain separate.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization MorseCancellation SingularMayerVietoris

def middleHandleReductionCost (c : ℕ → ℕ) : ℕ := c 1 + c 2 + c 5 + c 6

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}

namespace ExcellentMorsePresentation

theorem no_positive_index_one_of_middle_cost_minimal [PathConnectedSpace B]
    (P : S.ExcellentMorsePresentation)
    (horder : ∀ p q : criticalPoints (Vector 7) P.function,
      0 < P.function p → P.function p < P.function q →
        nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q)
    (hnobirth : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
      nativeMorseIndex (Vector 7) P.function p ≠ 0)
    (hcost : ∀ Q : S.ExcellentMorsePresentation,
      (criticalPoints (Vector 7) Q.function).ncard =
        (criticalPoints (Vector 7) P.function).ncard →
      middleHandleReductionCost (nativeMorseCount (Vector 7) P.function) ≤
        middleHandleReductionCost (nativeMorseCount (Vector 7) Q.function))
    (q : criticalPoints (Vector 7) P.function) (hq : 0 < P.function q) :
    nativeMorseIndex (Vector 7) P.function q ≠ 1 := by
  intro hi
  obtain ⟨Q, hcard, hone, _, hother, _⟩ :=
    P.exists_positive_one_to_three_handle_trade horder hnobirth q hq hi
  have hmin := hcost Q hcard
  dsimp only [middleHandleReductionCost] at hmin
  have htwo := hother 2 (by decide) (by decide)
  have hfive := hother 5 (by decide) (by decide)
  have hsix := hother 6 (by decide) (by decide)
  omega

theorem no_positive_index_six_of_middle_cost_minimal
    (P : S.ExcellentMorsePresentation)
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
    nativeMorseIndex (Vector 7) P.function q ≠ 6 := by
  intro hi
  obtain ⟨Q, hcard, hsix, _, hother, _⟩ := P.exists_positive_six_to_four_handle_trade
    horder (P.positive_index_seven_unique_of_minimal hminimal) q hq hi
  have hmin := hcost Q hcard
  dsimp only [middleHandleReductionCost] at hmin
  have hone := hother 1 (by decide) (by decide)
  have htwo := hother 2 (by decide) (by decide)
  have hfive := hother 5 (by decide) (by decide)
  omega

theorem no_positive_index_two_of_middle_cost_minimal [SimplyConnectedSpace B]
    [Subsingleton (SingularHomology B 2)]
    (P : S.ExcellentMorsePresentation)
    (horder : ∀ p q : criticalPoints (Vector 7) P.function,
      0 < P.function p → P.function p < P.function q →
        nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q)
    (hlower : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
      2 ≤ nativeMorseIndex (Vector 7) P.function p)
    (hcost : ∀ Q : S.ExcellentMorsePresentation,
      (criticalPoints (Vector 7) Q.function).ncard =
        (criticalPoints (Vector 7) P.function).ncard →
      middleHandleReductionCost (nativeMorseCount (Vector 7) P.function) ≤
        middleHandleReductionCost (nativeMorseCount (Vector 7) Q.function))
    (q : criticalPoints (Vector 7) P.function) (hq : 0 < P.function q) :
    nativeMorseIndex (Vector 7) P.function q ≠ 2 := by
  intro hi
  obtain ⟨Q, hcard, htwo, _, hother, _⟩ :=
    P.exists_positive_two_to_four_handle_trade horder hlower q hq hi
  have hmin := hcost Q hcard
  dsimp only [middleHandleReductionCost] at hmin
  have hone := hother 1 (by decide) (by decide)
  have hfive := hother 5 (by decide) (by decide)
  have hsix := hother 6 (by decide) (by decide)
  omega

end ExcellentMorsePresentation

theorem exists_minimal_positive_presentation_with_indices_three_through_five
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
          p = m ∨ (3 ≤ nativeMorseIndex (Vector 7) P.function p ∧
            nativeMorseIndex (Vector 7) P.function p ≤ 5) := by
  let : SimplyConnectedSpace B := eBoundary.toHomotopyEquiv.simplyConnectedSpace
  let : Subsingleton (SingularHomology (Sphere 6) 2) :=
    SphereHomology.unitSphere_homology_subsingleton 5 2 (by decide) (by decide)
  let : Subsingleton (SingularHomology B 2) :=
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
      eBoundary.toHomotopyEquiv 2).injective.subsingleton
  obtain ⟨P, horder, hminimal, hcost⟩ :=
    S.exists_count_cost_minimal_positive_ordered_presentation middleHandleReductionCost
  have hzero := P.no_positive_index_zero_of_minimal eBoundary hminimal
  have hone := P.no_positive_index_one_of_middle_cost_minimal horder hzero hcost
  have hlow (p : criticalPoints (Vector 7) P.function) (hp : 0 < P.function p) :
      2 ≤ nativeMorseIndex (Vector 7) P.function p := by
    have h0 := hzero p hp
    have h1 := hone p hp
    omega
  obtain ⟨m, hm, him, hmax, hunique⟩ := P.exists_unique_positive_maximum_of_minimal hminimal
  refine ⟨P, horder, hminimal, hcost, m, hm, him, hmax, ?_⟩
  intro p hp
  by_cases he : p = m
  · exact Or.inl he
  · have h2 := P.no_positive_index_two_of_middle_cost_minimal horder hlow hcost p hp
    have h6 := P.no_positive_index_six_of_middle_cost_minimal horder hminimal hcost p hp
    have h7 : nativeMorseIndex (Vector 7) P.function p ≠ 7 :=
      fun hi => he (hunique p hp hi)
    have hb := nativeMorseIndex_le (E := Vector 7) (f := P.function) (p := p.val)
    have hl := hlow p hp
    simp only [GLOrthonormalization.Vector, finrank_euclideanSpace_fin] at hb h2 h6 h7 hl ⊢
    exact Or.inr ⟨by omega, by omega⟩

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
