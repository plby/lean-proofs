import Wikipedia.HopfProblem.DegreeCollapsePositiveMaximumReduction
import Wikipedia.HopfProblem.DegreeCollapsePositiveIndexOneElimination
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarInterior

/-!
# A minimal presentation has exactly one positive index-seven point

The actual collar produces a positive interior point. The original final
Morse window gives a positive global maximum of index seven. Two positive
index-seven points would give the constructed supported reduction, contrary
to minimal total count. This retains the already established absence of
positive indices zero and one, on the same original state and boundary.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization MorseCancellation
open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}

namespace ExcellentMorsePresentation

variable (P : S.ExcellentMorsePresentation)

theorem exists_positive_index_seven_point :
    ∃ p : criticalPoints (Vector 7) P.function,
      0 < P.function p ∧ nativeMorseIndex (Vector 7) P.function p = 7 ∧
      ∀ x : S.Space, P.function x ≤ P.function p := by
  let : SimplyConnectedSpace S.collar.positiveInterior :=
    S.collar.interiorHalfHomotopyEquiv.simplyConnectedSpace
  let x : S.collar.positiveInterior := Classical.choice inferInstance
  have hx : 0 < P.function x.val := (P.positive_iff x.val).mpr x.property
  obtain ⟨A⟩ := nonempty_surgeryWindows P.smooth P.morse P.distinct
  have hn := A.count_pos P.smooth
  have hindex := (nativeMorseIndex_eq_chart (A.data (A.last hn)).chart).trans
    (A.last_index_dimension P.smooth hn)
  refine ⟨A.last hn, hx.trans_le (A.last_globalMax P.smooth hn x.val), ?_,
    A.last_globalMax P.smooth hn⟩
  simpa only [finrank_euclideanSpace_fin] using hindex

theorem positive_index_seven_unique_of_minimal
    (hminimal : ∀ Q : S.ExcellentMorsePresentation,
      (criticalPoints (Vector 7) P.function).ncard ≤
        (criticalPoints (Vector 7) Q.function).ncard)
    (p q : criticalPoints (Vector 7) P.function) (hp : 0 < P.function p)
    (hq : 0 < P.function q) (hip : nativeMorseIndex (Vector 7) P.function p = 7)
    (hiq : nativeMorseIndex (Vector 7) P.function q = 7) : p = q := by
  by_contra hne
  obtain ⟨Q, hcount, _, _⟩ := P.exists_reduction_of_two_positive_maxima p q hp hq hip hiq hne
  have h := hminimal Q
  omega

theorem exists_unique_positive_maximum_of_minimal
    (hminimal : ∀ Q : S.ExcellentMorsePresentation,
      (criticalPoints (Vector 7) P.function).ncard ≤
        (criticalPoints (Vector 7) Q.function).ncard) :
    ∃ p : criticalPoints (Vector 7) P.function,
      0 < P.function p ∧ nativeMorseIndex (Vector 7) P.function p = 7 ∧
      (∀ x : S.Space, P.function x ≤ P.function p) ∧
      ∀ q : criticalPoints (Vector 7) P.function, 0 < P.function q →
        nativeMorseIndex (Vector 7) P.function q = 7 → q = p := by
  obtain ⟨p, hp, hip, hmax⟩ := P.exists_positive_index_seven_point
  exact ⟨p, hp, hip, hmax,
    fun q hq hiq => P.positive_index_seven_unique_of_minimal hminimal q p hq hp hiq hip⟩

end ExcellentMorsePresentation

theorem exists_minimal_positive_ordered_presentation_with_unique_maximum
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
        nativeMorseCount (Vector 7) P.function 1 + nativeMorseCount (Vector 7) P.function 6 ≤
          nativeMorseCount (Vector 7) Q.function 1 + nativeMorseCount (Vector 7) Q.function 6) ∧
      (∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
        2 ≤ nativeMorseIndex (Vector 7) P.function p) ∧
      ∃ p : criticalPoints (Vector 7) P.function,
        0 < P.function p ∧ nativeMorseIndex (Vector 7) P.function p = 7 ∧
        (∀ x : S.Space, P.function x ≤ P.function p) ∧
        ∀ q : criticalPoints (Vector 7) P.function, 0 < P.function q →
          nativeMorseIndex (Vector 7) P.function q = 7 → q = p := by
  obtain ⟨P, horder, hminimal, hcost, hlow⟩ :=
    S.exists_minimal_positive_ordered_presentation_without_low_indices eBoundary
  exact ⟨P, horder, hminimal, hcost, hlow, P.exists_unique_positive_maximum_of_minimal hminimal⟩

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
