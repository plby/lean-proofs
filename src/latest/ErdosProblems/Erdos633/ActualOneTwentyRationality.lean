import ErdosProblems.Erdos633.ActualWRationality
import ErdosProblems.Erdos633.ActualZRationality
import ErdosProblems.Erdos633.ExceptionalOuterSides
import ErdosProblems.Erdos633.NormalizedArea

/-!
# Rationality of actual Y and U₂ tilings

Together with W and Z this covers all four non-isosceles 120-degree patterns.
In particular, the area equations below are consequences of geometric area
additivity and the sine rule, not additional hypotheses of the tiling.
-/

namespace Erdos633

theorem CongruentTiling.oneTwenty_Y_commensurableSides_ordered
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (hA : P.angleA = R.angleA) (hB : P.angleB = 2 * R.angleB)
    (hC : P.angleC = 2 * R.angleA + R.angleB) : R.CommensurableSides := by
  have hind : IntegerIndependentAngles R.angleA R.angleB := by
    simpa [Triangle.cornerAngle] using R.independent_angles_of_not_commensurable
      (Equiv.refl _) hR 3 3 (by simpa [Triangle.cornerAngle] using hrel)
  obtain ⟨_, hc, _, _, _, _⟩ := R.oneTwenty_normalized_parameters hrel
  obtain ⟨L, hL, h0, h1, h2⟩ := P.oneTwenty_Y_normalized_outer_sides R hrel hA hB hC
  have heq := T.normalized_area_equation_same_angle hA
  rw [h1, h2] at heq
  have harea : (N : ℝ) = L ^ 2 * (R.normalizedSide 0 + R.normalizedSide 1) *
      (2 * R.normalizedSide 0 + R.normalizedSide 1) := by
    apply mul_right_cancel₀ (ne_of_gt (R.normalizedSide_pos 1))
    linear_combination -heq
  have hsign := T.normalized_integerBoundarySigns hind (3, 3) (0, 2) (2, 1)
    (by simpa [angleFromCoordinates] using hrel.symm)
    (by simpa [angleFromCoordinates] using hB)
    (by simpa [angleFromCoordinates] using hC)
  rw [h0, h1, h2] at hsign
  obtain ⟨ha, hb⟩ := oneTwenty_Y_rational_of_boundary_signs
    (R.normalizedSide 0) (R.normalizedSide 1) L
    (R.normalizedSide_pos 0) (R.normalizedSide_pos 1) hL hc hsign N harea
  exact R.commensurableSides_of_first_two ha hb

theorem CongruentTiling.oneTwenty_U_two_commensurableSides_ordered
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (hA : P.angleA = R.angleA) (hB : P.angleB = 2 * R.angleA)
    (hC : P.angleC = 3 * R.angleB) : R.CommensurableSides := by
  have hind : IntegerIndependentAngles R.angleA R.angleB := by
    simpa [Triangle.cornerAngle] using R.independent_angles_of_not_commensurable
      (Equiv.refl _) hR 3 3 (by simpa [Triangle.cornerAngle] using hrel)
  obtain ⟨_, hc, _, _, _, _⟩ := R.oneTwenty_normalized_parameters hrel
  obtain ⟨L, hL, h0, h1, h2⟩ := P.oneTwenty_U_two_normalized_outer_sides R hrel hA hB hC
  have heq := T.normalized_area_equation_same_angle hA
  rw [h1, h2] at heq
  have harea : (N : ℝ) = 3 * L ^ 2 * (R.normalizedSide 0 + R.normalizedSide 1) *
      (R.normalizedSide 0 + 2 * R.normalizedSide 1) := by
    apply mul_right_cancel₀ (ne_of_gt (R.normalizedSide_pos 1))
    linear_combination -heq
  have hsign := T.normalized_integerBoundarySigns hind (3, 3) (2, 0) (0, 3)
    (by simpa [angleFromCoordinates] using hrel.symm)
    (by simpa [angleFromCoordinates] using hB)
    (by simpa [angleFromCoordinates] using hC)
  rw [h0, h1, h2] at hsign
  obtain ⟨ha, hb⟩ := oneTwenty_U_two_rational_of_boundary_signs
    (R.normalizedSide 0) (R.normalizedSide 1) L
    (R.normalizedSide_pos 0) (R.normalizedSide_pos 1) hL hc hsign N harea
  exact R.commensurableSides_of_first_two ha hb

theorem CongruentTiling.oneTwenty_Y_commensurableSides
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (hshape : PermutedTriple P.cornerAngle
      ![R.angleA, 2 * R.angleB, 2 * R.angleA + R.angleB]) : R.CommensurableSides := by
  obtain ⟨e, he⟩ := hshape
  let Q := P.relabel e
  let U : CongruentTiling Q R N := T.of_carrier_eq (P.relabel_carrier e).symm
  have hA : Q.angleA = R.angleA := (P.cornerAngle_relabel e 0).trans (he 0)
  have hB : Q.angleB = 2 * R.angleB := (P.cornerAngle_relabel e 1).trans (he 1)
  have hC : Q.angleC = 2 * R.angleA + R.angleB := (P.cornerAngle_relabel e 2).trans (he 2)
  exact U.oneTwenty_Y_commensurableSides_ordered hR hrel hA hB hC

theorem CongruentTiling.oneTwenty_U_two_commensurableSides
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (hshape : PermutedTriple P.cornerAngle
      ![R.angleA, 2 * R.angleA, 3 * R.angleB]) : R.CommensurableSides := by
  obtain ⟨e, he⟩ := hshape
  let Q := P.relabel e
  let U : CongruentTiling Q R N := T.of_carrier_eq (P.relabel_carrier e).symm
  have hA : Q.angleA = R.angleA := (P.cornerAngle_relabel e 0).trans (he 0)
  have hB : Q.angleB = 2 * R.angleA := (P.cornerAngle_relabel e 1).trans (he 1)
  have hC : Q.angleC = 3 * R.angleB := (P.cornerAngle_relabel e 2).trans (he 2)
  exact U.oneTwenty_U_two_commensurableSides_ordered hR hrel hA hB hC

theorem CongruentTiling.oneTwenty_Y_necessary_angle_condition
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (hA : P.angleA = R.angleA) (hB : P.angleB = 2 * R.angleB)
    (hC : P.angleC = 2 * R.angleA + R.angleB) :
    P.angleC = 2 * P.angleA + P.angleB / 2 ∧
      Real.sqrt 3 * Real.tan (P.angleA / 2) ∈ rationalReals := by
  have hrat := T.oneTwenty_Y_commensurableSides_ordered hR hrel hA hB hC
  refine ⟨by linarith, ?_⟩
  rw [hA]
  exact R.oneTwenty_half_tangent_rational hrel hrat

theorem CongruentTiling.oneTwenty_U_two_necessary_angle_condition
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (hA : P.angleA = R.angleA) (hB : P.angleB = 2 * R.angleA)
    (hC : P.angleC = 3 * R.angleB) :
    P.angleB = 2 * P.angleA ∧ Real.sqrt 3 * Real.tan (P.angleA / 2) ∈ rationalReals := by
  have hrat := T.oneTwenty_U_two_commensurableSides_ordered hR hrel hA hB hC
  refine ⟨by linarith, ?_⟩
  rw [hA]
  exact R.oneTwenty_half_tangent_rational hrel hrat

end Erdos633
