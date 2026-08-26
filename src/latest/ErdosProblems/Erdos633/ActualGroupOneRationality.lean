import ErdosProblems.Erdos633.ExceptionalOuterSides
import ErdosProblems.Erdos633.NormalizedArea

/-!
# Rational parameters of actual group-one tilings

The character identities, area equations, and (for V) positive longest-edge
count are all derived from the geometric tiling. The resulting rational scale
is retained together with the exact area equation for the later square test.
-/

namespace Erdos633

theorem CongruentTiling.groupOne_U_rational_parameters_ordered
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 2 * R.angleB = Real.pi)
    (hA : P.angleA = R.angleA) (hB : P.angleB = 2 * R.angleA)
    (hC : P.angleC = 2 * R.angleB) :
    ∃ s L : ℝ, 0 < s ∧ s < 1 ∧ 0 < L ∧ s = 2 * Real.sin (R.angleA / 2) ∧
      R.normalizedSide 0 = s ∧ R.normalizedSide 1 = 1 - s ^ 2 ∧
      s ∈ rationalReals ∧ L ∈ rationalReals ∧
      (N : ℝ) = L ^ 2 * (2 - s ^ 2) * (3 - s ^ 2) := by
  have hind : IntegerIndependentAngles R.angleA R.angleB := by
    simpa [Triangle.cornerAngle] using R.independent_angles_of_not_commensurable
      (Equiv.refl _) hR 3 2 (by simpa [Triangle.cornerAngle] using hrel)
  obtain ⟨s, hs0, hs1, hs, hr0, hr1, _⟩ := R.groupOne_normalized_parameters hrel
  obtain ⟨L, hL, h0, h1, h2⟩ := P.groupOne_U_normalized_outer_sides R s hrel hs hA hB hC
  have hb : 0 < 1 - s ^ 2 := by rw [← hr1]; exact R.normalizedSide_pos 1
  have heq := T.normalized_area_equation_same_angle hA
  rw [h1, h2, hr1] at heq
  have harea : (N : ℝ) = L ^ 2 * (2 - s ^ 2) * (3 - s ^ 2) := by
    apply mul_right_cancel₀ (ne_of_gt hb)
    linear_combination -heq
  have hsign := T.normalized_integerBoundarySigns hind (3, 2) (2, 0) (0, 2)
    (by simpa [angleFromCoordinates] using hrel.symm)
    (by simpa [angleFromCoordinates] using hB)
    (by simpa [angleFromCoordinates] using hC)
  rw [hr0, hr1, h0, h1, h2] at hsign
  obtain ⟨hsrat, hLrat⟩ := groupOne_U_rational_of_boundary_signs s L hs0 hs1 hL hsign N harea
  exact ⟨s, L, hs0, hs1, hL, hs, hr0, hr1, hsrat, hLrat, harea⟩

theorem CongruentTiling.groupOne_V_rational_parameters_ordered
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 2 * R.angleB = Real.pi)
    (hA : P.angleA = 2 * R.angleA) (hB : P.angleB = R.angleB)
    (hC : P.angleC = R.angleA + R.angleB) :
    ∃ s L : ℝ, 0 < s ∧ s < 1 ∧ 0 < L ∧ s = 2 * Real.sin (R.angleA / 2) ∧
      R.normalizedSide 0 = s ∧ R.normalizedSide 1 = 1 - s ^ 2 ∧
      s ∈ rationalReals ∧ L ∈ rationalReals ∧ (N : ℝ) = L ^ 2 * (2 - s ^ 2) := by
  have hind : IntegerIndependentAngles R.angleA R.angleB := by
    simpa [Triangle.cornerAngle] using R.independent_angles_of_not_commensurable
      (Equiv.refl _) hR 3 2 (by simpa [Triangle.cornerAngle] using hrel)
  obtain ⟨s, hs0, hs1, hs, hr0, hr1, hcos⟩ := R.groupOne_normalized_parameters hrel
  obtain ⟨L, hL, h0, h1, h2⟩ := P.groupOne_V_normalized_outer_sides R s hrel hs hA hB hC
  have hb : 0 < 1 - s ^ 2 := by rw [← hr1]; exact R.normalizedSide_pos 1
  have heq := T.normalized_area_equation_double_angle hA
  rw [h1, h2, hcos, hr1] at heq
  have harea : (N : ℝ) = L ^ 2 * (2 - s ^ 2) := by
    apply mul_right_cancel₀ (ne_of_gt hb)
    linear_combination -heq
  have hsign := T.normalized_integerBoundarySigns hind (3, 2) (0, 1) (1, 1)
    (by simpa [angleFromCoordinates] using hrel.symm)
    (by simpa [angleFromCoordinates] using hB)
    (by simpa [angleFromCoordinates] using hC)
  rw [hr0, hr1, h0, h1, h2] at hsign
  have hshape : PermutedTriple P.cornerAngle
      ![2 * R.angleA, R.angleB, R.angleA + R.angleB] := by
    refine ⟨Equiv.refl _, ?_⟩
    intro j
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    · exact hA
    · exact hB
    · exact hC
  have hr := T.groupOne_V_boundarySideCount_pos 2 hrel hshape
  have hedge := T.side_div_reference_eq_three 2
  rw [h2, hr0, hr1] at hedge
  obtain ⟨hsrat, hLrat⟩ := groupOne_V_rational_of_boundary_signs s L hs0 hs1 hL hsign N harea
    (T.boundarySideCount 2 0) (T.boundarySideCount 2 1) (T.boundarySideCount 2 2) hr hedge
  exact ⟨s, L, hs0, hs1, hL, hs, hr0, hr1, hsrat, hLrat, harea⟩

theorem CongruentTiling.groupOne_U_commensurableSides_ordered
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 2 * R.angleB = Real.pi)
    (hA : P.angleA = R.angleA) (hB : P.angleB = 2 * R.angleA)
    (hC : P.angleC = 2 * R.angleB) : R.CommensurableSides := by
  obtain ⟨s, _, _, _, _, _, h0, h1, hs, _, _⟩ :=
    T.groupOne_U_rational_parameters_ordered hR hrel hA hB hC
  apply R.commensurableSides_of_first_two
  · rwa [h0]
  · rw [h1]
    exact rationalReals.sub_mem rationalReals.one_mem (rationalReals.pow_mem hs 2)

theorem CongruentTiling.groupOne_V_commensurableSides_ordered
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 2 * R.angleB = Real.pi)
    (hA : P.angleA = 2 * R.angleA) (hB : P.angleB = R.angleB)
    (hC : P.angleC = R.angleA + R.angleB) : R.CommensurableSides := by
  obtain ⟨s, _, _, _, _, _, h0, h1, hs, _, _⟩ :=
    T.groupOne_V_rational_parameters_ordered hR hrel hA hB hC
  apply R.commensurableSides_of_first_two
  · rwa [h0]
  · rw [h1]
    exact rationalReals.sub_mem rationalReals.one_mem (rationalReals.pow_mem hs 2)

theorem CongruentTiling.groupOne_U_commensurableSides
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 2 * R.angleB = Real.pi)
    (hshape : PermutedTriple P.cornerAngle ![R.angleA, 2 * R.angleA, 2 * R.angleB]) :
    R.CommensurableSides := by
  obtain ⟨e, he⟩ := hshape
  let Q := P.relabel e
  let U : CongruentTiling Q R N := T.of_carrier_eq (P.relabel_carrier e).symm
  have hA : Q.angleA = R.angleA := (P.cornerAngle_relabel e 0).trans (he 0)
  have hB : Q.angleB = 2 * R.angleA := (P.cornerAngle_relabel e 1).trans (he 1)
  have hC : Q.angleC = 2 * R.angleB := (P.cornerAngle_relabel e 2).trans (he 2)
  exact U.groupOne_U_commensurableSides_ordered hR hrel hA hB hC

theorem CongruentTiling.groupOne_V_commensurableSides
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 2 * R.angleB = Real.pi)
    (hshape : PermutedTriple P.cornerAngle
      ![2 * R.angleA, R.angleB, R.angleA + R.angleB]) : R.CommensurableSides := by
  obtain ⟨e, he⟩ := hshape
  let Q := P.relabel e
  let U : CongruentTiling Q R N := T.of_carrier_eq (P.relabel_carrier e).symm
  have hA : Q.angleA = 2 * R.angleA := (P.cornerAngle_relabel e 0).trans (he 0)
  have hB : Q.angleB = R.angleB := (P.cornerAngle_relabel e 1).trans (he 1)
  have hC : Q.angleC = R.angleA + R.angleB := (P.cornerAngle_relabel e 2).trans (he 2)
  exact U.groupOne_V_commensurableSides_ordered hR hrel hA hB hC

end Erdos633
