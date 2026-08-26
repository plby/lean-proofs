import ErdosProblems.Erdos633.ExceptionalRealParameters

/-!
# Rationality of actual Z-family tilings

Both signed boundary equations and both nonnegative side-count equations are
derived from the tiling. Their opposite irrational coefficients force the
reference sides to be commensurable, without an assumed area formula.
-/

namespace Erdos633

theorem CongruentTiling.oneTwenty_Z_commensurableSides_ordered
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (hA : P.angleA = 2 * R.angleA) (hB : P.angleB = 2 * R.angleB)
    (hC : P.angleC = R.angleA + R.angleB) : R.CommensurableSides := by
  have hind : IntegerIndependentAngles R.angleA R.angleB := by
    simpa [Triangle.cornerAngle] using R.independent_angles_of_not_commensurable
      (Equiv.refl _) hR 3 3 (by simpa [Triangle.cornerAngle] using hrel)
  obtain ⟨_, hc, _, _, _, _⟩ := R.oneTwenty_normalized_parameters hrel
  have hab := R.oneTwenty_normalizedSides_ne_of_independent hrel hind
  obtain ⟨L, hL, h0, h1, h2⟩ := P.oneTwenty_Z_normalized_outer_sides R hrel hA hB hC
  have hsign := T.normalized_integerBoundarySigns hind (3, 3) (0, 2) (1, 1)
    (by simpa [angleFromCoordinates] using hrel.symm)
    (by simpa [angleFromCoordinates] using hB)
    (by simpa [angleFromCoordinates] using hC)
  rw [h0, h1, h2] at hsign
  have hx := T.side_div_reference_eq_three 0
  have hy := T.side_div_reference_eq_three 1
  rw [h0] at hx
  rw [h1] at hy
  obtain ⟨ha, hb⟩ := oneTwenty_Z_rational_of_boundary_signs
    (R.normalizedSide 0) (R.normalizedSide 1) L
    (R.normalizedSide_pos 0) (R.normalizedSide_pos 1) hL hab hc hsign
    (T.boundarySideCount 0 0) (T.boundarySideCount 0 1) (T.boundarySideCount 0 2)
    (T.boundarySideCount 1 0) (T.boundarySideCount 1 1) (T.boundarySideCount 1 2)
    (by simpa only [mul_assoc] using hx) (by simpa only [mul_assoc] using hy)
  exact R.commensurableSides_of_first_two ha hb

theorem CongruentTiling.oneTwenty_Z_commensurableSides
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (hshape : PermutedTriple P.cornerAngle
      ![2 * R.angleA, 2 * R.angleB, R.angleA + R.angleB]) : R.CommensurableSides := by
  obtain ⟨e, he⟩ := hshape
  let Q := P.relabel e
  let U : CongruentTiling Q R N := T.of_carrier_eq (P.relabel_carrier e).symm
  have hA : Q.angleA = 2 * R.angleA := (P.cornerAngle_relabel e 0).trans (he 0)
  have hB : Q.angleB = 2 * R.angleB := (P.cornerAngle_relabel e 1).trans (he 1)
  have hC : Q.angleC = R.angleA + R.angleB := (P.cornerAngle_relabel e 2).trans (he 2)
  exact U.oneTwenty_Z_commensurableSides_ordered hR hrel hA hB hC

theorem CongruentTiling.oneTwenty_Z_both_commensurableSides
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (hshape : PermutedTriple P.cornerAngle
      ![2 * R.angleA, 2 * R.angleB, R.angleA + R.angleB]) :
    R.CommensurableSides ∧ P.CommensurableSides := by
  have h := T.oneTwenty_Z_commensurableSides hR hrel hshape
  exact ⟨h, T.commensurableSides_of_reference h⟩

theorem CongruentTiling.oneTwenty_Z_necessary_angle_condition
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (hA : P.angleA = 2 * R.angleA) (hB : P.angleB = 2 * R.angleB)
    (hC : P.angleC = R.angleA + R.angleB) :
    P.angleC = Real.pi / 3 ∧ Real.sqrt 3 * Real.tan (P.angleA / 2) ∈ rationalReals := by
  have hrat := T.oneTwenty_Z_commensurableSides_ordered hR hrel hA hB hC
  refine ⟨by linarith, ?_⟩
  rw [hA, show 2 * R.angleA / 2 = R.angleA by ring]
  exact R.oneTwenty_tangent_rational hrel hrat

end Erdos633
