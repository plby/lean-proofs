import ErdosProblems.Erdos633.ExceptionalRealParameters

/-!
# Rationality of the actual W-family reference tile

The side parameters, character equations, and positive longest-edge count are
all extracted from the geometric tiling. No rationality, normalized-side
equation, area equation, or boundary-count equation is assumed.
-/

namespace Erdos633

theorem CongruentTiling.oneTwenty_W_commensurableSides_ordered
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (hA : P.angleA = R.angleA) (hB : P.angleB = R.angleA + R.angleB)
    (hC : P.angleC = R.angleA + 2 * R.angleB) : R.CommensurableSides := by
  have hind : IntegerIndependentAngles R.angleA R.angleB := by
    simpa [Triangle.cornerAngle] using R.independent_angles_of_not_commensurable
      (Equiv.refl _) hR 3 3 (by simpa [Triangle.cornerAngle] using hrel)
  obtain ⟨_, hc, _, _, _, _⟩ := R.oneTwenty_normalized_parameters hrel
  obtain ⟨L, hL, h0, h1, h2⟩ := P.oneTwenty_W_normalized_outer_sides R hrel hA hB hC
  have hsign := T.normalized_integerBoundarySigns hind (3, 3) (1, 1) (1, 2)
    (by simpa [angleFromCoordinates] using hrel.symm)
    (by simpa [angleFromCoordinates] using hB)
    (by simpa [angleFromCoordinates] using hC)
  rw [h0, h1, h2] at hsign
  have hshape : PermutedTriple P.cornerAngle
      ![R.angleA, R.angleA + R.angleB, R.angleA + 2 * R.angleB] := by
    refine ⟨Equiv.refl _, ?_⟩
    intro j
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl | rfl
    · exact hA
    · exact hB
    · exact hC
  have hr := T.oneTwenty_W_boundarySideCount_pos 0 hrel hshape
  have hedge := T.side_div_reference_eq_sum 0
  rw [h0] at hedge
  norm_num [Fin.sum_univ_succ] at hedge
  have hedge' : L * R.normalizedSide 0 =
      (T.boundarySideCount 0 0 : ℝ) * R.normalizedSide 0 +
      (T.boundarySideCount 0 1 : ℝ) * R.normalizedSide 1 + T.boundarySideCount 0 2 := by
    simpa only [← add_assoc] using hedge
  obtain ⟨ha, hb⟩ := oneTwenty_W_rational_of_boundary_signs
    (R.normalizedSide 0) (R.normalizedSide 1) L
    (R.normalizedSide_pos 0) (R.normalizedSide_pos 1) hL hc hsign
    (T.boundarySideCount 0 0) (T.boundarySideCount 0 1) (T.boundarySideCount 0 2) hr hedge'
  exact R.commensurableSides_of_first_two ha hb

theorem CongruentTiling.oneTwenty_W_commensurableSides
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (hshape : PermutedTriple P.cornerAngle
      ![R.angleA, R.angleA + R.angleB, R.angleA + 2 * R.angleB]) :
    R.CommensurableSides := by
  obtain ⟨e, he⟩ := hshape
  let Q := P.relabel e
  let U : CongruentTiling Q R N := T.of_carrier_eq (P.relabel_carrier e).symm
  have hA : Q.angleA = R.angleA := (P.cornerAngle_relabel e 0).trans (he 0)
  have hB : Q.angleB = R.angleA + R.angleB := (P.cornerAngle_relabel e 1).trans (he 1)
  have hC : Q.angleC = R.angleA + 2 * R.angleB := (P.cornerAngle_relabel e 2).trans (he 2)
  exact U.oneTwenty_W_commensurableSides_ordered hR hrel hA hB hC

theorem CongruentTiling.oneTwenty_W_both_commensurableSides
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (hshape : PermutedTriple P.cornerAngle
      ![R.angleA, R.angleA + R.angleB, R.angleA + 2 * R.angleB]) :
    R.CommensurableSides ∧ P.CommensurableSides := by
  have h := T.oneTwenty_W_commensurableSides hR hrel hshape
  exact ⟨h, T.commensurableSides_of_reference h⟩

theorem CongruentTiling.oneTwenty_W_necessary_angle_condition
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hR : ¬ R.CommensurableAngles)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (hA : P.angleA = R.angleA) (hB : P.angleB = R.angleA + R.angleB)
    (hC : P.angleC = R.angleA + 2 * R.angleB) :
    P.angleB = Real.pi / 3 ∧ Real.sqrt 3 * Real.tan (P.angleA / 2) ∈ rationalReals := by
  have hrat := T.oneTwenty_W_commensurableSides_ordered hR hrel hA hB hC
  refine ⟨by linarith, ?_⟩
  rw [hA]
  exact R.oneTwenty_half_tangent_rational hrel hrat

end Erdos633
