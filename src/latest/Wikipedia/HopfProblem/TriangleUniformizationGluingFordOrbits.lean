import Wikipedia.HopfProblem.TriangleUniformizationGluingClosedCut
import Wikipedia.HopfProblem.TriangleUniformizationGluingClosedPointOrbits
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientBasic

/-!
# The actual boundary identifications of the closed Ford polygon

The closed reduced-word classification is transferred back from the
circular double.  The two Ford representatives of any orbit are equal
or are exchanged by the vertical reflection on the boundary.  The
converse follows from the explicit circular and cusp side pairings.
Neither direction is a supplied fundamental-domain hypothesis.
-/

noncomputable section

open Set UpperHalfPlane
open scoped MatrixGroups Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

private def circularHalfPoint (z : ℍ) : ℍ := by
  classical
  exact if 1 ≤ ‖(z : ℂ) + 1‖ then z else circleReflection z

private theorem circularHalfPoint_of_half {z : ℍ} (hz : z ∈ halfFordRegion) :
    circularHalfPoint z = z := by
  simp only [circularHalfPoint, if_pos hz.1.2.2.1]

private theorem circularHalfPoint_circle_of_half {z : ℍ} (hz : z ∈ halfFordRegion) :
    circularHalfPoint (circleReflection z) = z := by
  by_cases hn : 1 ≤ ‖(circleReflection z : ℂ) + 1‖
  · rw [circularHalfPoint, if_pos hn]
    apply circleReflection_eq_self_of_halfFordRegion_mem z hz
    exact (circularDoubleRegion_and_norm_add_one_iff_halfFordRegion _).mp
      ⟨circleReflection_mapsTo_circularDoubleRegion
        (halfFordRegion_subset_circularDoubleRegion hz), hn⟩
  · rw [circularHalfPoint, if_neg hn, circleReflection_involutive z]

private theorem circularHalfPoint_circle {z : ℍ} (hz : z ∈ circularDoubleRegion) :
    circularHalfPoint (circleReflection z) = circularHalfPoint z := by
  rw [circularDoubleRegion_eq_halfFordRegion_union_circle] at hz
  rcases hz with hz | ⟨w, hw, rfl⟩
  · rw [circularHalfPoint_circle_of_half hz, circularHalfPoint_of_half hz]
  · rw [circleReflection_involutive w, circularHalfPoint_of_half hw,
      circularHalfPoint_circle_of_half hw]

private def fordHalfPoint (z : ℍ) : ℍ := by
  classical
  exact if z.re ≤ -(1 / 2) then z else rightReflection z

private theorem fordHalfPoint_mem {z : ℍ} (hz : z ∈ fordRegion) :
    fordHalfPoint z ∈ halfFordRegion := by
  by_cases hx : z.re ≤ -(1 / 2)
  · rw [fordHalfPoint, if_pos hx]
    exact ⟨hz, hx⟩
  · rw [fordHalfPoint, if_neg hx]
    refine ⟨rightReflection_mapsTo_fordRegion hz, ?_⟩
    change (rightReflection z).re ≤ -(1 / 2)
    rw [rightReflection_re]
    have hh := lt_of_not_ge hx
    linarith

private theorem eq_or_reflection_of_fordHalfPoint_eq {z w : ℍ}
    (h : fordHalfPoint w = fordHalfPoint z) : w = z ∨ w = rightReflection z := by
  by_cases hz : z.re ≤ -(1 / 2) <;> by_cases hw : w.re ≤ -(1 / 2)
  · left
    simpa only [fordHalfPoint, if_pos hz, if_pos hw] using h
  · right
    have hh : rightReflection w = z := by
      simpa only [fordHalfPoint, if_pos hz, if_neg hw] using h
    have he := congrArg rightReflection hh
    simpa only [rightReflection_involutive w] using he
  · right
    simpa only [fordHalfPoint, if_neg hz, if_pos hw] using h
  · left
    apply rightReflection.injective
    simpa only [fordHalfPoint, if_neg hz, if_neg hw] using h

private def fordCircularNormalizer (z : ℍ) : TriangleGroup := by
  classical
  exact if z.re ≤ -(1 / 2) then 1 else triangleGenerator₁⁻¹

private def fordCircularPoint (z : ℍ) : ℍ :=
  triangleGeometricRepresentation (fordCircularNormalizer z) z

private theorem generatorOne_inv_representation_apply (z : ℍ) :
    triangleGeometricRepresentation triangleGenerator₁⁻¹ z = generatorOneSL⁻¹ • z := by
  rw [map_inv, triangleGeometricRepresentation_generator₁]
  change (realSLPermutation generatorOneSL)⁻¹ z = _
  rw [← map_inv]
  rfl

private theorem fordCircularPoint_of_left {z : ℍ} (hz : z.re ≤ -(1 / 2)) :
    fordCircularPoint z = z := by
  rw [fordCircularPoint, fordCircularNormalizer, if_pos hz, map_one]
  rfl

private theorem fordCircularPoint_of_right {z : ℍ} (hz : ¬z.re ≤ -(1 / 2)) :
    fordCircularPoint z = circleReflection (rightReflection z) := by
  rw [fordCircularPoint, fordCircularNormalizer, if_neg hz,
    generatorOne_inv_representation_apply, generatorOne_inv_reflections]

private theorem fordCircularPoint_mem {z : ℍ} (hz : z ∈ fordRegion) :
    fordCircularPoint z ∈ circularDoubleRegion := by
  by_cases hx : z.re ≤ -(1 / 2)
  · rw [fordCircularPoint_of_left hx]
    exact fordRegion_left_mem_circularDoubleRegion z hz hx
  · rw [fordCircularPoint_of_right hx]
    apply circleReflection_mapsTo_circularDoubleRegion
    have hh := fordHalfPoint_mem hz
    rw [fordHalfPoint, if_neg hx] at hh
    exact halfFordRegion_subset_circularDoubleRegion hh

private theorem circularHalfPoint_fordCircularPoint {z : ℍ} (hz : z ∈ fordRegion) :
    circularHalfPoint (fordCircularPoint z) = fordHalfPoint z := by
  by_cases hx : z.re ≤ -(1 / 2)
  · rw [fordCircularPoint_of_left hx, fordHalfPoint, if_pos hx]
    exact circularHalfPoint_of_half ⟨hz, hx⟩
  · rw [fordCircularPoint_of_right hx, fordHalfPoint, if_neg hx]
    apply circularHalfPoint_circle_of_half
    have hh := fordHalfPoint_mem hz
    simpa only [fordHalfPoint, if_neg hx] using hh

private theorem fordHalfPoint_eq_of_orbit (g : TriangleGroup) {z w : ℍ}
    (hz : z ∈ fordRegion) (hw : w ∈ fordRegion)
    (hzw : triangleGeometricRepresentation g z = w) : fordHalfPoint w = fordHalfPoint z := by
  let h : TriangleGroup := fordCircularNormalizer w * g * (fordCircularNormalizer z)⁻¹
  have he : triangleGeometricRepresentation h (fordCircularPoint z) = fordCircularPoint w := by
    dsimp only [h, fordCircularPoint]
    rw [map_mul, map_mul, map_inv]
    change triangleGeometricRepresentation (fordCircularNormalizer w)
      (triangleGeometricRepresentation g
        ((triangleGeometricRepresentation (fordCircularNormalizer z)).symm
          (triangleGeometricRepresentation (fordCircularNormalizer z) z))) = _
    rw [(triangleGeometricRepresentation (fordCircularNormalizer z)).symm_apply_apply z, hzw]
  have hor := circularDoubleRegion_orbit_point_of_eq h
    (fordCircularPoint_mem hz) (fordCircularPoint_mem hw) he
  have hh : circularHalfPoint (fordCircularPoint w) =
      circularHalfPoint (fordCircularPoint z) := by
    rcases hor with hor | hor
    · exact congrArg circularHalfPoint hor
    · rw [hor, circularHalfPoint_circle (fordCircularPoint_mem hz)]
  rwa [circularHalfPoint_fordCircularPoint hw, circularHalfPoint_fordCircularPoint hz] at hh

/-- Any two actual closed Ford representatives of the same orbit are
equal or exchanged by the vertical reflection. -/
theorem fordRegion_orbit_point_of_eq (g : TriangleGroup) {z w : ℍ}
    (hz : z ∈ fordRegion) (hw : w ∈ fordRegion)
    (hzw : triangleGeometricRepresentation g z = w) :
    w = z ∨ (w = rightReflection z ∧ z ∉ fordInterior) := by
  rcases eq_or_reflection_of_fordHalfPoint_eq (fordHalfPoint_eq_of_orbit g hz hw hzw)
      with he | he
  · exact Or.inl he
  · by_cases hwz : w = z
    · exact Or.inl hwz
    · refine Or.inr ⟨he, ?_⟩
      intro hi
      have hwi : w ∈ fordInterior := he ▸ rightReflection_mapsTo_fordInterior hi
      have hg := eq_one_of_fordInterior_eq g hi hwi hzw
      apply hwz
      rw [hg, map_one] at hzw
      exact hzw.symm

theorem fordRegion_orbit_point (g : TriangleGroup) {z : ℍ} (hz : z ∈ fordRegion)
    (hgz : triangleGeometricRepresentation g z ∈ fordRegion) :
    triangleGeometricRepresentation g z = z ∨
      (triangleGeometricRepresentation g z = rightReflection z ∧ z ∉ fordInterior) :=
  fordRegion_orbit_point_of_eq g hz hgz rfl

/-- Every boundary point of the closed polygon lies on one of its four
actual paired sides, including the common vertices. -/
theorem fordRegion_boundary_cases {z : ℍ} (hz : z ∈ fordRegion) (hi : z ∉ fordInterior) :
    z.re = stripLeft ∨ z.re = stripRight ∨
      ‖(z : ℂ) + 1‖ = 1 ∨ ‖(z : ℂ)‖ = 1 := by
  by_cases hl : stripLeft < z.re
  · by_cases hr : z.re < stripRight
    · by_cases hc : 1 < ‖(z : ℂ) + 1‖
      · right; right; right
        apply le_antisymm _ hz.2.2.2
        apply le_of_not_gt
        intro hn
        exact hi ⟨hl, hr, hc, hn⟩
      · exact Or.inr (Or.inr (Or.inl (le_antisymm (le_of_not_gt hc) hz.2.2.1)))
    · exact Or.inr (Or.inl (le_antisymm hz.2.1 (le_of_not_gt hr)))
  · exact Or.inl (le_antisymm (le_of_not_gt hl) hz.1)

private theorem orbitProjection_rightReflection_of_right_side {z : ℍ}
    (hz : z.re = stripRight) :
    triangleOrbitProjection (rightReflection z) = triangleOrbitProjection z := by
  have h := triangleOrbitProjection_smul triangleCuspGenerator z
  rw [triangleGeometricRepresentation_cusp] at h
  change triangleOrbitProjection (cuspSL • z) = triangleOrbitProjection z at h
  rwa [cusp_eq_rightReflection_of_re_eq_stripRight z hz] at h

/-- The reflected boundary representatives are identified by the actual
elliptic or cusp side pairing, not by an added equivalence relation. -/
theorem orbitProjection_rightReflection_boundary {z : ℍ}
    (hz : z ∈ fordRegion) (hi : z ∉ fordInterior) :
    triangleOrbitProjection (rightReflection z) = triangleOrbitProjection z := by
  rcases fordRegion_boundary_cases hz hi with hl | hr | hc | hn
  · have hr' : (rightReflection z).re = stripRight :=
      (rightReflection_re_eq_stripRight_iff z).mpr hl
    have h := orbitProjection_rightReflection_of_right_side hr'
    rw [rightReflection_involutive z] at h
    exact h.symm
  · exact orbitProjection_rightReflection_of_right_side hr
  · have h := triangleOrbitProjection_smul triangleGenerator₁ z
    rwa [triangleGeometricRepresentation_generator₁_apply,
      generatorOne_eq_rightReflection_of_norm_add_one z hc] at h
  · have h := triangleOrbitProjection_smul triangleGenerator₁⁻¹ z
    rwa [generatorOne_inv_representation_apply,
      generatorOne_inv_eq_rightReflection_of_norm z hn] at h

/-- Exact orbit identifications on the closed Ford region.  The second
alternative is exactly the boundary reflection supplied by the two
proved side pairings. -/
theorem orbitProjection_eq_iff_fordRegion {z w : ℍ}
    (hz : z ∈ fordRegion) (hw : w ∈ fordRegion) :
    triangleOrbitProjection z = triangleOrbitProjection w ↔
      z = w ∨ (w = rightReflection z ∧ z ∉ fordInterior) := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := (triangleOrbitProjection_eq_iff w z).mp h.symm
    rcases fordRegion_orbit_point_of_eq g hz hw hg with he | he
    · exact Or.inl he.symm
    · exact Or.inr he
  · rintro (rfl | ⟨he, hi⟩)
    · rfl
    · rw [he]
      exact (orbitProjection_rightReflection_boundary hz hi).symm

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
