import Wikipedia.HopfProblem.TriangleUniformizationGluingWords
import Wikipedia.HopfProblem.TriangleUniformizationGluingClosedSectors

/-!
# Returns to the actual closed circular polygon

The boundary-inclusive cyclic-sector estimates instantiate the reduced-word
lemma for the genuine Möbius action.  Thus an element relating two points of
the closed polygon is one of the bounded powers of its two cyclic generators.
-/

noncomputable section

open Set UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- A return to the actual closed circular polygon comes from one cyclic
factor, with an explicitly bounded exponent. -/
theorem circularDoubleRegion_return_generator_pow (g : TriangleGroup) {z : ℍ}
    (hz : z ∈ circularDoubleRegion)
    (hgz : triangleGeometricRepresentation g z ∈ circularDoubleRegion) :
    (∃ n : ℕ, n < 3 ∧ g = triangleGenerator₁ ^ n) ∨
      (∃ n : ℕ, n < 4 ∧ g = triangleGenerator₂ ^ n) := by
  exact triangleLift_eq_generator_pow_of_closed_domain_mem
    generatorOnePerm generatorTwoPerm generatorOnePerm_cube generatorTwoPerm_fourth
    firstExcluded secondExcluded firstWeakExcluded secondWeakExcluded circularDoubleRegion
    firstExcluded_subset_firstWeakExcluded secondExcluded_subset_secondWeakExcluded
    (fun _ hw => generatorOnePerm_firstSector (secondWeakExcluded_subset_firstSector hw))
    (fun _ hw => generatorOnePerm_sq_firstSector (secondWeakExcluded_subset_firstSector hw))
    (fun _ hw => generatorTwoPerm_secondSector (firstWeakExcluded_subset_secondSector hw))
    (fun _ hw => generatorTwoPerm_sq_secondSector (firstWeakExcluded_subset_secondSector hw))
    (fun _ hw => generatorTwoPerm_cube_secondSector (firstWeakExcluded_subset_secondSector hw))
    (fun _ hw => generatorOne_closedFirstSector hw.1)
    (fun z hw => by
      change (generatorOnePerm ^ 2) z ∈ firstWeakExcluded
      rw [generatorOnePerm_pow_apply]
      exact generatorOne_sq_closedFirstSector hw.1)
    (fun _ hw => generatorTwo_closedSecondSector hw.2)
    (fun z hw => by
      change (generatorTwoPerm ^ 2) z ∈ secondWeakExcluded
      rw [generatorTwoPerm_pow_apply]
      exact generatorTwo_sq_closedSecondSector hw.2)
    (fun z hw => by
      change (generatorTwoPerm ^ 3) z ∈ secondWeakExcluded
      rw [generatorTwoPerm_pow_apply]
      exact generatorTwo_cube_closedSecondSector hw.2)
    circularDoubleRegion_disjoint_firstExcluded circularDoubleRegion_disjoint_secondExcluded
    g hz hgz

/-- Equality of two actual closed-polygon points under a triangle element
has the same finite cyclic-factor classification. -/
theorem circularDoubleRegion_return_generator_pow_of_eq (g : TriangleGroup) {z w : ℍ}
    (hz : z ∈ circularDoubleRegion) (hw : w ∈ circularDoubleRegion)
    (hzw : triangleGeometricRepresentation g z = w) :
    (∃ n : ℕ, n < 3 ∧ g = triangleGenerator₁ ^ n) ∨
      (∃ n : ℕ, n < 4 ∧ g = triangleGenerator₂ ^ n) :=
  circularDoubleRegion_return_generator_pow g hz (hzw ▸ hw)

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
