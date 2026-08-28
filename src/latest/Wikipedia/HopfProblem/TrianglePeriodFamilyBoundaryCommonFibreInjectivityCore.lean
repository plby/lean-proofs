import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologySourceSequence
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyDifferenceTopCoordinates

/-!
# Injectivity of the actual regular-family fibre in degree four

The exact kernel of the normalized, positive fibre inclusion is the range
of the actual two-generator monodromy difference. That difference vanishes
on fourth singular homology, so the literal fibre inclusion is injective.
No chosen splitting of the family homology is used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SingularMayerVietoris

variable (D : Data ℂ TriangleRegularPoint)

/-- The literal normalized fibre map has zero kernel on actual fourth homology. -/
theorem normalizedFamilyFibreHomologyFour_ker :
    LinearMap.ker (singularHomologyMap
      (Homology.familyFibreInclusion D Homology.normalizedSlitBaseLift) 4) = ⊥ := by
  rw [Homology.familyFibreInclusion_kernel, HomologyDifference.sourceDifference_four,
    LinearMap.range_zero]

/-- The actual positive normalized fibre inclusion is injective on fourth homology. -/
theorem normalizedFamilyFibreHomologyFour_injective :
    Function.Injective (singularHomologyMap
      (Homology.familyFibreInclusion D Homology.normalizedSlitBaseLift) 4) :=
  LinearMap.ker_eq_bot.mp (normalizedFamilyFibreHomologyFour_ker D)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
