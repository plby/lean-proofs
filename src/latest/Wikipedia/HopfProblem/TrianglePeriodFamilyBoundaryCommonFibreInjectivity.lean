import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCommonFibreInjectivityCore
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCommonFibreCore

/-!
# Injectivity on the common actual fourth-homology fibre class

All three original boundary fibre maps have been identified with the same
normalized positive fibre inclusion by genuine homotopies. Its proved
fourth-homology injectivity therefore applies to each literal boundary
coefficient on its Wang fibre and to each original fibre-to-family map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SpecialPeriods.Threefold SingularMayerVietoris
open ThreefoldOverlapMappingTorus MappingTorusHomology

/-- Each original attachment coefficient is injective on the actual fourth-homology fibre. -/
theorem boundaryRegularHomologyMap_common_fibre_four_injective (i : Puncture) :
    Function.Injective
      ((boundaryRegularHomologyMap i 4).comp (fibreHomologyMap (monodromy i) 4)) := by
  rw [boundaryRegularHomologyMap_common_fibre]
  exact normalizedFamilyFibreHomologyFour_injective _

/-- Each literal original fibre-to-regular-family map is injective on fourth singular homology. -/
theorem fibreToRegularFamily_homologyFour_injective (i : Puncture) :
    Function.Injective (singularHomologyMap (fibreToRegularFamily i) 4) := by
  rw [fibreToRegularFamily_homology_common]
  exact normalizedFamilyFibreHomologyFour_injective _

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
