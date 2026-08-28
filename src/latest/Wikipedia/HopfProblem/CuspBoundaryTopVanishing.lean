import Wikipedia.HopfProblem.CuspBoundaryTopVanishingCap
import Wikipedia.HopfProblem.CuspBoundaryGammaZero

/-!
# The actual gamma-zero swept three-torus bounds in the original cusp cap

This is the cap-vanishing assertion for the source's swept `uwδ`
three-torus in Remark 7.23.  The class is the image of the actual
canonical positive top class of the literal gamma-zero invariant
three-torus mapping torus.  It is not an arbitrary preimage of the
corresponding Wang coordinate.

The vanishing theorem concerns the original boundary-to-filling map at
the original gluing radius.  Its proof is the preceding explicit
whole-circle collapse, actual central Mayer--Vietoris argument, and
actual whole-boundary height homotopy.
-/

noncomputable section

open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspBoundaryTopVanishing

open SingularMayerVietoris PeriodTorusHigherHomology
open ThreefoldOverlapMappingTorus.Cusp

/-- The actual full sub-boundary map has zero fourth homology image in
the original cusp filling. -/
theorem boundaryToFilling_gammaBoundary_homologyFour_eq_zero :
    singularHomologyMap
      ((ThreefoldOverlapMappingTorus.boundaryToFilling none).comp
        CuspBoundaryGammaZero.boundaryMap) 4 = 0 := by
  rw [gammaBoundaryToFilling_eq]
  exact gammaBoundaryToFull_homologyFour_eq_zero specialData specialHeight

/-- Every top class of the literal gamma-zero mapping torus maps to
zero under the two original geometric maps. -/
theorem boundaryToFilling_boundaryMap_homologyFour
    (a : SingularHomology CuspBoundaryGammaZero.Boundary 4) :
    singularHomologyMap (ThreefoldOverlapMappingTorus.boundaryToFilling none) 4
      (singularHomologyMap CuspBoundaryGammaZero.boundaryMap 4 a) = 0 := by
  have h := LinearMap.congr_fun boundaryToFilling_gammaBoundary_homologyFour_eq_zero a
  rw [singularHomologyMap_comp CuspBoundaryGammaZero.boundaryMap
    (ThreefoldOverlapMappingTorus.boundaryToFilling none) 4] at h
  exact h

/-- The exact canonical native swept `uwδ` class vanishes in the
original full cusp cap.  The class retains its previously proved
positive `uwδ` Wang coordinate and original monodromy convention. -/
theorem boundaryToFilling_nativeClass_eq_zero :
    singularHomologyMap (ThreefoldOverlapMappingTorus.boundaryToFilling none) 4
      CuspBoundaryGammaZero.nativeClass = 0 :=
  boundaryToFilling_boundaryMap_homologyFour CuspBoundaryGammaZero.fundamentalClass

/-- The same equality in the original global boundary-filling
coefficient API. -/
theorem boundaryFillingHomologyMap_nativeClass_eq_zero :
    ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap none 4
      CuspBoundaryGammaZero.nativeClass = 0 :=
  boundaryToFilling_nativeClass_eq_zero

end Wikipedia.HopfProblem.CuspBoundaryTopVanishing
