import Wikipedia.HopfProblem.CuspBoundaryGammaZeroBoundaryMap
import Wikipedia.HopfProblem.CuspBoundaryGammaZeroHomology
import Wikipedia.HopfProblem.CuspBoundaryGammaZeroWangNaturality

/-!
# A canonical actual gamma-zero class in the native cusp boundary

The literal sub-mapping-torus inclusion preserves the actual signed Wang
boundary. Its positive top class therefore maps to a native degree-four
class whose Wang coordinate is exactly the source's `uwδ` basis vector.
All statements concern actual maps and actual integral singular homology.
No vanishing assertion about the subsequent map into a filling is used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspBoundaryGammaZero

open SingularMayerVietoris PeriodTorusHigherHomology Elliptic.HigherHomology
open MappingTorusHomology
open TrianglePeriodFamily

/-- The actual sub-mapping-torus inclusion preserves Wang with no sign change. -/
theorem boundaryMap_wang (n : ℕ) (a : SingularHomology Boundary (n + 1)) :
    wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n
        (singularHomologyMap boundaryMap (n + 1) a) =
      singularHomologyMap fibreMap n (wangBoundary restrictedMonodromy n a) :=
  wangBoundary_mappingTorusMap restrictedMonodromy ThreefoldOverlapMappingTorus.Cusp.monodromy
    fibreMap fibreMap_monodromy n a

/-- Every source top class has its exact original ordered native Wang coordinate. -/
theorem boundaryMap_wang_coordinates (a : SingularHomology Boundary 4) :
    FlatTorus.singularH3Coordinates
      (wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 3
        (singularHomologyMap boundaryMap 4 a)) =
      Pi.single (3 : Fin 4) (H4Coordinates a) := by
  rw [boundaryMap_wang, fibreMap_h3_coordinates, H4Coordinates_apply]

/-- The native class is the image of the canonical positive source class under the literal map. -/
def nativeClass : SingularHomology ThreefoldOverlapMappingTorus.Cusp.Boundary 4 :=
  singularHomologyMap boundaryMap 4 fundamentalClass

/-- Its actual Wang boundary is the literal included positive three-torus orientation. -/
theorem nativeClass_wang :
    wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 3 nativeClass =
      singularHomologyMap fibreMap 3 (torusH3Coordinates.symm 1) := by
  change wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 3
    (singularHomologyMap boundaryMap 4 fundamentalClass) = _
  rw [boundaryMap_wang, wangBoundary_fundamentalClass]

/-- The native Wang class is precisely the positive `uwδ` coordinate, with coefficient one. -/
theorem nativeClass_wang_coordinates :
    FlatTorus.singularH3Coordinates
      (wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 3 nativeClass) =
      Pi.single (3 : Fin 4) 1 := by
  rw [nativeClass_wang, fibreMap_h3_top]

/-- In particular the constructed native boundary class is genuinely nonzero. -/
theorem nativeClass_ne_zero : nativeClass ≠ 0 := by
  intro h
  have hc := nativeClass_wang_coordinates
  rw [h, map_zero, map_zero] at hc
  have he := congrFun hc (3 : Fin 4)
  norm_num at he

end Wikipedia.HopfProblem.CuspBoundaryGammaZero
