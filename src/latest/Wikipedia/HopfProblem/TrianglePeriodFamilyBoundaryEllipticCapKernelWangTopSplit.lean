import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTopSource
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTopSplitProducts
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangSplitOne
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportTorus

/-!
# Original degree-three coordinates of the actual elliptic split source classes

The genuine inverse splitting acts by the exterior cube of its actual
integral twist basis.  Ordered positive loop products identify both input
classes, so their original coordinates are the positive `uwδ` generator
and the signed `γuw` generator.  The surface-cover shear remains the
actual coordinate defined in the existing surface marking.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic Elliptic.HigherHomology SingularMayerVietoris PeriodTorusHigherHomology

/-- The original inverse splitting acts on actual third homology by its literal three-minors. -/
theorem splitFlat_inverse_h3_coordinates (j : Kind)
    (a : SingularHomology (CircleTopology.Circle × ProductTorus 3) 3) :
    FlatTorus.singularH3Coordinates
      (singularHomologyMap ((splitFlatTorusHomeomorph j).symm :
        C(CircleTopology.Circle × ProductTorus 3, RealTorus₄)) 3 a) =
      LocalSystemMatrices.exteriorCube (twistBasisMatrix j) *ᵥ
        coordinateTorusH3Coordinates
          (singularHomologyMap ((productTorusSuccHomeomorph 3).symm :
            C(CircleTopology.Circle × ProductTorus 3, ProductTorus 4)) 3 a) := by
  rw [FlatTorus.singularH3Coordinates_apply, FlatTorus.singularH3Equiv_apply,
    splitFlat_inverse_circle_homology]
  exact coordinateTorusH3Coordinates_matrix (twistBasisMatrix j) _

/-- The genuine positive fibre top class is the original positive `uwδ` basis vector. -/
theorem splitFibreClassThree_coordinates (j : Kind) :
    FlatTorus.singularH3Coordinates (splitFibreClassThree j) = ![0, 0, 0, 1] := by
  rw [splitFibreClassThree, splitFlat_inverse_h3_coordinates,
    splitThree_fibre_unsplit_coordinates]
  cases j <;> decide

/-- The actual positive split-circle cross class is the original `γuw` generator
with the true twist sign; its other original coordinates vanish. -/
theorem splitCircleClassThree_coordinates (j : Kind) :
    FlatTorus.singularH3Coordinates (splitCircleClassThree j) =
      ![γ j.twist, 0, 0, 0] := by
  rw [splitCircleClassThree, splitFlat_inverse_h3_coordinates,
    splitThree_circle_unsplit_coordinates]
  cases j <;> decide

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
