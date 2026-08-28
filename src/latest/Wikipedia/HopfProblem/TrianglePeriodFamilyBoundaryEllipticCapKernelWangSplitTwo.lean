import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangSplitOne
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangSplitTwoProducts
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportTorus

/-!
# Original degree-two coordinates of the elliptic split classes

The genuine inverse splitting acts by the minors of its actual integral
twist basis. The ordered loop-product calculations fix the two input
coordinates and hence their coordinates in the original flat torus.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic Elliptic.HigherHomology SingularMayerVietoris PeriodTorusHigherHomology

/-- The actual inverse splitting acts on the original second-homology marking by its minors. -/
theorem splitFlat_inverse_h2_coordinates (j : Kind)
    (a : SingularHomology (CircleTopology.Circle × ProductTorus 3) 2) :
    FlatTorus.singularH2Coordinates
      (singularHomologyMap ((splitFlatTorusHomeomorph j).symm :
        C(CircleTopology.Circle × ProductTorus 3, RealTorus₄)) 2 a) =
      LocalSystemMatrices.exteriorSquare (twistBasisMatrix j) *ᵥ
        coordinateTorusH2Coordinates
          (singularHomologyMap ((productTorusSuccHomeomorph 3).symm :
            C(CircleTopology.Circle × ProductTorus 3, ProductTorus 4)) 2 a) := by
  rw [FlatTorus.singularH2Coordinates_apply, FlatTorus.singularH2Equiv_apply,
    splitFlat_inverse_circle_homology]
  exact coordinateTorusH2Coordinates_matrix (twistBasisMatrix j) _

/-- The actual split fibre input is the positive original `u ∧ w` class. -/
theorem splitFibreClassTwo_coordinates (j : Kind) :
    FlatTorus.singularH2Coordinates (splitFibreClassTwo j) = ![0, 0, 0, 1, 0, 0] := by
  rw [splitFibreClassTwo, splitFlat_inverse_h2_coordinates, splitTwo_fibre_unsplit_coordinates]
  cases j <;> decide

/-- The ordered circle input is the original twist wedged with the positive `w`-direction. -/
theorem splitCircleClassTwo_coordinates (j : Kind) :
    FlatTorus.singularH2Coordinates (splitCircleClassTwo j) =
      ![0, j.twist 0, 0, j.twist 1, 0, 0] := by
  rw [splitCircleClassTwo, splitFlat_inverse_h2_coordinates, splitTwo_circle_unsplit_coordinates]
  cases j <;> decide

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
