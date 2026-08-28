import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangNorm
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangSplitTwo
import Wikipedia.HopfProblem.EllipticHigherHomologyNormData

/-!
# Actual finite norms of the four native elliptic split inputs

All four inputs are defined by the genuine section and positive cross
maps. Their original homology markings are computed geometrically before
the already checked original finite norm matrices are applied.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic Elliptic.HigherHomology SingularMayerVietoris

/-- The fibre's positive `w`-loop has norm equal to the index times the original `δ`-loop. -/
theorem originalAffineNorm_splitFibreClassOne (j : Kind) :
    FlatTorus.singularH1Equiv (originalAffineNorm j 1 (splitFibreClassOne j)) =
      (fibreNormIndex j : ℤ) • (![0, 0, 0, 1] : Lattice) := by
  rw [originalAffineNorm_h1_coordinates, splitFibreClassOne_coordinates]
  cases j
  · rw [originalNormMatrixOne_three]
    decide
  · rw [originalNormMatrixOne_four]
    decide

/-- The actual primitive twist circle has norm equal to the order times the twist. -/
theorem originalAffineNorm_splitCircleClassOne (j : Kind) :
    FlatTorus.singularH1Equiv (originalAffineNorm j 1 (splitCircleClassOne j)) =
      (j.order : ℤ) • j.twist := by
  rw [originalAffineNorm_h1_coordinates, splitCircleClassOne_coordinates]
  cases j
  · rw [originalNormMatrixOne_three]
    decide
  · rw [originalNormMatrixOne_four]
    decide

/-- The actual positive fibre pair has norm equal to the index times the original invariant pair. -/
theorem originalAffineNorm_splitFibreClassTwo (j : Kind) :
    FlatTorus.singularH2Coordinates (originalAffineNorm j 2 (splitFibreClassTwo j)) =
      (fibreNormIndex j : ℤ) •
        ![0, 0, 0, fibreSquareKernelVector j 0,
          fibreSquareKernelVector j 1, fibreSquareKernelVector j 2] := by
  rw [originalAffineNorm_h2_coordinates, splitFibreClassTwo_coordinates]
  cases j
  · rw [originalNormMatrixTwo_three]
    decide
  · rw [originalNormMatrixTwo_four]
    decide

/-- The positive twist-circle pair has norm equal to the index times `twist ∧ δ`. -/
theorem originalAffineNorm_splitCircleClassTwo (j : Kind) :
    FlatTorus.singularH2Coordinates (originalAffineNorm j 2 (splitCircleClassTwo j)) =
      (fibreNormIndex j : ℤ) • ![0, 0, j.twist 0, 0, j.twist 1, j.twist 2] := by
  rw [originalAffineNorm_h2_coordinates, splitCircleClassTwo_coordinates]
  cases j
  · rw [originalNormMatrixTwo_three]
    decide
  · rw [originalNormMatrixTwo_four]
    decide

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
