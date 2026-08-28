import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangNormBasic
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyExteriorLatticeMatrices

/-!
# Explicit finite norms in the original lattice and exterior coordinates

The entries below evaluate the finite matrix sums already identified
with the actual affine covering norms on singular homology.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic SingularMayerVietoris PeriodTorusHigherHomologyExterior

@[simp] theorem originalNormMatrixOne_three :
    originalNormMatrixOne .three =
      !![3, 0, 0, 0;
         6, 0, 0, 0;
         -12, 0, 0, 0;
         0, 2, 1, 3] := by
  decide

@[simp] theorem originalNormMatrixOne_four :
    originalNormMatrixOne .four =
      !![4, 0, 0, 0;
         12, 0, 0, 0;
         -12, 0, 0, 0;
         0, 2, 2, 4] := by
  decide

@[simp] theorem originalNormMatrixTwo_three :
    originalNormMatrixTwo .three =
      !![0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0;
         2, 1, 3, 0, 0, 0;
         -12, -6, 0, 3, 0, 0;
         8, 4, 6, -1, 0, 0;
         -16, -8, -12, 2, 0, 0] := by
  change (∑ k ∈ Finset.range 3, squareA₁ ^ k) = _
  rw [squareA₁_eq]
  decide

@[simp] theorem originalNormMatrixTwo_four :
    originalNormMatrixTwo .four =
      !![0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0;
         2, 2, 4, 0, 0, 0;
         -12, -12, 0, 4, 0, 0;
         12, 12, 12, -2, 0, 0;
         -12, -12, -12, 2, 0, 0] := by
  change (∑ k ∈ Finset.range 4, squareA₂ ^ k) = _
  rw [squareA₂_eq]
  decide

/-- Concrete entries for the actual order-three first-homology norm. -/
theorem originalAffineNorm_h1_three (a : SingularHomology RealTorus₄ 1) :
    FlatTorus.singularH1Equiv (originalAffineNorm .three 1 a) =
      !![3, 0, 0, 0; 6, 0, 0, 0; -12, 0, 0, 0; 0, 2, 1, 3] *ᵥ
        FlatTorus.singularH1Equiv a := by
  rw [originalAffineNorm_h1_coordinates, originalNormMatrixOne_three]

/-- Concrete entries for the actual order-four first-homology norm. -/
theorem originalAffineNorm_h1_four (a : SingularHomology RealTorus₄ 1) :
    FlatTorus.singularH1Equiv (originalAffineNorm .four 1 a) =
      !![4, 0, 0, 0; 12, 0, 0, 0; -12, 0, 0, 0; 0, 2, 2, 4] *ᵥ
        FlatTorus.singularH1Equiv a := by
  rw [originalAffineNorm_h1_coordinates, originalNormMatrixOne_four]

/-- Concrete entries for the actual order-three second-homology norm. -/
theorem originalAffineNorm_h2_three (a : SingularHomology RealTorus₄ 2) :
    FlatTorus.singularH2Coordinates (originalAffineNorm .three 2 a) =
      !![0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0;
         2, 1, 3, 0, 0, 0;
         -12, -6, 0, 3, 0, 0;
         8, 4, 6, -1, 0, 0;
         -16, -8, -12, 2, 0, 0] *ᵥ FlatTorus.singularH2Coordinates a := by
  rw [originalAffineNorm_h2_coordinates, originalNormMatrixTwo_three]

/-- Concrete entries for the actual order-four second-homology norm. -/
theorem originalAffineNorm_h2_four (a : SingularHomology RealTorus₄ 2) :
    FlatTorus.singularH2Coordinates (originalAffineNorm .four 2 a) =
      !![0, 0, 0, 0, 0, 0;
         0, 0, 0, 0, 0, 0;
         2, 2, 4, 0, 0, 0;
         -12, -12, 0, 4, 0, 0;
         12, 12, 12, -2, 0, 0;
         -12, -12, -12, 2, 0, 0] *ᵥ FlatTorus.singularH2Coordinates a := by
  rw [originalAffineNorm_h2_coordinates, originalNormMatrixTwo_four]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
