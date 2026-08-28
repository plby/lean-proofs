import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTransfer
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangSource
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangAlgebra

/-!
# The actual cap-kernel Wang map in the original flat markings

The two genuine covering columns determine the Wang map on every class
of the actual central surface.  The existing surface marking and its
actual off-diagonal coefficient are left unchanged.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic Elliptic.HigherHomology SingularMayerVietoris PeriodTorusHigherHomology
open SpecialPeriods.EllipticFilling

local notation "S" => ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface

/-- The actual degree-two cap-kernel Wang coefficient in the original period-loop marking. -/
def h1Coordinates (j : Kind) : SingularHomology (S j) 1 →ₗ[ℤ] Lattice :=
  FlatTorus.singularH1Equiv.toLinearMap.comp (crossWang j 1)

/-- The actual degree-three coefficient in the original ordered exterior-square marking. -/
def h2Coordinates (j : Kind) : SingularHomology (S j) 2 →ₗ[ℤ] (Fin 6 → ℤ) :=
  FlatTorus.singularH2Coordinates.toLinearMap.comp (crossWang j 2)

@[simp] theorem h1Coordinates_apply (j : Kind) (a : SingularHomology (S j) 1) :
    h1Coordinates j a = FlatTorus.singularH1Equiv (crossWang j 1 a) := rfl

@[simp] theorem h2Coordinates_apply (j : Kind) (a : SingularHomology (S j) 2) :
    h2Coordinates j a = FlatTorus.singularH2Coordinates (crossWang j 2 a) := rfl

theorem h1Coordinates_surfaceCover (j : Kind) (a : SingularHomology RealTorus₄ 1) :
    h1Coordinates j (singularHomologyMap (surfaceCover j) 1 a) =
      FlatTorus.singularH1Equiv (originalAffineNorm j 1 a) := by
  rw [h1Coordinates_apply, crossWang_surfaceCover_one]

theorem h2Coordinates_surfaceCover (j : Kind) (a : SingularHomology RealTorus₄ 2) :
    h2Coordinates j (singularHomologyMap (surfaceCover j) 2 a) =
      FlatTorus.singularH2Coordinates (originalAffineNorm j 2 a) := by
  rw [h2Coordinates_apply, crossWang_surfaceCover_two]

/-- Multiplication by the genuine covering degree gives the complete first coefficient. -/
theorem h1Coordinates_cover_columns (j : Kind) (a : SingularHomology (S j) 1) :
    (j.order : ℤ) • h1Coordinates j a =
      ((j.order : ℤ) * surfaceH1Equiv j (specialLocalData j).centralPeriod a 0 -
          sourceShearOne j * surfaceH1Equiv j (specialLocalData j).centralPeriod a 1) •
        FlatTorus.singularH1Equiv (originalAffineNorm j 1 (splitFibreClassOne j)) +
      surfaceH1Equiv j (specialLocalData j).centralPeriod a 1 •
        FlatTorus.singularH1Equiv (originalAffineNorm j 1 (splitCircleClassOne j)) := by
  have h := map_cover_columns (surfaceH1Equiv j (specialLocalData j).centralPeriod)
    (h1Coordinates j)
    (singularHomologyMap (surfaceCover j) 1 (splitFibreClassOne j))
    (singularHomologyMap (surfaceCover j) 1 (splitCircleClassOne j)) a
    (sourceShearOne j) (j.order : ℤ)
    (surfaceCover_splitFibreClassOne j) (surfaceCover_splitCircleClassOne j)
  simpa only [h1Coordinates_surfaceCover] using h

/-- The genuine one-or-two norm index gives the complete second coefficient. -/
theorem h2Coordinates_cover_columns (j : Kind) (a : SingularHomology (S j) 2) :
    (fibreNormIndex j : ℤ) • h2Coordinates j a =
      ((fibreNormIndex j : ℤ) * surfaceH2Equiv j (specialLocalData j).centralPeriod a 0 -
          sourceShearTwo j * surfaceH2Equiv j (specialLocalData j).centralPeriod a 1) •
        FlatTorus.singularH2Coordinates (originalAffineNorm j 2 (splitFibreClassTwo j)) +
      surfaceH2Equiv j (specialLocalData j).centralPeriod a 1 •
        FlatTorus.singularH2Coordinates (originalAffineNorm j 2 (splitCircleClassTwo j)) := by
  have h := map_cover_columns (surfaceH2Equiv j (specialLocalData j).centralPeriod)
    (h2Coordinates j)
    (singularHomologyMap (surfaceCover j) 2 (splitFibreClassTwo j))
    (singularHomologyMap (surfaceCover j) 2 (splitCircleClassTwo j)) a
    (sourceShearTwo j) (fibreNormIndex j : ℤ)
    (surfaceCover_splitFibreClassTwo j) (surfaceCover_splitCircleClassTwo j)
  simpa only [h2Coordinates_surfaceCover] using h

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
