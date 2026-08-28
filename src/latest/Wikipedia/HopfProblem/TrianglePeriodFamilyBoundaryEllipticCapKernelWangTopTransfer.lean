import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTopShear
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTopNorm

/-!
# The native finite-cover comparison in third homology

The actual twist-circle shear has now been proved to preserve every
positive-circle cross class in degree four.  Substitution in the existing
geometric finite-cover square gives the third-homology norm identity
without a supplied homology-map hypothesis.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic SingularMayerVietoris

/-- The genuine degree-four cap-kernel cross map, followed by Wang, is the
actual finite norm on every class coming from the original surface cover. -/
theorem crossWang_surfaceCover_three (j : Kind) (a : SingularHomology RealTorus₄ 3) :
    crossWang j 3 (singularHomologyMap (surfaceCover j) 3 a) =
      originalAffineNorm j 3 a :=
  crossWang_surfaceCover_of_shear j 3 a (nativeShear_positiveCircleCross_three j a)

/-- The actual degree-four cap-kernel Wang map in the ordered third exterior marking. -/
def h3Coordinates (j : Kind) :
    SingularHomology (ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j) 3 →ₗ[ℤ]
      Lattice :=
  FlatTorus.singularH3Coordinates.toLinearMap.comp (crossWang j 3)

@[simp] theorem h3Coordinates_apply (j : Kind)
    (a : SingularHomology (ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j) 3) :
    h3Coordinates j a = FlatTorus.singularH3Coordinates (crossWang j 3 a) := rfl

/-- The actual coordinate map on the literal cover is the computed original affine norm. -/
theorem h3Coordinates_surfaceCover (j : Kind) (a : SingularHomology RealTorus₄ 3) :
    h3Coordinates j (singularHomologyMap (surfaceCover j) 3 a) =
      FlatTorus.singularH3Coordinates (originalAffineNorm j 3 a) := by
  rw [h3Coordinates_apply, crossWang_surfaceCover_three]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
