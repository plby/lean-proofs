import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepCentral
import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepFlatProduct
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTwo

/-!
# Transfer coordinates of the genuine central delta sweep

The finite covering here is exactly the one used by the original Wang
coordinates. Its two genuine first-homology columns determine the transfer
of the actual sweep. The covering shear is retained throughout; no chosen
Wang section is identified with a literal base circle.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep

open Elliptic Elliptic.HigherHomology EllipticFilling SingularMayerVietoris
open TrianglePeriodFamily TrianglePeriodFamily.Boundary.EllipticCapKernelWang
open PeriodTorusHigherHomologyPontryagin

/-- The actual central finite cover is the unchanged covering used in the
frozen Wang coordinates. -/
theorem centralFlatPeriodCover_eq_surfaceCover (j : Kind) :
    centralFlatPeriodCover j = surfaceCover j := by
  rw [surfaceCover_eq_periodCover]
  rfl

/-- The finite norm kills the delta-left product with the primitive fibre
one-class, in the original six exterior coordinates. -/
theorem originalAffineNorm_delta_splitFibreClassOne (j : Kind) :
    FlatTorus.singularH2Coordinates
      (originalAffineNorm j 2
        (product11 RealTorus₄ (FlatTorus.singularH1Equiv.symm deltaLattice)
          (splitFibreClassOne j))) = 0 := by
  have hf : splitFibreClassOne j =
      FlatTorus.singularH1Equiv.symm ![0, 0, 1, 0] := by
    apply FlatTorus.singularH1Equiv.injective
    rw [splitFibreClassOne_coordinates, LinearEquiv.apply_symm_apply]
  rw [hf, originalAffineNorm_h2_coordinates, deltaLattice, flat_delta_product11_coordinates]
  cases j
  · rw [originalNormMatrixTwo_three]
    decide
  · rw [originalNormMatrixTwo_four]
    decide

/-- The positive delta circle is the first input. Consequently its product
with the actual positive twist has the negative `twist ∧ δ` norm. -/
theorem originalAffineNorm_delta_splitCircleClassOne (j : Kind) :
    FlatTorus.singularH2Coordinates
      (originalAffineNorm j 2
        (product11 RealTorus₄ (FlatTorus.singularH1Equiv.symm deltaLattice)
          (splitCircleClassOne j))) =
      -(j.order : ℤ) • twistDeltaVector j := by
  have hc : splitCircleClassOne j = FlatTorus.singularH1Equiv.symm j.twist := by
    apply FlatTorus.singularH1Equiv.injective
    rw [splitCircleClassOne_coordinates, LinearEquiv.apply_symm_apply]
  rw [hc, originalAffineNorm_h2_coordinates, deltaLattice, flat_delta_product11_coordinates]
  cases j
  · rw [originalNormMatrixTwo_three]
    decide
  · rw [originalNormMatrixTwo_four]
    decide

/-- Transfer of a genuinely swept covering class is its actual finite
affine norm, not a substitute map on a coordinate module. -/
theorem centralSweep_h2Coordinates_surfaceCover (j : Kind)
    (v : SingularHomology RealTorus₄ 1) :
    h2Coordinates j
        (centralSweep j 1 (singularHomologyMap (surfaceCover j) 1 v)) =
      FlatTorus.singularH2Coordinates
        (originalAffineNorm j 2
          (product11 RealTorus₄ (FlatTorus.singularH1Equiv.symm deltaLattice) v)) := by
  rw [← centralFlatPeriodCover_eq_surfaceCover, centralSweep_flatPeriodCover,
    centralFlatPeriodCover_eq_surfaceCover, h2Coordinates_surfaceCover]

/-- In the original transfer coordinates, the actual central sweep
depends only on the second coordinate of the unchanged first Wang marking. -/
theorem centralSweep_h2Coordinates (j : Kind)
    (a : SingularHomology (SpecialCentralSurface j) 1) :
    h2Coordinates j (centralSweep j 1 a) =
      -surfaceH1Equiv j (specialLocalData j).centralPeriod a 1 • twistDeltaVector j := by
  have h := map_cover_columns (surfaceH1Equiv j (specialLocalData j).centralPeriod)
    ((h2Coordinates j).comp (centralSweep j 1))
    (singularHomologyMap (surfaceCover j) 1 (splitFibreClassOne j))
    (singularHomologyMap (surfaceCover j) 1 (splitCircleClassOne j)) a
    (sourceShearOne j) (j.order : ℤ)
    (surfaceCover_splitFibreClassOne j) (surfaceCover_splitCircleClassOne j)
  simp only [LinearMap.comp_apply, centralSweep_h2Coordinates_surfaceCover,
    originalAffineNorm_delta_splitFibreClassOne,
    originalAffineNorm_delta_splitCircleClassOne, smul_zero, zero_add] at h
  ext i
  apply mul_left_cancel₀ (show (j.order : ℤ) ≠ 0 by cases j <;> decide)
  have hi := congrFun h i
  change (j.order : ℤ) * h2Coordinates j (centralSweep j 1 a) i =
    surfaceH1Equiv j (specialLocalData j).centralPeriod a 1 *
      (-(j.order : ℤ) * twistDeltaVector j i) at hi
  change (j.order : ℤ) * h2Coordinates j (centralSweep j 1 a) i =
    (j.order : ℤ) *
      (-surfaceH1Equiv j (specialLocalData j).centralPeriod a 1 * twistDeltaVector j i)
  rw [hi]
  ring

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep
