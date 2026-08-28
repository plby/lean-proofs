import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangGeometry
import Wikipedia.HopfProblem.EllipticHigherHomologyCoverIndicesLowDegrees

/-!
# The original surface cover in the actual split-torus coordinates

The finite surface quotient is identified with its already constructed
mapping-torus cover on the entire circle product.  Functoriality then
retains the actual fibre and circle summands in singular homology.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic Elliptic.HigherHomology SingularMayerVietoris PeriodTorusHigherHomology
open SpecialPeriods.EllipticFilling MappingTorusHomology

local notation "S" => ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface

/-- The original flat covering is the original period covering after its
actual period-coordinate homeomorphism. -/
theorem surfaceCover_eq_periodCover (j : Kind) :
    surfaceCover j =
      (periodCover j (specialLocalData j).centralPeriod j.twist (mainTwist_admissible j)).comp
        (flatTorusPeriodHomeomorph (specialLocalData j).centralPeriod.val : C(_, _)) := by
  apply ContinuousMap.ext
  exact surfaceCover_apply j

/-- The complete split covering diagram, on original continuous maps. -/
theorem surfaceCover_split (j : Kind) :
    (surfaceMappingTorusHomeomorph j (specialLocalData j).centralPeriod : C(_, _)).comp
        ((surfaceCover j).comp ((splitFlatTorusHomeomorph j).symm : C(_, _))) =
      Covering.productCover j.order (fibreTorusHomeomorph j)
        (fibreTorusHomeomorph_pow_order j) := by
  apply ContinuousMap.ext
  rintro ⟨c, x⟩
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective c
  change surfaceMappingTorusHomeomorph j (specialLocalData j).centralPeriod
    (surfaceCover j ((splitFlatTorusHomeomorph j).symm ((t : MappingTorus.Circle), x))) = _
  rw [surfaceCover_apply]
  change surfaceMappingTorusHomeomorph j (specialLocalData j).centralPeriod
    (surfaceProjection j (specialLocalData j).centralPeriod j.twist (mainTwist_admissible j)
      ((splitPeriodTorusHomeomorph j (specialLocalData j).centralPeriod.val).symm
        ((t : MappingTorus.Circle), x))) = _
  rw [surfaceMappingTorusHomeomorph_splitPeriodTorus, Covering.productCover_real_apply]

/-- The same diagram on all actual singular homology groups. -/
theorem surfaceCover_split_homology (j : Kind) (n : ℕ)
    (a : SingularHomology (MappingTorus.Circle × ProductTorus 3) n) :
    surfaceMappingTorusHomologyEquiv j (specialLocalData j).centralPeriod n
        (singularHomologyMap (surfaceCover j) n
          (singularHomologyMap ((splitFlatTorusHomeomorph j).symm : C(_, _)) n a)) =
      Covering.productCoverHomology j.order (fibreTorusHomeomorph j)
        (fibreTorusHomeomorph_pow_order j) n a := by
  have h := congrArg
    (fun f : C(MappingTorus.Circle × ProductTorus 3, mappingTorusModel j) =>
      singularHomologyMap f n) (surfaceCover_split j)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  exact LinearMap.congr_fun h a

/-- The original fibre section remains the actual mapping-torus fibre inclusion. -/
theorem surfaceCover_split_section (j : Kind) (n : ℕ)
    (a : SingularHomology (ProductTorus 3) n) :
    surfaceMappingTorusHomologyEquiv j (specialLocalData j).centralPeriod n
        (singularHomologyMap (surfaceCover j) n
          (singularHomologyMap ((splitFlatTorusHomeomorph j).symm : C(_, _)) n
            (circleSectionHomology (ProductTorus 3) n a))) =
      fibreHomologyMap (fibreTorusHomeomorph j).symm n a := by
  rw [surfaceCover_split_homology, Covering.productCoverHomology_circleSection_apply]

/-- The actual surface-cover Wang boundary of the positive split-circle class. -/
theorem surfaceCover_split_cross_wang (j : Kind) (n : ℕ)
    (a : SingularHomology (ProductTorus 3) n) :
    wangBoundary (fibreTorusHomeomorph j).symm n
        (surfaceMappingTorusHomologyEquiv j (specialLocalData j).centralPeriod (n + 1)
          (singularHomologyMap (surfaceCover j) (n + 1)
            (singularHomologyMap ((splitFlatTorusHomeomorph j).symm : C(_, _)) (n + 1)
              (positiveCircleCross (ProductTorus 3) n a)))) =
      fibreHomologyNorm j n a := by
  rw [surfaceCover_split_homology, Covering.wangBoundary_productCover_positiveCircleCross]
  exact LinearMap.congr_fun (fibreHomologyNorm_eq_homologyNorm j n).symm a

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
