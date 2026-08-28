import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryGammaZeroCusp
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspSourceProjection
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticGaugeLinearization
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapProductMarked
import Wikipedia.HopfProblem.TrianglePeriodFamilyGammaZeroHomology

/-!
# A full actual fourth-homology relation among the three boundary sections

The native zero-γ cusp class and the two actual elliptic cap-section
classes all map into the literal rank-three regular subfamily.  Their
actual source-kernel coordinates agree with the displayed signed Wang
classes.  Since the source-kernel projection is injective on this actual
subfamily image, the resulting equality is an equality in the whole
regular-family fourth homology, including its residual fibre coordinate.

No arbitrary splitting is used.  In particular the image of the cusp
class in its filling is not assumed to vanish.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.FourthRelation

open Elliptic Elliptic.HigherHomology SpecialPeriods SpecialPeriods.EllipticFilling
open Homology SingularMayerVietoris PeriodTorusHigherHomology MappingTorusHomology
open ThreefoldOverlapMappingTorus EllipticCapProduct EllipticGaugeLinearization

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The two genuine cap-section Wang classes are the negatives of the
same actual native cusp Wang class, not merely classes of equal rank. -/
theorem unitCapSection_wang_eq_neg_cusp (j : Kind) :
    wangBoundary (flatTorusAffine j j.twist) 3 (unitCapSectionClass j) =
      -wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 3
        CuspBoundaryGammaZero.nativeClass := by
  apply FlatTorus.singularH3Coordinates.injective
  rw [unitCapSectionClass_wang, map_neg, CuspBoundaryGammaZero.nativeClass_wang_coordinates]

/-- The actual inverse first source generator fixes this genuine native cusp Wang class. -/
theorem nativeClass_wang_first_inv_fixed :
    triangleHomologyEquiv triangleGenerator₁⁻¹ 3
        (wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 3
          CuspBoundaryGammaZero.nativeClass) =
      wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 3
        CuspBoundaryGammaZero.nativeClass := by
  have h := ellipticWangBoundary_generator_inv_fixed .three Kind.three.twist 3
    (unitCapSectionClass .three)
  change triangleHomologyEquiv triangleGenerator₁⁻¹ 3
    (wangBoundary (flatTorusAffine .three Kind.three.twist) 3 (unitCapSectionClass .three)) =
      wangBoundary (flatTorusAffine .three Kind.three.twist) 3 (unitCapSectionClass .three) at h
  rw [unitCapSection_wang_eq_neg_cusp, map_neg] at h
  exact neg_injective h

/-- Each actual elliptic unit section lands in the genuine zero-γ homology image. -/
theorem unitCapSection_regular_mem_range (j : Kind) :
    boundaryRegularHomologyMap (some j) 4 (unitCapSectionClass j) ∈
      LinearMap.range (GammaZero.homologyInclusion Dsp 4) :=
  boundaryRegularHomologyMap_capSection_mem_range j 0 4
    ((surfaceH4Equiv j (specialLocalData j).centralPeriod).symm 1)

/-- The actual source-kernel coordinates of the native cusp class and
the sum of the two genuine cap sections agree. -/
theorem nativeClass_sourceKernel_eq_capSections :
    sourceKernelProjection Dsp 3
        (boundaryRegularHomologyMap none 4 CuspBoundaryGammaZero.nativeClass) =
      sourceKernelProjection Dsp 3
        (boundaryRegularHomologyMap (some Kind.three) 4 (unitCapSectionClass .three) +
          boundaryRegularHomologyMap (some Kind.four) 4 (unitCapSectionClass .four)) := by
  apply Subtype.ext
  have hadd :
      (sourceKernelProjection Dsp 3
          (boundaryRegularHomologyMap (some Kind.three) 4 (unitCapSectionClass .three) +
            boundaryRegularHomologyMap (some Kind.four) 4 (unitCapSectionClass .four)) :
        SingularHomology RealTorus₄ 3 × SingularHomology RealTorus₄ 3) =
        (sourceKernelProjection Dsp 3
          (boundaryRegularHomologyMap (some Kind.three) 4 (unitCapSectionClass .three)) :
            SingularHomology RealTorus₄ 3 × SingularHomology RealTorus₄ 3) +
        (sourceKernelProjection Dsp 3
          (boundaryRegularHomologyMap (some Kind.four) 4 (unitCapSectionClass .four)) :
            SingularHomology RealTorus₄ 3 × SingularHomology RealTorus₄ 3) :=
    congrArg Subtype.val (map_add (sourceKernelProjection Dsp 3) _ _)
  have hc :
      (sourceKernelProjection Dsp 3
          (boundaryRegularHomologyMap none 4 CuspBoundaryGammaZero.nativeClass) :
        SingularHomology RealTorus₄ 3 × SingularHomology RealTorus₄ 3) =
        (-triangleHomologyEquiv triangleGenerator₁⁻¹ 3
          (wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 3
            CuspBoundaryGammaZero.nativeClass),
          -wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 3
            CuspBoundaryGammaZero.nativeClass) :=
    Cusp.boundary_four_sourceKernelProjection CuspBoundaryGammaZero.nativeClass
  rw [hc, hadd, ellipticThreeBoundary_sourceKernelProjection,
    ellipticFourBoundary_sourceKernelProjection, unitCapSection_wang_eq_neg_cusp,
    unitCapSection_wang_eq_neg_cusp, nativeClass_wang_first_inv_fixed]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

/-- The complete original regular-family `H₄` relation, including the
otherwise undetected residual fibre coordinate. -/
theorem nativeClass_regular_eq_capSections :
    boundaryRegularHomologyMap none 4 CuspBoundaryGammaZero.nativeClass =
      boundaryRegularHomologyMap (some Kind.three) 4 (unitCapSectionClass .three) +
        boundaryRegularHomologyMap (some Kind.four) 4 (unitCapSectionClass .four) := by
  apply GammaZero.sourceKernelProjection_injOn_range Dsp
    CuspBoundaryGammaZero.nativeClass_regular_mem_range
    (Submodule.add_mem _ (unitCapSection_regular_mem_range .three)
      (unitCapSection_regular_mem_range .four))
  exact nativeClass_sourceKernel_eq_capSections

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.FourthRelation
