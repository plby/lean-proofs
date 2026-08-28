import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapProductWangReflection
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapProductFibreCoordinates

/-!
# The actual Wang boundary of the cap section

The genuine cap section reverses the base parameter of the genuine
central-surface mapping torus.  Actual Mayer--Vietoris naturality therefore
gives a minus sign.  The retained fibre map is the literal coordinate
three-torus inclusion, so the positive fourth-homology class of either
central surface has actual Wang boundary equal to minus the `uwδ` class.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct

open Elliptic Elliptic.HigherHomology SpecialPeriods SpecialPeriods.EllipticFilling
open PeriodTorusHigherHomology SingularMayerVietoris MappingTorusHomology

/-- Naturality of the actual Wang map for the literal time-reversing cap section. -/
theorem capSectionFromModel_wang (j : Kind) (n : ℕ)
    (a : SingularHomology (mappingTorusModel j) (n + 1)) :
    wangBoundary (flatTorusAffine j j.twist) n
      (singularHomologyMap (capSectionFromModel j) (n + 1) a) =
        -singularHomologyMap (capSectionFibre j 0) n
          (wangBoundary (fibreTorusHomeomorph j).symm n a) :=
  wangBoundary_timeReflection_of_quarter
    (fibreTorusHomeomorph j).symm (flatTorusAffine j j.twist)
    (capSectionFromModel j) (capSectionFibre j) (capSectionFromModel_mk j)
    (capSectionFibre j 0) n a (affine_symm_capSectionFibre_wang j (3 / 4) n a)

/-- The same formula with the original actual central surface as the domain. -/
theorem capSection_wang (j : Kind) (n : ℕ)
    (a : SingularHomology (ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j)
      (n + 1)) :
    wangBoundary (flatTorusAffine j j.twist) n
      (singularHomologyMap (capSection j) (n + 1) a) =
        -singularHomologyMap (capSectionFibre j 0) n
          (wangBoundary (fibreTorusHomeomorph j).symm n
            (homeomorphHomologyEquiv
              (surfaceMappingTorusHomeomorph j (specialLocalData j).centralPeriod) (n + 1) a)) := by
  have hcomp : (capSectionFromModel j).comp
      (surfaceMappingTorusHomeomorph j (specialLocalData j).centralPeriod : C(_, _)) =
        capSection j := by
    ext x
    change capSection j
      ((surfaceMappingTorusHomeomorph j (specialLocalData j).centralPeriod).symm
        (surfaceMappingTorusHomeomorph j (specialLocalData j).centralPeriod x)) = _
    rw [Homeomorph.symm_apply_apply]
  rw [← hcomp, singularHomologyMap_comp, LinearMap.comp_apply, capSectionFromModel_wang]
  rfl

/-- The positive top class of the original surface has the exact negative
`uwδ` Wang coordinate in the source's ordered flat-torus marking. -/
theorem capSection_wang_h4_coordinates (j : Kind)
    (a : SingularHomology (ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j) 4) :
    FlatTorus.singularH3Coordinates
      (wangBoundary (flatTorusAffine j j.twist) 3
        (singularHomologyMap (capSection j) 4 a)) =
      -Pi.single (3 : Fin 4) (surfaceH4Equiv j (specialLocalData j).centralPeriod a) := by
  rw [capSection_wang, map_neg, capSectionFibre_zero_h3]
  congr 2

/-- The prescribed unit cap class has an actual, not postulated, primitive
Wang coordinate in the common `uwδ` direction. -/
theorem capSection_wang_h4_unit (j : Kind) :
    FlatTorus.singularH3Coordinates
      (wangBoundary (flatTorusAffine j j.twist) 3
        (singularHomologyMap (capSection j) 4
          ((surfaceH4Equiv j (specialLocalData j).centralPeriod).symm 1))) =
        -Pi.single (3 : Fin 4) 1 := by
  rw [capSection_wang_h4_coordinates, LinearEquiv.apply_symm_apply]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct
