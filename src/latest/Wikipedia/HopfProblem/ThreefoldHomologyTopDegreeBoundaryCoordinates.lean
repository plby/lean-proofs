import Wikipedia.HopfProblem.ThreefoldHomologyTopDegreeGrouping
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticTopWang
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusHomology
import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlapMonodromy
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyGroups

/-!
# Canonical fifth-homology coordinates on the actual boundary pieces

The actual top fibre actions are identities, including the cusp action
identified by its original quotient homeomorphism.  The genuine Wang
boundaries therefore give integral coordinates on all three original
overlaps.  The regular-family coordinate is its original source-kernel
projection; no projective splitting enters in degree five.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.TopDegree

open SingularMayerVietoris PeriodTorusHigherHomology
open MappingTorusHomology ThreefoldOverlapMappingTorus
open TrianglePeriodFamily.Homology TrianglePeriodFamily.HomologyDifference

local notation "Dsp" =>
  TrianglePeriodFamily.regularData
    specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- Every actual triangle torus map has the identity top-homology map. -/
theorem triangleTopHomologyMap_identity (g : TriangleGroup) :
    singularHomologyMap (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) 4 =
      LinearMap.id := by
  change (triangleHomologyEquiv g 4).toLinearMap = _
  rw [triangleHomologyFour_identity]
  rfl

/-- The actual affine elliptic and cusp boundary monodromies all preserve
the genuine top fibre class. -/
theorem boundaryMonodromy_four_identity (i : Puncture) :
    monodromyHomologyMap (monodromy i) 4 = LinearMap.id := by
  cases i with
  | none =>
    change singularHomologyMap
      (CuspFamily.cuspTorusHomeomorph 1 : C(RealTorus₄, RealTorus₄)) 4 = _
    rw [← triangleTorusHomeomorph_cusp_zpow 1]
    exact triangleTopHomologyMap_identity _
  | some j =>
    change singularHomologyMap
      (Elliptic.flatTorusAffine j j.twist : C(RealTorus₄, RealTorus₄)) 4 = _
    rw [TrianglePeriodFamily.Boundary.flatTorusAffine_homology_triangle,
      triangleHomologyFour_identity]
    rfl

/-- The fifth-homology marking is the actual Wang boundary followed by
the genuine integral top-fibre marking. -/
def boundaryFifthEquiv (i : Puncture) : SingularHomology (Boundary i) 5 ≃ₗ[ℤ] ℤ :=
  (TrianglePeriodFamily.Boundary.H5ToH4WangEquiv (monodromy i)
    (boundaryMonodromy_four_identity i)).trans realTorusH4Equiv

@[simp] theorem boundaryFifthEquiv_apply (i : Puncture)
    (a : SingularHomology (Boundary i) 5) :
    boundaryFifthEquiv i a = realTorusH4Equiv (wangBoundary (monodromy i) 4 a) := rfl

/-- Canonical fifth homology of each literal intersection in the original threefold. -/
def overlapFifthEquiv (i : Puncture) :
    SingularHomology (RegularOverlap i) 5 ≃ₗ[ℤ] ℤ :=
  (overlapHomologyEquiv i 5).trans (boundaryFifthEquiv i)

@[simp] theorem overlapFifthEquiv_apply (i : Puncture)
    (a : SingularHomology (RegularOverlap i) 5) :
    overlapFifthEquiv i a =
      boundaryFifthEquiv i (overlapHomologyEquiv i 5 a) :=
  LinearEquiv.trans_apply a

/-- The actual regular-family boundary coordinate in degree five. -/
def regularFifthEquiv : SingularHomology SpecialRegularFamily 5 ≃ₗ[ℤ] (ℤ × ℤ) :=
  familyH5ProductEquiv Dsp

@[simp] theorem regularFifthEquiv_apply (a : SingularHomology SpecialRegularFamily 5) :
    regularFifthEquiv a =
      (realTorusH4Equiv (sourceKernelProjection Dsp 4 a).val.1,
        realTorusH4Equiv (sourceKernelProjection Dsp 4 a).val.2) := rfl

/-- The two actual elliptic Wang coordinates in the original order-three,
order-four ordering. -/
def ellipticFifthCoordinates : EllipticOverlapFifth ≃ₗ[ℤ] (ℤ × ℤ) :=
  ({ toFun := fun a =>
       (overlapFifthEquiv (some .three) (a .three),
         overlapFifthEquiv (some .four) (a .four))
     invFun := fun a j => match j with
       | .three => (overlapFifthEquiv (some .three)).symm a.1
       | .four => (overlapFifthEquiv (some .four)).symm a.2
     left_inv := by
       intro a
       funext j
       cases j <;> exact LinearEquiv.symm_apply_apply _ _
     right_inv := fun a => Prod.ext
       (LinearEquiv.apply_symm_apply _ a.1) (LinearEquiv.apply_symm_apply _ a.2)
     map_add' := fun a b => Prod.ext (map_add _ _ _) (map_add _ _ _) } :
    EllipticOverlapFifth ≃+ (ℤ × ℤ)).toIntLinearEquiv

@[simp] theorem ellipticFifthCoordinates_apply (a : EllipticOverlapFifth) :
    ellipticFifthCoordinates a =
      (overlapFifthEquiv (some .three) (a .three),
        overlapFifthEquiv (some .four) (a .four)) := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.TopDegree
