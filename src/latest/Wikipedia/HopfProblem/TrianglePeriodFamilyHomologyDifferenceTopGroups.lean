import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyDifferenceRanks
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyDifferenceTopCoordinates

/-!
# Actual top-degree homology-difference kernel and cokernel

The actual top homology action, transported through the real torus's circle
coordinates, is the identity. Its literal difference kernel and cokernel
therefore have the integral coordinates and ranks below.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.HomologyDifference

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
  TrianglePeriodFamilyHomologyAlgebra.kernelModule

/-- The actual top-degree homology kernel in determinant-lattice coordinates. -/
def kernelFourCoordinates :
    LinearMap.ker (Homology.sourceDifference 4) ≃ₗ[ℤ]
      LinearMap.ker TrianglePeriodFamilyHomologyLattice.deltaFour :=
  kernelEquivOfCommuting (Homology.sourceDifference 4)
    TrianglePeriodFamilyHomologyLattice.deltaFour
    (realTorusH4Equiv.toAddEquiv.prodCongr realTorusH4Equiv.toAddEquiv).toIntLinearEquiv
    realTorusH4Equiv sourceDifferenceFour_coordinates

@[simp] theorem kernelFourCoordinates_apply_val
    (x : LinearMap.ker (Homology.sourceDifference 4)) :
    (kernelFourCoordinates x : ℤ × ℤ) =
      (realTorusH4Equiv x.val.1, realTorusH4Equiv x.val.2) := rfl

/-- The actual top-degree difference kernel is a free rank-two integral module. -/
def kernelFourEquiv : LinearMap.ker (Homology.sourceDifference 4) ≃ₗ[ℤ] (ℤ × ℤ) :=
  (kernelFourCoordinates.toAddEquiv.trans
    TrianglePeriodFamilyHomologyLattice.kernelFourEquiv.toAddEquiv).toIntLinearEquiv

/-- The actual top-degree quotient cokernel in determinant-lattice coordinates. -/
def cokernelFourCoordinates :
    (SingularHomology RealTorus₄ 4 ⧸ LinearMap.range (Homology.sourceDifference 4)) ≃ₗ[ℤ]
      (ℤ ⧸ LinearMap.range TrianglePeriodFamilyHomologyLattice.deltaFour) :=
  cokernelEquivOfCommuting (Homology.sourceDifference 4)
    TrianglePeriodFamilyHomologyLattice.deltaFour
    (realTorusH4Equiv.toAddEquiv.prodCongr realTorusH4Equiv.toAddEquiv).toIntLinearEquiv
    realTorusH4Equiv sourceDifferenceFour_coordinates

@[simp] theorem cokernelFourCoordinates_mk (a : SingularHomology RealTorus₄ 4) :
    cokernelFourCoordinates (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (realTorusH4Equiv a) := rfl

/-- The actual top-degree singular-homology difference cokernel is infinite cyclic. -/
def cokernelFourEquiv :
    (SingularHomology RealTorus₄ 4 ⧸ LinearMap.range (Homology.sourceDifference 4)) ≃ₗ[ℤ] ℤ :=
  (cokernelFourCoordinates.toAddEquiv.trans
    TrianglePeriodFamilyHomologyLattice.cokernelFourEquiv.toAddEquiv).toIntLinearEquiv

theorem cokernelFourEquiv_apply
    (q : SingularHomology RealTorus₄ 4 ⧸ LinearMap.range (Homology.sourceDifference 4)) :
    cokernelFourEquiv q =
      TrianglePeriodFamilyHomologyLattice.cokernelFourEquiv (cokernelFourCoordinates q) := rfl

@[simp] theorem cokernelFourEquiv_mk (a : SingularHomology RealTorus₄ 4) :
    cokernelFourEquiv (Submodule.Quotient.mk a) = realTorusH4Equiv a := by
  rw [cokernelFourEquiv_apply, cokernelFourCoordinates_mk,
    TrianglePeriodFamilyHomologyLattice.cokernelFourEquiv_mk]

@[simp] theorem cokernelFourEquiv_symm_apply (z : ℤ) :
    cokernelFourEquiv.symm z = Submodule.Quotient.mk (realTorusH4Equiv.symm z) := by
  apply cokernelFourEquiv.injective
  rw [LinearEquiv.apply_symm_apply, cokernelFourEquiv_mk, LinearEquiv.apply_symm_apply]

theorem kernelFour_free : Module.Free ℤ (LinearMap.ker (Homology.sourceDifference 4)) :=
  Module.Free.of_equiv kernelFourEquiv.symm

theorem kernelFour_finite : Module.Finite ℤ (LinearMap.ker (Homology.sourceDifference 4)) :=
  Module.Finite.of_surjective kernelFourEquiv.symm.toLinearMap kernelFourEquiv.symm.surjective

theorem kernelFour_finrank : Module.finrank ℤ
    (LinearMap.ker (Homology.sourceDifference 4)) = 2 := by
  rw [kernelFourEquiv.finrank_eq]
  simp

theorem cokernelFour_free : Module.Free ℤ
    (SingularHomology RealTorus₄ 4 ⧸ LinearMap.range (Homology.sourceDifference 4)) :=
  Module.Free.of_equiv cokernelFourEquiv.symm

theorem cokernelFour_finite : Module.Finite ℤ
    (SingularHomology RealTorus₄ 4 ⧸ LinearMap.range (Homology.sourceDifference 4)) :=
  Module.Finite.of_surjective cokernelFourEquiv.symm.toLinearMap cokernelFourEquiv.symm.surjective

theorem cokernelFour_finrank : Module.finrank ℤ
    (SingularHomology RealTorus₄ 4 ⧸ LinearMap.range (Homology.sourceDifference 4)) = 1 := by
  rw [cokernelFourEquiv.finrank_eq]
  exact Module.finrank_self ℤ

end Wikipedia.HopfProblem.TrianglePeriodFamily.HomologyDifference
