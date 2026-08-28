import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyDifferenceCoordinates
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyDifferenceLowCoordinates
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyDifferenceEquiv

/-!
# Actual homology-difference kernels and cokernels

The actual singular-homology maps are conjugate to the computed integral
lattice maps. Transporting their literal kernels and quotient cokernels
therefore gives the free modules and primitive quotient coordinates below.
No statement about a total-space homology group is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.HomologyDifference

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
  TrianglePeriodFamilyHomologyAlgebra.kernelModule

/-- The actual degree-0 homology kernel in the literal lattice-difference coordinates. -/
def kernelZeroCoordinates :
    LinearMap.ker (Homology.sourceDifference 0) ≃ₗ[ℤ]
      LinearMap.ker TrianglePeriodFamilyHomologyLattice.deltaZero :=
  kernelEquivOfCommuting (Homology.sourceDifference 0)
    TrianglePeriodFamilyHomologyLattice.deltaZero
    ((connectedHomologyZeroEquiv RealTorus₄).toAddEquiv.prodCongr
      (connectedHomologyZeroEquiv RealTorus₄).toAddEquiv).toIntLinearEquiv
    (connectedHomologyZeroEquiv RealTorus₄) sourceDifferenceZero_coordinates

@[simp] theorem kernelZeroCoordinates_apply_val
    (x : LinearMap.ker (Homology.sourceDifference 0)) :
    (kernelZeroCoordinates x : ℤ × ℤ) =
      ((connectedHomologyZeroEquiv RealTorus₄) x.val.1,
        (connectedHomologyZeroEquiv RealTorus₄) x.val.2) := rfl

/-- The kernel of the actual degree-0 singular-homology difference map is free. -/
def kernelZeroEquiv : LinearMap.ker (Homology.sourceDifference 0) ≃ₗ[ℤ] (ℤ × ℤ) :=
  (kernelZeroCoordinates.toAddEquiv.trans
    TrianglePeriodFamilyHomologyLattice.kernelZeroEquiv.toAddEquiv).toIntLinearEquiv

/-- The actual quotient cokernel in the literal lattice-difference coordinates. -/
def cokernelZeroCoordinates :
    (SingularHomology RealTorus₄ 0 ⧸ LinearMap.range (Homology.sourceDifference 0)) ≃ₗ[ℤ]
      (ℤ ⧸ LinearMap.range TrianglePeriodFamilyHomologyLattice.deltaZero) :=
  cokernelEquivOfCommuting (Homology.sourceDifference 0)
    TrianglePeriodFamilyHomologyLattice.deltaZero
    ((connectedHomologyZeroEquiv RealTorus₄).toAddEquiv.prodCongr
      (connectedHomologyZeroEquiv RealTorus₄).toAddEquiv).toIntLinearEquiv
    (connectedHomologyZeroEquiv RealTorus₄) sourceDifferenceZero_coordinates

@[simp] theorem cokernelZeroCoordinates_mk (a : SingularHomology RealTorus₄ 0) :
    cokernelZeroCoordinates (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk ((connectedHomologyZeroEquiv RealTorus₄) a) := rfl

/-- The actual singular-homology difference cokernel is infinite cyclic over the integers. -/
def cokernelZeroEquiv :
    (SingularHomology RealTorus₄ 0 ⧸ LinearMap.range (Homology.sourceDifference 0)) ≃ₗ[ℤ] ℤ :=
  (cokernelZeroCoordinates.toAddEquiv.trans
    TrianglePeriodFamilyHomologyLattice.cokernelZeroEquiv.toAddEquiv).toIntLinearEquiv

/-- The actual quotient class is evaluated by the specified primitive coordinate. -/
@[simp] theorem cokernelZeroEquiv_mk (a : SingularHomology RealTorus₄ 0) :
    cokernelZeroEquiv (Submodule.Quotient.mk a) =
      connectedHomologyZeroEquiv RealTorus₄ a := by
  change TrianglePeriodFamilyHomologyLattice.cokernelZeroEquiv
    (cokernelZeroCoordinates (Submodule.Quotient.mk a)) = _
  rw [cokernelZeroCoordinates_mk]
  exact TrianglePeriodFamilyHomologyLattice.cokernelZeroEquiv_mk _

/-- The inverse coordinate is represented by an actual marked fibre-homology class. -/
@[simp] theorem cokernelZeroEquiv_symm_apply (z : ℤ) :
    cokernelZeroEquiv.symm z =
      Submodule.Quotient.mk ((connectedHomologyZeroEquiv RealTorus₄).symm z) := by
  apply cokernelZeroEquiv.injective
  rw [LinearEquiv.apply_symm_apply, cokernelZeroEquiv_mk]
  simp only [LinearEquiv.apply_symm_apply]

/-- The actual degree-1 homology kernel in the literal lattice-difference coordinates. -/
def kernelOneCoordinates :
    LinearMap.ker (Homology.sourceDifference 1) ≃ₗ[ℤ]
      LinearMap.ker TrianglePeriodFamilyHomologyLattice.deltaOne :=
  kernelEquivOfCommuting (Homology.sourceDifference 1)
    TrianglePeriodFamilyHomologyLattice.deltaOne
    (FlatTorus.singularH1Equiv.toAddEquiv.prodCongr
      FlatTorus.singularH1Equiv.toAddEquiv).toIntLinearEquiv
    FlatTorus.singularH1Equiv sourceDifferenceOne_coordinates

@[simp] theorem kernelOneCoordinates_apply_val
    (x : LinearMap.ker (Homology.sourceDifference 1)) :
    (kernelOneCoordinates x : Lattice × Lattice) =
      (FlatTorus.singularH1Equiv x.val.1, FlatTorus.singularH1Equiv x.val.2) := rfl

/-- The kernel of the actual degree-1 singular-homology difference map is free. -/
def kernelOneEquiv : LinearMap.ker (Homology.sourceDifference 1) ≃ₗ[ℤ] (Fin 5 → ℤ) :=
  (kernelOneCoordinates.toAddEquiv.trans
    TrianglePeriodFamilyHomologyLattice.kernelOneEquiv.toAddEquiv).toIntLinearEquiv

/-- The actual quotient cokernel in the literal lattice-difference coordinates. -/
def cokernelOneCoordinates :
    (SingularHomology RealTorus₄ 1 ⧸ LinearMap.range (Homology.sourceDifference 1)) ≃ₗ[ℤ]
      (Lattice ⧸ LinearMap.range TrianglePeriodFamilyHomologyLattice.deltaOne) :=
  cokernelEquivOfCommuting (Homology.sourceDifference 1)
    TrianglePeriodFamilyHomologyLattice.deltaOne
    (FlatTorus.singularH1Equiv.toAddEquiv.prodCongr
      FlatTorus.singularH1Equiv.toAddEquiv).toIntLinearEquiv
    FlatTorus.singularH1Equiv sourceDifferenceOne_coordinates

@[simp] theorem cokernelOneCoordinates_mk (a : SingularHomology RealTorus₄ 1) :
    cokernelOneCoordinates (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (FlatTorus.singularH1Equiv a) := rfl

/-- The actual singular-homology difference cokernel is infinite cyclic over the integers. -/
def cokernelOneEquiv :
    (SingularHomology RealTorus₄ 1 ⧸ LinearMap.range (Homology.sourceDifference 1)) ≃ₗ[ℤ] ℤ :=
  (cokernelOneCoordinates.toAddEquiv.trans
    TrianglePeriodFamilyHomologyLattice.cokernelOneEquiv.toAddEquiv).toIntLinearEquiv

/-- The actual quotient class is evaluated by the specified primitive coordinate. -/
@[simp] theorem cokernelOneEquiv_mk (a : SingularHomology RealTorus₄ 1) :
    cokernelOneEquiv (Submodule.Quotient.mk a) =
      FlatTorus.singularH1Equiv a 0 := by
  change TrianglePeriodFamilyHomologyLattice.cokernelOneEquiv
    (cokernelOneCoordinates (Submodule.Quotient.mk a)) = _
  rw [cokernelOneCoordinates_mk]
  exact TrianglePeriodFamilyHomologyLattice.cokernelOneEquiv_mk _

/-- The inverse coordinate is represented by an actual marked fibre-homology class. -/
@[simp] theorem cokernelOneEquiv_symm_apply (z : ℤ) :
    cokernelOneEquiv.symm z =
      Submodule.Quotient.mk (FlatTorus.singularH1Equiv.symm ![z, 0, 0, 0]) := by
  apply cokernelOneEquiv.injective
  rw [LinearEquiv.apply_symm_apply, cokernelOneEquiv_mk]
  simp only [LinearEquiv.apply_symm_apply]
  rfl

/-- The actual degree-2 homology kernel in the literal lattice-difference coordinates. -/
def kernelTwoCoordinates :
    LinearMap.ker (Homology.sourceDifference 2) ≃ₗ[ℤ]
      LinearMap.ker TrianglePeriodFamilyHomologyLattice.deltaTwo :=
  kernelEquivOfCommuting (Homology.sourceDifference 2)
    TrianglePeriodFamilyHomologyLattice.deltaTwo
    (FlatTorus.singularH2Coordinates.toAddEquiv.prodCongr
      FlatTorus.singularH2Coordinates.toAddEquiv).toIntLinearEquiv
    FlatTorus.singularH2Coordinates sourceDifferenceTwo_coordinates

@[simp] theorem kernelTwoCoordinates_apply_val
    (x : LinearMap.ker (Homology.sourceDifference 2)) :
    (kernelTwoCoordinates x : (Fin 6 → ℤ) × (Fin 6 → ℤ)) =
      (FlatTorus.singularH2Coordinates x.val.1, FlatTorus.singularH2Coordinates x.val.2) := rfl

/-- The kernel of the actual degree-2 singular-homology difference map is free. -/
def kernelTwoEquiv : LinearMap.ker (Homology.sourceDifference 2) ≃ₗ[ℤ] (Fin 7 → ℤ) :=
  (kernelTwoCoordinates.toAddEquiv.trans
    TrianglePeriodFamilyHomologyLattice.kernelTwoEquiv.toAddEquiv).toIntLinearEquiv

/-- The actual quotient cokernel in the literal lattice-difference coordinates. -/
def cokernelTwoCoordinates :
    (SingularHomology RealTorus₄ 2 ⧸ LinearMap.range (Homology.sourceDifference 2)) ≃ₗ[ℤ]
      ((Fin 6 → ℤ) ⧸ LinearMap.range TrianglePeriodFamilyHomologyLattice.deltaTwo) :=
  cokernelEquivOfCommuting (Homology.sourceDifference 2)
    TrianglePeriodFamilyHomologyLattice.deltaTwo
    (FlatTorus.singularH2Coordinates.toAddEquiv.prodCongr
      FlatTorus.singularH2Coordinates.toAddEquiv).toIntLinearEquiv
    FlatTorus.singularH2Coordinates sourceDifferenceTwo_coordinates

@[simp] theorem cokernelTwoCoordinates_mk (a : SingularHomology RealTorus₄ 2) :
    cokernelTwoCoordinates (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (FlatTorus.singularH2Coordinates a) := rfl

/-- The actual singular-homology difference cokernel is infinite cyclic over the integers. -/
def cokernelTwoEquiv :
    (SingularHomology RealTorus₄ 2 ⧸ LinearMap.range (Homology.sourceDifference 2)) ≃ₗ[ℤ] ℤ :=
  (cokernelTwoCoordinates.toAddEquiv.trans
    TrianglePeriodFamilyHomologyLattice.cokernelTwoEquiv.toAddEquiv).toIntLinearEquiv

/-- The actual quotient class is evaluated by the specified primitive coordinate. -/
@[simp] theorem cokernelTwoEquiv_mk (a : SingularHomology RealTorus₄ 2) :
    cokernelTwoEquiv (Submodule.Quotient.mk a) =
      6 * FlatTorus.singularH2Coordinates a 2 + FlatTorus.singularH2Coordinates a 3 := by
  change TrianglePeriodFamilyHomologyLattice.cokernelTwoEquiv
    (cokernelTwoCoordinates (Submodule.Quotient.mk a)) = _
  rw [cokernelTwoCoordinates_mk]
  exact TrianglePeriodFamilyHomologyLattice.cokernelTwoEquiv_mk _

/-- The inverse coordinate is represented by an actual marked fibre-homology class. -/
@[simp] theorem cokernelTwoEquiv_symm_apply (z : ℤ) :
    cokernelTwoEquiv.symm z =
      Submodule.Quotient.mk (FlatTorus.singularH2Coordinates.symm ![0, 0, 0, z, 0, 0]) := by
  apply cokernelTwoEquiv.injective
  rw [LinearEquiv.apply_symm_apply, cokernelTwoEquiv_mk]
  simp only [LinearEquiv.apply_symm_apply]
  simp

/-- The actual degree-3 homology kernel in the literal lattice-difference coordinates. -/
def kernelThreeCoordinates :
    LinearMap.ker (Homology.sourceDifference 3) ≃ₗ[ℤ]
      LinearMap.ker TrianglePeriodFamilyHomologyLattice.deltaThree :=
  kernelEquivOfCommuting (Homology.sourceDifference 3)
    TrianglePeriodFamilyHomologyLattice.deltaThree
    (FlatTorus.singularH3Coordinates.toAddEquiv.prodCongr
      FlatTorus.singularH3Coordinates.toAddEquiv).toIntLinearEquiv
    FlatTorus.singularH3Coordinates sourceDifferenceThree_coordinates

@[simp] theorem kernelThreeCoordinates_apply_val
    (x : LinearMap.ker (Homology.sourceDifference 3)) :
    (kernelThreeCoordinates x : Lattice × Lattice) =
      (FlatTorus.singularH3Coordinates x.val.1, FlatTorus.singularH3Coordinates x.val.2) := rfl

/-- The kernel of the actual degree-3 singular-homology difference map is free. -/
def kernelThreeEquiv : LinearMap.ker (Homology.sourceDifference 3) ≃ₗ[ℤ] (Fin 5 → ℤ) :=
  (kernelThreeCoordinates.toAddEquiv.trans
    TrianglePeriodFamilyHomologyLattice.kernelThreeEquiv.toAddEquiv).toIntLinearEquiv

/-- The actual quotient cokernel in the literal lattice-difference coordinates. -/
def cokernelThreeCoordinates :
    (SingularHomology RealTorus₄ 3 ⧸ LinearMap.range (Homology.sourceDifference 3)) ≃ₗ[ℤ]
      (Lattice ⧸ LinearMap.range TrianglePeriodFamilyHomologyLattice.deltaThree) :=
  cokernelEquivOfCommuting (Homology.sourceDifference 3)
    TrianglePeriodFamilyHomologyLattice.deltaThree
    (FlatTorus.singularH3Coordinates.toAddEquiv.prodCongr
      FlatTorus.singularH3Coordinates.toAddEquiv).toIntLinearEquiv
    FlatTorus.singularH3Coordinates sourceDifferenceThree_coordinates

@[simp] theorem cokernelThreeCoordinates_mk (a : SingularHomology RealTorus₄ 3) :
    cokernelThreeCoordinates (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (FlatTorus.singularH3Coordinates a) := rfl

/-- The actual singular-homology difference cokernel is infinite cyclic over the integers. -/
def cokernelThreeEquiv :
    (SingularHomology RealTorus₄ 3 ⧸ LinearMap.range (Homology.sourceDifference 3)) ≃ₗ[ℤ] ℤ :=
  (cokernelThreeCoordinates.toAddEquiv.trans
    TrianglePeriodFamilyHomologyLattice.cokernelThreeEquiv.toAddEquiv).toIntLinearEquiv

/-- The actual quotient class is evaluated by the specified primitive coordinate. -/
@[simp] theorem cokernelThreeEquiv_mk (a : SingularHomology RealTorus₄ 3) :
    cokernelThreeEquiv (Submodule.Quotient.mk a) =
      FlatTorus.singularH3Coordinates a 0 := by
  change TrianglePeriodFamilyHomologyLattice.cokernelThreeEquiv
    (cokernelThreeCoordinates (Submodule.Quotient.mk a)) = _
  rw [cokernelThreeCoordinates_mk]
  exact TrianglePeriodFamilyHomologyLattice.cokernelThreeEquiv_mk _

/-- The inverse coordinate is represented by an actual marked fibre-homology class. -/
@[simp] theorem cokernelThreeEquiv_symm_apply (z : ℤ) :
    cokernelThreeEquiv.symm z =
      Submodule.Quotient.mk (FlatTorus.singularH3Coordinates.symm ![z, 0, 0, 0]) := by
  apply cokernelThreeEquiv.injective
  rw [LinearEquiv.apply_symm_apply, cokernelThreeEquiv_mk]
  simp only [LinearEquiv.apply_symm_apply]
  rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.HomologyDifference

