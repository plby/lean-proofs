import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologySplit
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyDifference
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyFreeCoordinates

/-!
# Integral singular homology of the actual regular family

The actual Mayer--Vietoris extension, its proved integral endpoint
markings, and a section derived from projectivity give free integral
coordinates in degrees one through five. The first four splittings keep
the positive fibre image in the first coordinate block. In degree five
the actual connecting projection itself is an isomorphism.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology HomologyDifference
open TrianglePeriodFamilyHomologyFreeCoordinates

attribute [local instance] TrianglePeriodFamilyHomologyAlgebra.cokernelQuotientModule
  TrianglePeriodFamilyHomologyAlgebra.kernelModule

variable (D : Data ℂ TriangleRegularPoint)

/-- Actual degree-one homology, with the fibre coinvariant first and the two base cycles last. -/
def familyH1ProductEquiv : SingularHomology D.Space 1 ≃ₗ[ℤ] (ℤ × (ℤ × ℤ)) :=
  familyHomologyMarkedEquiv D 0 cokernelOneEquiv.toAddEquiv kernelZeroEquiv.toAddEquiv

/-- Actual degree-two homology with its primitive fibre coordinate and difference kernel. -/
def familyH2ProductEquiv : SingularHomology D.Space 2 ≃ₗ[ℤ] (ℤ × (Fin 5 → ℤ)) :=
  familyHomologyMarkedEquiv D 1 cokernelTwoEquiv.toAddEquiv kernelOneEquiv.toAddEquiv

/-- Actual degree-three homology with its primitive fibre coordinate and difference kernel. -/
def familyH3ProductEquiv : SingularHomology D.Space 3 ≃ₗ[ℤ] (ℤ × (Fin 7 → ℤ)) :=
  familyHomologyMarkedEquiv D 2 cokernelThreeEquiv.toAddEquiv kernelTwoEquiv.toAddEquiv

/-- Actual degree-four homology with its top fibre coordinate and difference kernel. -/
def familyH4ProductEquiv : SingularHomology D.Space 4 ≃ₗ[ℤ] (ℤ × (Fin 5 → ℤ)) :=
  familyHomologyMarkedEquiv D 3 cokernelFourEquiv.toAddEquiv kernelThreeEquiv.toAddEquiv

/-- The actual fibre map in degree one is the first primitive lattice coordinate. -/
@[simp] theorem familyH1ProductEquiv_fibre (a : SingularHomology RealTorus₄ 1) :
    familyH1ProductEquiv D
      (singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) 1 a) =
      (FlatTorus.singularH1Equiv a 0, 0) :=
  (familyHomologyMarkedEquiv_fibre D 0 cokernelOneEquiv.toAddEquiv
    kernelZeroEquiv.toAddEquiv a).trans
      (Prod.ext (cokernelOneEquiv_mk a) rfl)

/-- The actual degree-two fibre map is the primitive integral functional from the source. -/
@[simp] theorem familyH2ProductEquiv_fibre (a : SingularHomology RealTorus₄ 2) :
    familyH2ProductEquiv D
      (singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) 2 a) =
      (6 * FlatTorus.singularH2Coordinates a 2 + FlatTorus.singularH2Coordinates a 3, 0) :=
  (familyHomologyMarkedEquiv_fibre D 1 cokernelTwoEquiv.toAddEquiv
    kernelOneEquiv.toAddEquiv a).trans
      (Prod.ext (cokernelTwoEquiv_mk a) rfl)

/-- The actual degree-three fibre map is its primitive ordered exterior coordinate. -/
@[simp] theorem familyH3ProductEquiv_fibre (a : SingularHomology RealTorus₄ 3) :
    familyH3ProductEquiv D
      (singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) 3 a) =
      (FlatTorus.singularH3Coordinates a 0, 0) :=
  (familyHomologyMarkedEquiv_fibre D 2 cokernelThreeEquiv.toAddEquiv
    kernelTwoEquiv.toAddEquiv a).trans
      (Prod.ext (cokernelThreeEquiv_mk a) rfl)

/-- The actual degree-four fibre map preserves its proved integral top coordinate. -/
@[simp] theorem familyH4ProductEquiv_fibre (a : SingularHomology RealTorus₄ 4) :
    familyH4ProductEquiv D
      (singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) 4 a) =
      (realTorusH4Equiv a, 0) :=
  (familyHomologyMarkedEquiv_fibre D 3 cokernelFourEquiv.toAddEquiv
    kernelThreeEquiv.toAddEquiv a).trans
      (Prod.ext (cokernelFourEquiv_mk a) rfl)

@[simp] theorem familyH1ProductEquiv_snd (a : SingularHomology D.Space 1) :
    (familyH1ProductEquiv D a).2 = kernelZeroEquiv (sourceKernelProjection D 0 a) :=
  familyHomologyMarkedEquiv_snd D 0 _ _ a

@[simp] theorem familyH2ProductEquiv_snd (a : SingularHomology D.Space 2) :
    (familyH2ProductEquiv D a).2 = kernelOneEquiv (sourceKernelProjection D 1 a) :=
  familyHomologyMarkedEquiv_snd D 1 _ _ a

@[simp] theorem familyH3ProductEquiv_snd (a : SingularHomology D.Space 3) :
    (familyH3ProductEquiv D a).2 = kernelTwoEquiv (sourceKernelProjection D 2 a) :=
  familyHomologyMarkedEquiv_snd D 2 _ _ a

@[simp] theorem familyH4ProductEquiv_snd (a : SingularHomology D.Space 4) :
    (familyH4ProductEquiv D a).2 = kernelThreeEquiv (sourceKernelProjection D 3 a) :=
  familyHomologyMarkedEquiv_snd D 3 _ _ a

/-- With zero higher fibre homology, the actual connecting projection is injective. -/
theorem sourceKernelProjection_injective_of_torus_vanish (n : ℕ)
    (hn : Subsingleton (SingularHomology RealTorus₄ (n + 1))) :
    Function.Injective (sourceKernelProjection D n) := by
  intro a b hab
  have hzero : sourceKernelProjection D n (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨q, hq⟩ := (sourceCoinvariantInclusion_kernelProjection_exact D n (a - b)).mp hzero
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hx : x = 0 := hn.elim _ _
  rw [hx, Submodule.Quotient.mk_zero, map_zero] at hq
  exact sub_eq_zero.mp hq.symm

/-- The actual degree-five connecting projection is an integral isomorphism. -/
def familyH5KernelEquiv :
    SingularHomology D.Space 5 ≃ₗ[ℤ] LinearMap.ker (sourceDifference 4) :=
  LinearEquiv.ofBijective (sourceKernelProjection D 4)
    ⟨sourceKernelProjection_injective_of_torus_vanish D 4
      (realTorus_homology_subsingleton_of_lt (by decide)),
      sourceKernelProjection_surjective D 4⟩

@[simp] theorem familyH5KernelEquiv_apply (a : SingularHomology D.Space 5) :
    familyH5KernelEquiv D a = sourceKernelProjection D 4 a := rfl

/-- Actual degree-five homology is identified by its two marked top-fibre
boundary coordinates. -/
def familyH5ProductEquiv : SingularHomology D.Space 5 ≃ₗ[ℤ] (ℤ × ℤ) :=
  ((familyH5KernelEquiv D).toAddEquiv.trans kernelFourEquiv.toAddEquiv).toIntLinearEquiv

@[simp] theorem familyH5ProductEquiv_apply (a : SingularHomology D.Space 5) :
    familyH5ProductEquiv D a = kernelFourEquiv (sourceKernelProjection D 4 a) := rfl

/-- Actual first singular homology is free of rank three over the integers. -/
def familyH1Equiv : SingularHomology D.Space 1 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  let e : (ℤ × (ℤ × ℤ)) ≃+ (ℤ × (Fin 2 → ℤ)) :=
    (AddEquiv.refl ℤ).prodCongr (LinearEquiv.finTwoArrow ℤ ℤ).symm.toAddEquiv
  (((familyH1ProductEquiv D).toAddEquiv.trans e).toIntLinearEquiv).trans
    (integerFreeCoordinateEquiv 2)

/-- Actual second singular homology is free of rank six over the integers. -/
def familyH2Equiv : SingularHomology D.Space 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  (familyH2ProductEquiv D).trans (integerFreeCoordinateEquiv 5)

/-- Actual third singular homology is free of rank eight over the integers. -/
def familyH3Equiv : SingularHomology D.Space 3 ≃ₗ[ℤ] (Fin 8 → ℤ) :=
  (familyH3ProductEquiv D).trans (integerFreeCoordinateEquiv 7)

/-- Actual fourth singular homology is free of rank six over the integers. -/
def familyH4Equiv : SingularHomology D.Space 4 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  (familyH4ProductEquiv D).trans (integerFreeCoordinateEquiv 5)

/-- Actual fifth singular homology is free of rank two over the integers. -/
def familyH5Equiv : SingularHomology D.Space 5 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (familyH5ProductEquiv D).trans (LinearEquiv.finTwoArrow ℤ ℤ).symm

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
