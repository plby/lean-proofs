import Wikipedia.HopfProblem.EllipticHigherHomologyMappingTorusGroups
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePointClass

/-!
# Actual zeroth and first homology of the elliptic mapping tori

The augmentation of the actual connected three-torus makes every
continuous self-map the identity in degree zero.  Thus its actual
degree-zero Wang operator vanishes.  The genuine degree-zero endpoint
and the first short exact Wang extension identify the actual mapping
torus homology with `ℤ` and `ℤ²`.

These equivalences retain the literal fibre-inclusion maps, the positive
point class, and the signed Wang boundary.  No homology action or rank
is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology MappingTorusHomology

/-- The actual positive augmentation marking of the three-torus. -/
abbrev torusH0Coordinates : SingularHomology (ProductTorus 3) 0 ≃ₗ[ℤ] ℤ :=
  connectedHomologyZeroEquiv (ProductTorus 3)

@[simp] theorem torusH0Coordinates_pointClass (x : ProductTorus 3) :
    torusH0Coordinates (pointClass x) = 1 :=
  connectedHomologyZeroEquiv_pointClass x

/-- Naturality of actual augmentation computes the degree-zero monodromy. -/
theorem mappingTorusMonodromy_zero (j : Kind)
    (a : SingularHomology (ProductTorus 3) 0) :
    torusH0Coordinates (monodromyHomologyMap (fibreTorusHomeomorph j).symm 0 a) =
      torusH0Coordinates a :=
  connectedHomologyZeroEquiv_natural
    ((fibreTorusHomeomorph j).symm : C(ProductTorus 3, ProductTorus 3)) a

/-- The genuine degree-zero homology monodromy is the identity map. -/
theorem mappingTorusMonodromy_zero_eq_id (j : Kind) :
    monodromyHomologyMap (fibreTorusHomeomorph j).symm 0 =
      LinearMap.id (R := ℤ) (M := SingularHomology (ProductTorus 3) 0) := by
  ext a
  apply torusH0Coordinates.injective
  exact mappingTorusMonodromy_zero j a

/-- The actual degree-zero Wang operator vanishes. -/
theorem mappingTorusDifference_zero (j : Kind) :
    wangDifference (fibreTorusHomeomorph j).symm 0 = 0 := by
  ext a
  apply torusH0Coordinates.injective
  change torusH0Coordinates
    (a - monodromyHomologyMap (fibreTorusHomeomorph j).symm 0 a) = torusH0Coordinates 0
  rw [map_sub, mappingTorusMonodromy_zero, sub_self, map_zero]

/-- The actual degree-zero invariant subgroup is the point-class axis. -/
def mappingTorusKernelZeroEquiv (j : Kind) :
    LinearMap.ker (wangDifference (fibreTorusHomeomorph j).symm 0) ≃ₗ[ℤ] ℤ := by
  letI := (LinearMap.ker (wangDifference (fibreTorusHomeomorph j).symm 0)).module
  letI := (⊤ : Submodule ℤ (SingularHomology (ProductTorus 3) 0)).module
  exact (((LinearEquiv.ofEq (LinearMap.ker (wangDifference (fibreTorusHomeomorph j).symm 0))
    (⊤ : Submodule ℤ (SingularHomology (ProductTorus 3) 0))
    (by rw [mappingTorusDifference_zero, LinearMap.ker_zero])).toAddEquiv.trans
    Submodule.topEquiv.toAddEquiv).trans torusH0Coordinates.toAddEquiv).toIntLinearEquiv

@[simp] theorem mappingTorusKernelZeroEquiv_apply (j : Kind)
    (a : LinearMap.ker (wangDifference (fibreTorusHomeomorph j).symm 0)) :
    mappingTorusKernelZeroEquiv j a = torusH0Coordinates a := rfl

/-- The actual degree-zero coinvariants have the same augmentation marking. -/
def mappingTorusCokernelZeroEquiv (j : Kind) :
    (SingularHomology (ProductTorus 3) 0 ⧸
      LinearMap.range (wangDifference (fibreTorusHomeomorph j).symm 0)) ≃ₗ[ℤ] ℤ := by
  letI := Submodule.Quotient.module
    (LinearMap.range (wangDifference (fibreTorusHomeomorph j).symm 0))
  exact ((Submodule.quotEquivOfEqBot
    (LinearMap.range (wangDifference (fibreTorusHomeomorph j).symm 0))
    (by rw [mappingTorusDifference_zero, LinearMap.range_zero])).toAddEquiv.trans
      torusH0Coordinates.toAddEquiv).toIntLinearEquiv

@[simp] theorem mappingTorusCokernelZeroEquiv_mk (j : Kind)
    (a : SingularHomology (ProductTorus 3) 0) :
    mappingTorusCokernelZeroEquiv j (Submodule.Quotient.mk a) = torusH0Coordinates a := rfl

/-- The actual zeroth singular homology of the mapping torus is `ℤ`. -/
def mappingTorusH0Equiv (j : Kind) :
    SingularHomology (mappingTorusModel j) 0 ≃ₗ[ℤ] ℤ :=
  (degreeZeroHomologyEquiv (fibreTorusHomeomorph j).symm).trans
    (mappingTorusCokernelZeroEquiv j)

/-- Fibre inclusion preserves the literal positive augmentation coordinate. -/
theorem mappingTorusH0Equiv_fibre (j : Kind)
    (a : SingularHomology (ProductTorus 3) 0) :
    mappingTorusH0Equiv j (fibreHomologyMap (fibreTorusHomeomorph j).symm 0 a) =
      torusH0Coordinates a := by
  change mappingTorusCokernelZeroEquiv j
    ((degreeZeroHomologyEquiv (fibreTorusHomeomorph j).symm)
      ((degreeZeroHomologyEquiv (fibreTorusHomeomorph j).symm).symm
        (Submodule.Quotient.mk a))) = _
  rw [LinearEquiv.apply_symm_apply, mappingTorusCokernelZeroEquiv_mk]

/-- The actual point class in the fibre has positive coordinate one. -/
@[simp] theorem mappingTorusH0Equiv_fibre_pointClass (j : Kind) (x : ProductTorus 3) :
    mappingTorusH0Equiv j
      (pointClass (MappingTorus.HomologyCover.fibreInclusion
        (fibreTorusHomeomorph j).symm x)) = 1 := by
  have h := mappingTorusH0Equiv_fibre j (pointClass x)
  simpa only [fibreHomologyMap, singularHomologyMap_pointClass,
    torusH0Coordinates_pointClass] using h

/-- The inverse degree-zero marking is the integral multiple of an
actual positive point class, not an abstract chosen generator. -/
theorem mappingTorusH0Equiv_symm_apply (j : Kind) (n : ℤ) (x : ProductTorus 3) :
    (mappingTorusH0Equiv j).symm n =
      n • pointClass (MappingTorus.HomologyCover.fibreInclusion
        (fibreTorusHomeomorph j).symm x) := by
  apply (mappingTorusH0Equiv j).injective
  rw [LinearEquiv.apply_symm_apply, map_zsmul, mappingTorusH0Equiv_fibre_pointClass,
    zsmul_eq_mul, mul_one]
  simp

/-- The first actual short exact Wang extension gives integral two-coordinates. -/
def mappingTorusH1Equiv (j : Kind) :
    SingularHomology (mappingTorusModel j) 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  shortExtensionFinTwoEquivOfEndpoints
    (cokernelInclusion (fibreTorusHomeomorph j).symm 1)
    (kernelBoundary (fibreTorusHomeomorph j).symm 0)
    (mappingTorusCokernelOneEquiv j) (mappingTorusKernelZeroEquiv j)
    (cokernelInclusion_injective _ _) (kernelBoundary_surjective _ _)
    (cokernelInclusion_range_eq_ker_kernelBoundary _ _)

/-- The second coordinate is the actual signed Wang boundary,
measured in the positive point-class marking. -/
theorem mappingTorusH1Equiv_boundary (j : Kind)
    (a : SingularHomology (mappingTorusModel j) 1) :
    mappingTorusH1Equiv j a 1 =
      torusH0Coordinates (wangBoundary (fibreTorusHomeomorph j).symm 0 a) := by
  exact shortExtensionFinTwoEquivOfEndpoints_one _ _ _ _ _ _ _ a

/-- A genuine fibre one-class maps to the first coordinate axis with
the proved integral coinvariant coordinate. -/
theorem mappingTorusH1Equiv_fibre (j : Kind)
    (a : SingularHomology (ProductTorus 3) 1) :
    mappingTorusH1Equiv j (fibreHomologyMap (fibreTorusHomeomorph j).symm 1 a) =
      ![fibreCoinvariantCoordinate j (torusH1Equiv a), 0] := by
  change mappingTorusH1Equiv j
    (cokernelInclusion (fibreTorusHomeomorph j).symm 1 (Submodule.Quotient.mk a)) = _
  rw [mappingTorusH1Equiv, shortExtensionFinTwoEquivOfEndpoints_inclusion,
    mappingTorusCokernelOneEquiv_mk]

theorem mappingTorus_h0_finrank (j : Kind) :
    Module.finrank ℤ (SingularHomology (mappingTorusModel j) 0) = 1 := by
  rw [(mappingTorusH0Equiv j).finrank_eq]
  simp

theorem mappingTorus_h1_finrank (j : Kind) :
    Module.finrank ℤ (SingularHomology (mappingTorusModel j) 1) = 2 := by
  rw [(mappingTorusH1Equiv j).finrank_eq]
  simp

end Wikipedia.HopfProblem.Elliptic.HigherHomology
