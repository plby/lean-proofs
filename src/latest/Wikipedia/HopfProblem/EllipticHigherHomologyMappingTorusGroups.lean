import Wikipedia.HopfProblem.EllipticHigherHomologyMappingTorusMonodromy
import Wikipedia.HopfProblem.EllipticHigherHomologyMappingTorusDimension
import Wikipedia.HopfProblem.EllipticHigherHomologyEquivalenceConjugacy
import Wikipedia.HopfProblem.EllipticHigherHomologyEquivalenceExtension

/-!
# Integral higher homology of the actual elliptic mapping tori

The genuine singular Wang sequence, the actual coordinate-loop and
exterior-product markings of the three-torus, and the proved integral
kernel/cokernel calculations give explicit linear equivalences for the
actual homology groups.  The splitting in degrees two and three chooses
one preimage of the positive Wang-boundary generator.  Its other axis is
the genuine fibre-inclusion map, so the equivalences retain that map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology MappingTorusHomology

/-- Actual first-homology monodromy invariants have one integral coordinate. -/
def mappingTorusKernelOneEquiv (j : Kind) :
    LinearMap.ker (wangDifference (fibreTorusHomeomorph j).symm 1) ≃ₗ[ℤ] ℤ :=
  (conjugacyKernelEquiv torusH1Equiv _ _ (mappingTorusDifference_one j)).trans
    (fibreInverseKernelEquivInt j)

@[simp] theorem mappingTorusKernelOneEquiv_apply (j : Kind)
    (a : LinearMap.ker (wangDifference (fibreTorusHomeomorph j).symm 1)) :
    mappingTorusKernelOneEquiv j a = torusH1Equiv a 2 := rfl

/-- Actual first-homology monodromy coinvariants have one integral coordinate. -/
def mappingTorusCokernelOneEquiv (j : Kind) :
    (SingularHomology (ProductTorus 3) 1 ⧸
      LinearMap.range (wangDifference (fibreTorusHomeomorph j).symm 1)) ≃ₗ[ℤ] ℤ :=
  (conjugacyCokernelEquiv torusH1Equiv _ _ (mappingTorusDifference_one j)).trans
    (fibreInverseCokernelEquivInt j)

@[simp] theorem mappingTorusCokernelOneEquiv_mk (j : Kind)
    (a : SingularHomology (ProductTorus 3) 1) :
    mappingTorusCokernelOneEquiv j (Submodule.Quotient.mk a) =
      fibreCoinvariantCoordinate j (torusH1Equiv a) := rfl

/-- Actual second-homology monodromy invariants have one integral coordinate. -/
def mappingTorusKernelTwoEquiv (j : Kind) :
    LinearMap.ker (wangDifference (fibreTorusHomeomorph j).symm 2) ≃ₗ[ℤ] ℤ :=
  (conjugacyKernelEquiv torusH2Coordinates _ _ (mappingTorusDifference_two j)).trans
    (fibreSquareInverseKernelEquivInt j)

@[simp] theorem mappingTorusKernelTwoEquiv_apply (j : Kind)
    (a : LinearMap.ker (wangDifference (fibreTorusHomeomorph j).symm 2)) :
    mappingTorusKernelTwoEquiv j a = -(torusH2Coordinates a 1) := rfl

/-- Actual second-homology monodromy coinvariants have one integral coordinate. -/
def mappingTorusCokernelTwoEquiv (j : Kind) :
    (SingularHomology (ProductTorus 3) 2 ⧸
      LinearMap.range (wangDifference (fibreTorusHomeomorph j).symm 2)) ≃ₗ[ℤ] ℤ :=
  (conjugacyCokernelEquiv torusH2Coordinates _ _ (mappingTorusDifference_two j)).trans
    (fibreSquareInverseCokernelEquivInt j)

@[simp] theorem mappingTorusCokernelTwoEquiv_mk (j : Kind)
    (a : SingularHomology (ProductTorus 3) 2) :
    mappingTorusCokernelTwoEquiv j (Submodule.Quotient.mk a) =
      torusH2Coordinates a 0 := rfl

/-- The actual positive fibre orientation identifies the degree-three invariants. -/
def mappingTorusKernelThreeEquiv (j : Kind) :
    LinearMap.ker (wangDifference (fibreTorusHomeomorph j).symm 3) ≃ₗ[ℤ] ℤ := by
  letI := (LinearMap.ker (wangDifference (fibreTorusHomeomorph j).symm 3)).module
  letI := (⊤ : Submodule ℤ (SingularHomology (ProductTorus 3) 3)).module
  exact (((LinearEquiv.ofEq (LinearMap.ker (wangDifference (fibreTorusHomeomorph j).symm 3))
    (⊤ : Submodule ℤ (SingularHomology (ProductTorus 3) 3))
    (by rw [mappingTorusDifference_three, LinearMap.ker_zero])).toAddEquiv.trans
    Submodule.topEquiv.toAddEquiv).trans torusH3Coordinates.toAddEquiv).toIntLinearEquiv

@[simp] theorem mappingTorusKernelThreeEquiv_apply (j : Kind)
    (a : LinearMap.ker (wangDifference (fibreTorusHomeomorph j).symm 3)) :
    mappingTorusKernelThreeEquiv j a = torusH3Coordinates a := rfl

/-- The actual positive fibre orientation identifies the degree-three coinvariants. -/
def mappingTorusCokernelThreeEquiv (j : Kind) :
    (SingularHomology (ProductTorus 3) 3 ⧸
      LinearMap.range (wangDifference (fibreTorusHomeomorph j).symm 3)) ≃ₗ[ℤ] ℤ := by
  letI := Submodule.Quotient.module
    (LinearMap.range (wangDifference (fibreTorusHomeomorph j).symm 3))
  exact ((Submodule.quotEquivOfEqBot
    (LinearMap.range (wangDifference (fibreTorusHomeomorph j).symm 3))
    (by rw [mappingTorusDifference_three, LinearMap.range_zero])).toAddEquiv.trans
      torusH3Coordinates.toAddEquiv).toIntLinearEquiv

@[simp] theorem mappingTorusCokernelThreeEquiv_mk (j : Kind)
    (a : SingularHomology (ProductTorus 3) 3) :
    mappingTorusCokernelThreeEquiv j (Submodule.Quotient.mk a) =
      torusH3Coordinates a := rfl

/-- The actual second singular homology is integrally free of rank two. -/
def mappingTorusH2Equiv (j : Kind) :
    SingularHomology (mappingTorusModel j) 2 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  shortExtensionFinTwoEquivOfEndpoints
    (cokernelInclusion (fibreTorusHomeomorph j).symm 2)
    (kernelBoundary (fibreTorusHomeomorph j).symm 1)
    (mappingTorusCokernelTwoEquiv j) (mappingTorusKernelOneEquiv j)
    (cokernelInclusion_injective _ _) (kernelBoundary_surjective _ _)
    (cokernelInclusion_range_eq_ker_kernelBoundary _ _)

/-- Its second coordinate is the actual signed Wang boundary in the positive invariant axis. -/
theorem mappingTorusH2Equiv_boundary (j : Kind)
    (a : SingularHomology (mappingTorusModel j) 2) :
    mappingTorusH2Equiv j a 1 =
      torusH1Equiv (wangBoundary (fibreTorusHomeomorph j).symm 1 a) 2 := by
  exact shortExtensionFinTwoEquivOfEndpoints_one _ _ _ _ _ _ _ a

/-- The actual inclusion of a fibre two-class is the oriented first axis. -/
theorem mappingTorusH2Equiv_fibre (j : Kind)
    (a : SingularHomology (ProductTorus 3) 2) :
    mappingTorusH2Equiv j (fibreHomologyMap (fibreTorusHomeomorph j).symm 2 a) =
      ![torusH2Coordinates a 0, 0] := by
  change mappingTorusH2Equiv j
    (cokernelInclusion (fibreTorusHomeomorph j).symm 2 (Submodule.Quotient.mk a)) = _
  rw [mappingTorusH2Equiv, shortExtensionFinTwoEquivOfEndpoints_inclusion,
    mappingTorusCokernelTwoEquiv_mk]

/-- The actual third singular homology is integrally free of rank two. -/
def mappingTorusH3Equiv (j : Kind) :
    SingularHomology (mappingTorusModel j) 3 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  shortExtensionFinTwoEquivOfEndpoints
    (cokernelInclusion (fibreTorusHomeomorph j).symm 3)
    (kernelBoundary (fibreTorusHomeomorph j).symm 2)
    (mappingTorusCokernelThreeEquiv j) (mappingTorusKernelTwoEquiv j)
    (cokernelInclusion_injective _ _) (kernelBoundary_surjective _ _)
    (cokernelInclusion_range_eq_ker_kernelBoundary _ _)

/-- Its second coordinate is the normalized actual Wang boundary. -/
theorem mappingTorusH3Equiv_boundary (j : Kind)
    (a : SingularHomology (mappingTorusModel j) 3) :
    mappingTorusH3Equiv j a 1 =
      -(torusH2Coordinates (wangBoundary (fibreTorusHomeomorph j).symm 2 a) 1) := by
  exact shortExtensionFinTwoEquivOfEndpoints_one _ _ _ _ _ _ _ a

/-- The actual positive fibre orientation is the first third-homology axis. -/
theorem mappingTorusH3Equiv_fibre (j : Kind)
    (a : SingularHomology (ProductTorus 3) 3) :
    mappingTorusH3Equiv j (fibreHomologyMap (fibreTorusHomeomorph j).symm 3 a) =
      ![torusH3Coordinates a, 0] := by
  change mappingTorusH3Equiv j
    (cokernelInclusion (fibreTorusHomeomorph j).symm 3 (Submodule.Quotient.mk a)) = _
  rw [mappingTorusH3Equiv, shortExtensionFinTwoEquivOfEndpoints_inclusion,
    mappingTorusCokernelThreeEquiv_mk]

/-- In top degree the actual Wang boundary is injective, since the fibre has no fourth homology. -/
theorem mappingTorusKernelBoundary_three_injective (j : Kind) :
    Function.Injective (kernelBoundary (fibreTorusHomeomorph j).symm 3) := by
  have := productTorus_homology_subsingleton_of_lt (show 3 < 4 by decide)
  intro a b hab
  have hzero : wangBoundary (fibreTorusHomeomorph j).symm 3 (a - b) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val hab)
  have hmem : a - b ∈ LinearMap.ker (wangBoundary (fibreTorusHomeomorph j).symm 3) :=
    hzero
  rw [← wang_exact_at_mappingTorus] at hmem
  obtain ⟨v, hv⟩ := hmem
  have hv0 : v = 0 := Subsingleton.elim _ _
  rw [hv0, map_zero] at hv
  exact sub_eq_zero.mp hv.symm

/-- Actual fourth homology is the integral orientation group. -/
def mappingTorusH4Equiv (j : Kind) :
    SingularHomology (mappingTorusModel j) 4 ≃ₗ[ℤ] ℤ :=
  (LinearEquiv.ofBijective (kernelBoundary (fibreTorusHomeomorph j).symm 3)
    ⟨mappingTorusKernelBoundary_three_injective j, kernelBoundary_surjective _ _⟩).trans
      (mappingTorusKernelThreeEquiv j)

/-- The actual signed Wang boundary fixes the integral top-degree marking. -/
theorem mappingTorusH4Equiv_boundary (j : Kind)
    (a : SingularHomology (mappingTorusModel j) 4) :
    mappingTorusH4Equiv j a =
      torusH3Coordinates (wangBoundary (fibreTorusHomeomorph j).symm 3 a) := rfl

theorem mappingTorus_h2_finrank (j : Kind) :
    Module.finrank ℤ (SingularHomology (mappingTorusModel j) 2) = 2 := by
  rw [(mappingTorusH2Equiv j).finrank_eq]
  simp

theorem mappingTorus_h3_finrank (j : Kind) :
    Module.finrank ℤ (SingularHomology (mappingTorusModel j) 3) = 2 := by
  rw [(mappingTorusH3Equiv j).finrank_eq]
  simp

theorem mappingTorus_h4_finrank (j : Kind) :
    Module.finrank ℤ (SingularHomology (mappingTorusModel j) 4) = 1 := by
  rw [(mappingTorusH4Equiv j).finrank_eq]
  simp

end Wikipedia.HopfProblem.Elliptic.HigherHomology
