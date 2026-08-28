import Wikipedia.HopfProblem.ThreefoldHomologyCuspKernelFibre

/-!
# The actual cusp-cap kernel is the genuine Wang invariant group

The original cap and Wang coefficients jointly detect every native
boundary class.  Restricting Wang to the actual cap kernel is therefore
injective.  Surjectivity follows by subtracting from any Wang lift the
unique coinvariant fibre class with the same original cap image.

All maps are the original fixed-radius cusp attachment maps.  The
inverse is canonical through the proved actual fibre-coinvariant
equivalence, not a prescribed boundary matrix or an assumed splitting.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThreefoldHomologyCuspFibre

open SingularMayerVietoris MappingTorusHomology ThreefoldOverlapMappingTorus
open PeriodTorusHigherHomology SpecialPeriods.Threefold
open SpecialPeriods.Threefold.Homology

local notation "f₀" => ThreefoldOverlapMappingTorus.monodromy none

/-- The actual cap and actual Wang coefficients jointly detect a native boundary class. -/
theorem cuspCap_wang_eq_zero (n : ℕ) (a : SingularHomology (Boundary none) (n + 1))
    (hcap : boundaryFillingHomologyMap none (n + 1) a = 0)
    (hwang : wangBoundary f₀ n a = 0) : a = 0 := by
  have ha : a ∈ LinearMap.range (fibreHomologyMap f₀ (n + 1)) := by
    rw [wang_exact_at_mappingTorus f₀ n]
    exact hwang
  obtain ⟨b, rfl⟩ := ha
  apply (fibreToFilling_cusp_eq_zero_iff_fibreHomologyMap_eq_zero (n + 1) b).mp
  exact (LinearMap.congr_fun (boundaryFillingHomologyMap_fibre none (n + 1)) b).symm.trans hcap

theorem cuspCap_wang_ext (n : ℕ) (a b : SingularHomology (Boundary none) (n + 1))
    (hcap : boundaryFillingHomologyMap none (n + 1) a =
      boundaryFillingHomologyMap none (n + 1) b)
    (hwang : wangBoundary f₀ n a = wangBoundary f₀ n b) : a = b := by
  apply sub_eq_zero.mp
  apply cuspCap_wang_eq_zero n (a - b)
  · rw [map_sub, hcap, sub_self]
  · rw [map_sub, hwang, sub_self]

theorem cuspCap_wang_joint_injective (n : ℕ) :
    Function.Injective (fun a : SingularHomology (Boundary none) (n + 1) =>
      (boundaryFillingHomologyMap none (n + 1) a, wangBoundary f₀ n a)) := by
  intro a b hab
  exact cuspCap_wang_ext n a b (congrArg Prod.fst hab) (congrArg Prod.snd hab)

/-- The genuine kernel-valued Wang map, restricted to the actual original cap kernel. -/
def cuspCapKernelWangDegreeMap (n : ℕ) :
    LinearMap.ker (boundaryFillingHomologyMap none (n + 1)) →ₗ[ℤ]
      LinearMap.ker (wangDifference f₀ n) :=
  intLinearMapOfAddHom
    { toFun a := kernelBoundary f₀ n a.val
      map_zero' := (kernelBoundary f₀ n).map_zero
      map_add' a b := (kernelBoundary f₀ n).map_add a.val b.val }

@[simp] theorem cuspCapKernelWangDegreeMap_apply (n : ℕ)
    (a : LinearMap.ker (boundaryFillingHomologyMap none (n + 1))) :
    cuspCapKernelWangDegreeMap n a = kernelBoundary f₀ n a.val := rfl

@[simp] theorem cuspCapKernelWangDegreeMap_val (n : ℕ)
    (a : LinearMap.ker (boundaryFillingHomologyMap none (n + 1))) :
    (cuspCapKernelWangDegreeMap n a).val = wangBoundary f₀ n a.val := rfl

theorem cuspCapKernelWangDegreeMap_injective (n : ℕ) :
    Function.Injective (cuspCapKernelWangDegreeMap n) := by
  intro a b hab
  apply Subtype.ext
  apply cuspCap_wang_ext n a.val b.val
  · exact a.property.trans b.property.symm
  · exact congrArg Subtype.val hab

/-- Original Wang exactness kills the genuine coinvariant fibre inclusion. -/
theorem cuspWang_cokernelInclusion_zero (n : ℕ) (a : CuspWangCokernel (n + 1)) :
    wangBoundary f₀ n (cokernelInclusion f₀ (n + 1) a) = 0 := by
  have ha : cokernelInclusion f₀ (n + 1) a ∈
      LinearMap.range (cokernelInclusion f₀ (n + 1)) := ⟨a, rfl⟩
  rw [cokernelInclusion_range_eq_ker_kernelBoundary f₀ n] at ha
  exact congrArg Subtype.val ha

/-- Subtract the unique genuine coinvariant fibre class with the same original cap image. -/
def cuspCapCorrectionDegree (n : ℕ) (a : SingularHomology (Boundary none) (n + 1)) :
    LinearMap.ker (boundaryFillingHomologyMap none (n + 1)) :=
  ⟨a - cokernelInclusion f₀ (n + 1)
      ((cuspFibreCoinvariantEquiv (n + 1)).symm (boundaryFillingHomologyMap none (n + 1) a)), by
    change boundaryFillingHomologyMap none (n + 1) (a - _) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr
      ((cuspFibreCoinvariantEquiv (n + 1)).apply_symm_apply
        (boundaryFillingHomologyMap none (n + 1) a)).symm⟩

@[simp] theorem cuspCapCorrectionDegree_val (n : ℕ)
    (a : SingularHomology (Boundary none) (n + 1)) :
    (cuspCapCorrectionDegree n a).val =
      a - cokernelInclusion f₀ (n + 1)
        ((cuspFibreCoinvariantEquiv (n + 1)).symm
          (boundaryFillingHomologyMap none (n + 1) a)) := rfl

/-- The canonical fibre correction leaves the original actual Wang value unchanged. -/
theorem cuspCapCorrectionDegree_wang (n : ℕ)
    (a : SingularHomology (Boundary none) (n + 1)) :
    cuspCapKernelWangDegreeMap n (cuspCapCorrectionDegree n a) = kernelBoundary f₀ n a := by
  apply Subtype.ext
  change wangBoundary f₀ n (a - cokernelInclusion f₀ (n + 1) _) = wangBoundary f₀ n a
  rw [map_sub, cuspWang_cokernelInclusion_zero, sub_zero]

theorem cuspCapKernelWangDegreeMap_surjective (n : ℕ) :
    Function.Surjective (cuspCapKernelWangDegreeMap n) := by
  intro a
  obtain ⟨b, hb⟩ := kernelBoundary_surjective f₀ n a
  exact ⟨cuspCapCorrectionDegree n b, (cuspCapCorrectionDegree_wang n b).trans hb⟩

/-- In every positive boundary degree the actual cap kernel is exactly
the actual Wang invariants. -/
def cuspCapKernelWangEquivDegree (n : ℕ) :
    LinearMap.ker (boundaryFillingHomologyMap none (n + 1)) ≃ₗ[ℤ]
      LinearMap.ker (wangDifference f₀ n) :=
  LinearEquiv.ofBijective (cuspCapKernelWangDegreeMap n)
    ⟨cuspCapKernelWangDegreeMap_injective n, cuspCapKernelWangDegreeMap_surjective n⟩

@[simp] theorem cuspCapKernelWangEquivDegree_apply (n : ℕ)
    (a : LinearMap.ker (boundaryFillingHomologyMap none (n + 1))) :
    cuspCapKernelWangEquivDegree n a = kernelBoundary f₀ n a.val := rfl

/-- The forward equivalence is literally the signed native Wang boundary. -/
@[simp] theorem cuspCapKernelWangEquivDegree_apply_val (n : ℕ)
    (a : LinearMap.ker (boundaryFillingHomologyMap none (n + 1))) :
    (cuspCapKernelWangEquivDegree n a).val = wangBoundary f₀ n a.val := rfl

/-- The inverse realizes the specified actual invariant class. -/
@[simp] theorem cuspCapKernelWangEquivDegree_symm_wang (n : ℕ)
    (a : LinearMap.ker (wangDifference f₀ n)) :
    wangBoundary f₀ n ((cuspCapKernelWangEquivDegree n).symm a).val = a.val :=
  congrArg Subtype.val ((cuspCapKernelWangEquivDegree n).apply_symm_apply a)

/-- Its cap image is zero in the original full fixed-radius filling. -/
@[simp] theorem cuspCapKernelWangEquivDegree_symm_cap (n : ℕ)
    (a : LinearMap.ker (wangDifference f₀ n)) :
    boundaryFillingHomologyMap none (n + 1)
      ((cuspCapKernelWangEquivDegree n).symm a).val = 0 :=
  ((cuspCapKernelWangEquivDegree n).symm a).property

/-- Any actual Wang lift gives the canonical inverse after its actual fibre correction. -/
theorem cuspCapKernelWangEquivDegree_symm_kernelBoundary (n : ℕ)
    (a : SingularHomology (Boundary none) (n + 1)) :
    ((cuspCapKernelWangEquivDegree n).symm (kernelBoundary f₀ n a)).val =
      a - cokernelInclusion f₀ (n + 1)
        ((cuspFibreCoinvariantEquiv (n + 1)).symm
          (boundaryFillingHomologyMap none (n + 1) a)) := by
  have h : (cuspCapKernelWangEquivDegree n).symm (kernelBoundary f₀ n a) =
      cuspCapCorrectionDegree n a := by
    apply (cuspCapKernelWangEquivDegree n).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (cuspCapCorrectionDegree_wang n a).symm
  exact congrArg Subtype.val h

/-- The same joint detection holds on the literal original gluing overlap. -/
theorem cuspOverlap_cap_wang_eq_zero (n : ℕ)
    (a : SingularHomology (RegularOverlap none) (n + 1))
    (hcap : singularHomologyMap (overlapToFilling none) (n + 1) a = 0)
    (hwang : wangBoundary f₀ n (overlapHomologyEquiv none (n + 1) a) = 0) : a = 0 := by
  apply (overlapHomologyEquiv none (n + 1)).injective
  rw [map_zero]
  apply cuspCap_wang_eq_zero n _ ?_ hwang
  exact (LinearMap.congr_fun (boundaryFillingHomologyMap_retraction none (n + 1)) a).trans hcap

end Wikipedia.HopfProblem.ThreefoldHomologyCuspFibre
