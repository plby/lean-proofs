import Wikipedia.HopfProblem.ThreefoldHomologyCuspFibre
import Wikipedia.HopfProblem.MappingTorusHomology
import Wikipedia.HopfProblem.ThreefoldHomologyFreeProducts
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroupsPeriod

/-!
# The fourth cusp-cap kernel in actual Wang coordinates

The actual fibre-to-cap map in degree four is surjective between two
proved free integral modules of rank one, hence bijective.  Restricting
the genuine degree-three Wang boundary to the kernel of the actual
boundary-to-cap map is then an integral equivalence onto its actual
invariant group.  Any Wang lift is corrected by subtracting the unique
fibre class with the same cap image.

The forward map remains exactly the signed Wang map.  No formula for a
regular-family coefficient, nor any residual scalar factor, is asserted.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThreefoldHomologyCuspFibre

open SpecialPeriods SpecialPeriods.Threefold SingularMayerVietoris
open PeriodTorusHigherHomology MappingTorusHomology ThreefoldOverlapMappingTorus
open ThreefoldHomologyFinitenessCusp

local notation "f₀" => ThreefoldOverlapMappingTorus.monodromy none

/-- The literal cusp fibre-to-filling map is bijective in degree four. -/
theorem fibreToFilling_four_bijective :
    Function.Bijective (singularHomologyMap (fibreToFilling none) 4) := by
  have := realTorus_homology_free 4
  have := realTorus_homology_finite 4
  have : Module.Free ℤ (SingularHomology (localPiece (some none)) 4) :=
    fullHomology_free Cusp.specialData 4
  have : Module.Finite ℤ (SingularHomology (localPiece (some none)) 4) :=
    fullHomology_finite Cusp.specialData 4
  have hcap : Module.finrank ℤ (SingularHomology (localPiece (some none)) 4) = 1 :=
    fullHomology_finrank Cusp.specialData 4
  apply OrzechProperty.bijective_of_surjective_of_finrank_le
    (singularHomologyMap (fibreToFilling none) 4) (fibreToFilling_homology_surjective 4)
  rw [realTorus_homology_finrank, hcap]
  decide

/-- The original fibre map, as the proved fourth-homology equivalence. -/
def cuspFibreFourEquiv :
    SingularHomology RealTorus₄ 4 ≃ₗ[ℤ] SingularHomology (localPiece (some none)) 4 :=
  LinearEquiv.ofBijective (singularHomologyMap (fibreToFilling none) 4)
    fibreToFilling_four_bijective

@[simp] theorem cuspFibreFourEquiv_toLinearMap :
    cuspFibreFourEquiv.toLinearMap = singularHomologyMap (fibreToFilling none) 4 := rfl

@[simp] theorem cuspFibreFourEquiv_apply (a : SingularHomology RealTorus₄ 4) :
    cuspFibreFourEquiv a = singularHomologyMap (fibreToFilling none) 4 a := rfl

/-- The two original inclusions compose to the actual fibre-to-cap equivalence. -/
theorem cuspCap_four_fibre (a : SingularHomology RealTorus₄ 4) :
    boundaryFillingHomologyMap none 4 (fibreHomologyMap f₀ 4 a) = cuspFibreFourEquiv a :=
  LinearMap.congr_fun (boundaryFillingHomologyMap_fibre none 4) a

/-- Genuine Wang exactness kills the original fibre image. -/
theorem cuspWang_three_fibre_four (a : SingularHomology RealTorus₄ 4) :
    wangBoundary f₀ 3 (fibreHomologyMap f₀ 4 a) = 0 := by
  have ha : fibreHomologyMap f₀ 4 a ∈ LinearMap.range (fibreHomologyMap f₀ 4) := ⟨a, rfl⟩
  rw [wang_exact_at_mappingTorus f₀ 3] at ha
  exact ha

/-- The actual cap image and actual Wang image jointly detect a boundary class. -/
theorem cuspCap_wang_four_eq_zero (a : SingularHomology (Boundary none) 4)
    (hcap : boundaryFillingHomologyMap none 4 a = 0)
    (hwang : wangBoundary f₀ 3 a = 0) : a = 0 := by
  have ha : a ∈ LinearMap.range (fibreHomologyMap f₀ 4) := by
    rw [wang_exact_at_mappingTorus f₀ 3]
    exact hwang
  obtain ⟨b, hb⟩ := ha
  have hb0 : cuspFibreFourEquiv b = 0 :=
    (cuspCap_four_fibre b).symm.trans
      ((congrArg (boundaryFillingHomologyMap none 4) hb).trans hcap)
  have hb' : b = 0 := cuspFibreFourEquiv.injective (hb0.trans cuspFibreFourEquiv.map_zero.symm)
  rw [hb', map_zero] at hb
  exact hb.symm

theorem cuspCap_wang_four_ext (a b : SingularHomology (Boundary none) 4)
    (hcap : boundaryFillingHomologyMap none 4 a = boundaryFillingHomologyMap none 4 b)
    (hwang : wangBoundary f₀ 3 a = wangBoundary f₀ 3 b) : a = b := by
  apply sub_eq_zero.mp
  apply cuspCap_wang_four_eq_zero (a - b)
  · rw [map_sub, hcap, sub_self]
  · rw [map_sub, hwang, sub_self]

theorem cuspCap_wang_four_joint_injective :
    Function.Injective (fun a : SingularHomology (Boundary none) 4 =>
      (boundaryFillingHomologyMap none 4 a, wangBoundary f₀ 3 a)) := by
  intro a b hab
  exact cuspCap_wang_four_ext a b (congrArg Prod.fst hab) (congrArg Prod.snd hab)

/-- Restrict the actual kernel-valued Wang map to the actual cap kernel. -/
def cuspCapKernelWangMap :
    LinearMap.ker (boundaryFillingHomologyMap none 4) →ₗ[ℤ]
      LinearMap.ker (wangDifference f₀ 3) :=
  intLinearMapOfAddHom
    { toFun a := kernelBoundary f₀ 3 a.val
      map_zero' := (kernelBoundary f₀ 3).map_zero
      map_add' a b := (kernelBoundary f₀ 3).map_add a.val b.val }

@[simp] theorem cuspCapKernelWangMap_apply
    (a : LinearMap.ker (boundaryFillingHomologyMap none 4)) :
    cuspCapKernelWangMap a = kernelBoundary f₀ 3 a.val := rfl

@[simp] theorem cuspCapKernelWangMap_val
    (a : LinearMap.ker (boundaryFillingHomologyMap none 4)) :
    (cuspCapKernelWangMap a).val = wangBoundary f₀ 3 a.val := rfl

theorem cuspCapKernelWangMap_injective : Function.Injective cuspCapKernelWangMap := by
  intro a b hab
  apply Subtype.ext
  apply cuspCap_wang_four_ext a.val b.val
  · exact a.property.trans b.property.symm
  · exact congrArg (fun x : LinearMap.ker (wangDifference f₀ 3) => x.val) hab

/-- Subtract the unique original fibre class with the same cap image. -/
def cuspCapCorrection (a : SingularHomology (Boundary none) 4) :
    LinearMap.ker (boundaryFillingHomologyMap none 4) :=
  ⟨a - fibreHomologyMap f₀ 4
      (cuspFibreFourEquiv.symm (boundaryFillingHomologyMap none 4 a)), by
    change boundaryFillingHomologyMap none 4 (a - _) = 0
    rw [map_sub, cuspCap_four_fibre, LinearEquiv.apply_symm_apply, sub_self]⟩

@[simp] theorem cuspCapCorrection_val (a : SingularHomology (Boundary none) 4) :
    (cuspCapCorrection a).val = a - fibreHomologyMap f₀ 4
      (cuspFibreFourEquiv.symm (boundaryFillingHomologyMap none 4 a)) := rfl

/-- Correcting the cap image leaves the genuine Wang value unchanged. -/
theorem cuspCapCorrection_wang (a : SingularHomology (Boundary none) 4) :
    cuspCapKernelWangMap (cuspCapCorrection a) = kernelBoundary f₀ 3 a := by
  apply Subtype.ext
  change wangBoundary f₀ 3 (a - fibreHomologyMap f₀ 4 _) = wangBoundary f₀ 3 a
  rw [map_sub, cuspWang_three_fibre_four, sub_zero]

theorem cuspCapKernelWangMap_surjective : Function.Surjective cuspCapKernelWangMap := by
  intro y
  obtain ⟨a, ha⟩ := kernelBoundary_surjective f₀ 3 y
  exact ⟨cuspCapCorrection a, (cuspCapCorrection_wang a).trans ha⟩

/-- The cap kernel is canonically the actual degree-three Wang invariant group. -/
def cuspCapKernelWangEquiv :
    LinearMap.ker (boundaryFillingHomologyMap none 4) ≃ₗ[ℤ]
      LinearMap.ker (wangDifference f₀ 3) :=
  LinearEquiv.ofBijective cuspCapKernelWangMap
    ⟨cuspCapKernelWangMap_injective, cuspCapKernelWangMap_surjective⟩

/-- The equivalence is literally the actual kernel-valued Wang boundary. -/
@[simp] theorem cuspCapKernelWangEquiv_apply
    (a : LinearMap.ker (boundaryFillingHomologyMap none 4)) :
    cuspCapKernelWangEquiv a = kernelBoundary f₀ 3 a.val := rfl

@[simp] theorem cuspCapKernelWangEquiv_apply_val
    (a : LinearMap.ker (boundaryFillingHomologyMap none 4)) :
    (cuspCapKernelWangEquiv a).val = wangBoundary f₀ 3 a.val := rfl

/-- The inverse has precisely the prescribed actual Wang value. -/
@[simp] theorem cuspCapKernelWangEquiv_symm_wang
    (a : LinearMap.ker (wangDifference f₀ 3)) :
    wangBoundary f₀ 3 (cuspCapKernelWangEquiv.symm a).val = a.val :=
  congrArg Subtype.val (cuspCapKernelWangEquiv.apply_symm_apply a)

/-- The inverse lies in the kernel of the original cap coefficient. -/
@[simp] theorem cuspCapKernelWangEquiv_symm_cap
    (a : LinearMap.ker (wangDifference f₀ 3)) :
    boundaryFillingHomologyMap none 4 (cuspCapKernelWangEquiv.symm a).val = 0 :=
  (cuspCapKernelWangEquiv.symm a).property

/-- Any actual Wang lift gives the same inverse after its unique fibre correction. -/
theorem cuspCapKernelWangEquiv_symm_kernelBoundary (a : SingularHomology (Boundary none) 4) :
    (cuspCapKernelWangEquiv.symm (kernelBoundary f₀ 3 a)).val =
      a - fibreHomologyMap f₀ 4
        (cuspFibreFourEquiv.symm (boundaryFillingHomologyMap none 4 a)) := by
  have he : cuspCapKernelWangEquiv.symm (kernelBoundary f₀ 3 a) = cuspCapCorrection a := by
    apply cuspCapKernelWangEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (cuspCapCorrection_wang a).symm
  exact congrArg Subtype.val he

end Wikipedia.HopfProblem.ThreefoldHomologyCuspFibre
