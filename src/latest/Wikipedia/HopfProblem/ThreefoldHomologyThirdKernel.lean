import Wikipedia.HopfProblem.ThreefoldHomologyThirdResidual
import Wikipedia.HopfProblem.ThreefoldHomologyFourthAttachment

/-!
# The actual fourth homology and the genuine third residual kernel

The original signed star kernel is transported through the actual
overlap homology equivalences to the kernel of the original native cap
relation map.  The exact source-kernel classification then identifies
this kernel with the annihilator of the actual residual integer.
Together with the genuine fourth-degree attachment isomorphism this
computes fourth homology without assuming the value of that integer.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdDegree

open SingularMayerVietoris PeriodTorusHigherHomology ThreefoldOverlapMappingTorus CapElimination

/-- A genuine signed star-kernel element is killed by the original filling coefficient. -/
def starKernelIntoCapKernel (n : ℕ) (a : LinearMap.ker (starLeftHomologyMap n)) :
    LinearMap.ker (starOverlapToFillingsHomologyMap n) :=
  ⟨a.val, by
    have h : -starOverlapToFillingsHomologyMap n a.val = 0 := congrArg Prod.snd a.property
    exact neg_eq_zero.mp h⟩

/-- Transport the actual signed star kernel through the original native overlap equivalences. -/
def starKernelToNative (n : ℕ) :
    LinearMap.ker (starLeftHomologyMap n) →ₗ[ℤ]
      LinearMap.ker (nativeCapKernelRegularMap n) :=
  intLinearMapOfAddHom
    { toFun a := ⟨nativeCapKernelEquiv n (starKernelIntoCapKernel n a), by
        change nativeCapKernelRegularMap n
          (nativeCapKernelEquiv n (starKernelIntoCapKernel n a)) = 0
        rw [nativeCapKernelRegularMap_equiv]
        exact congrArg Prod.fst a.property⟩
      map_zero' := by
        apply Subtype.ext
        exact (nativeCapKernelEquiv n).map_zero
      map_add' a b := by
        apply Subtype.ext
        exact (nativeCapKernelEquiv n).map_add
          (starKernelIntoCapKernel n a) (starKernelIntoCapKernel n b) }

@[simp] theorem starKernelToNative_val (n : ℕ)
    (a : LinearMap.ker (starLeftHomologyMap n)) :
    (starKernelToNative n a).val = nativeCapKernelEquiv n (starKernelIntoCapKernel n a) := rfl

theorem starKernelToNative_injective (n : ℕ) : Function.Injective (starKernelToNative n) := by
  intro a b hab
  apply Subtype.ext
  have h := (nativeCapKernelEquiv n).injective (congrArg Subtype.val hab)
  exact congrArg (fun c : LinearMap.ker (starOverlapToFillingsHomologyMap n) => c.val) h

theorem starKernelToNative_surjective (n : ℕ) : Function.Surjective (starKernelToNative n) := by
  intro a
  let b := (nativeCapKernelEquiv n).symm a.val
  have hreg : starOverlapToRegularHomologyMap n b.val = 0 := by
    have h := nativeCapKernelRegularMap_equiv n b
    change nativeCapKernelRegularMap n
      (nativeCapKernelEquiv n ((nativeCapKernelEquiv n).symm a.val)) = _ at h
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm.trans a.property
  refine ⟨⟨b.val, ?_⟩, ?_⟩
  · change starLeftHomologyMap n b.val = 0
    rw [starLeft_regular_fillings, hreg, b.property, neg_zero]
    rfl
  · apply Subtype.ext
    exact (nativeCapKernelEquiv n).apply_symm_apply a.val

/-- This equivalence retains the actual original boundary classes in its forward map. -/
def starKernelNativeEquiv (n : ℕ) :
    LinearMap.ker (starLeftHomologyMap n) ≃ₗ[ℤ]
      LinearMap.ker (nativeCapKernelRegularMap n) :=
  LinearEquiv.ofBijective (starKernelToNative n)
    ⟨starKernelToNative_injective n, starKernelToNative_surjective n⟩

@[simp] theorem starKernelNativeEquiv_toLinearMap (n : ℕ) :
    (starKernelNativeEquiv n).toLinearMap = starKernelToNative n := rfl

/-- Multiplication by the integer defined by the original full reference relation. -/
def residualMultiplication : ℤ →ₗ[ℤ] ℤ :=
  LinearMap.toSpanSingleton ℤ ℤ referenceFibreCoefficient

@[simp] theorem residualMultiplication_apply (k : ℤ) :
    residualMultiplication k = k * referenceFibreCoefficient := rfl

/-- Each integer in the genuine residual annihilator gives its original native reference tuple. -/
def residualKernelToNative :
    LinearMap.ker residualMultiplication →ₗ[ℤ]
      LinearMap.ker (nativeCapKernelRegularMap 3) :=
  intLinearMapOfAddHom
    { toFun a := ⟨a.val • referenceClasses, by
        change nativeCapKernelRegularMap 3 (a.val • referenceClasses) = 0
        rw [nativeCapKernelRegularMap_smul_reference]
        have ha : a.val * referenceFibreCoefficient = 0 := a.property
        rw [ha, map_zero]⟩
      map_zero' := by
        apply Subtype.ext
        exact zero_smul ℤ referenceClasses
      map_add' a b := by
        apply Subtype.ext
        exact add_smul a.val b.val referenceClasses }

@[simp] theorem residualKernelToNative_val (a : LinearMap.ker residualMultiplication) :
    (residualKernelToNative a).val = a.val • referenceClasses := rfl

theorem residualKernelToNative_injective : Function.Injective residualKernelToNative := by
  intro a b hab
  apply Subtype.ext
  exact ThirdSource.referenceClasses_smul_injective (congrArg Subtype.val hab)

theorem residualKernelToNative_surjective : Function.Surjective residualKernelToNative := by
  intro a
  obtain ⟨k, hk, hz⟩ := (nativeCapKernelRegularMap_three_eq_zero_iff a.val).mp a.property
  exact ⟨⟨k, hz⟩, Subtype.ext hk.symm⟩

/-- The exact original native relation kernel is the annihilator of its genuine residual integer. -/
def residualNativeKernelEquiv :
    LinearMap.ker residualMultiplication ≃ₗ[ℤ]
      LinearMap.ker (nativeCapKernelRegularMap 3) :=
  LinearEquiv.ofBijective residualKernelToNative
    ⟨residualKernelToNative_injective, residualKernelToNative_surjective⟩

@[simp] theorem residualNativeKernelEquiv_val (a : LinearMap.ker residualMultiplication) :
    (residualNativeKernelEquiv a).val = a.val • referenceClasses := rfl

/-- Actual fourth homology is exactly the integral annihilator of the original residual relation. -/
def homologyFourResidualKernelEquiv :
    SingularHomology Space 4 ≃ₗ[ℤ] LinearMap.ker residualMultiplication :=
  (FourthDegree.homologyFourKernelEquiv.toAddEquiv.trans
    ((starKernelNativeEquiv 3).toAddEquiv.trans
      residualNativeKernelEquiv.symm.toAddEquiv)).toIntLinearEquiv

/-- The actual fourth-homology coefficient, obtained from the genuine connecting map. -/
def homologyFourCoefficientMap : SingularHomology Space 4 →ₗ[ℤ] ℤ :=
  intLinearMapOfAddHom
    { toFun a := (homologyFourResidualKernelEquiv a).val
      map_zero' := by rw [map_zero, Submodule.coe_zero]
      map_add' a b := by rw [map_add, Submodule.coe_add] }

/-- The actual coefficient loses no fourth-homology class. -/
theorem homologyFourCoefficientMap_injective : Function.Injective homologyFourCoefficientMap := by
  intro a b hab
  exact homologyFourResidualKernelEquiv.injective (Subtype.ext hab)

/-- Every genuine fourth-homology coefficient is killed by the actual residual relation. -/
theorem homologyFourCoefficientMap_mul (a : SingularHomology Space 4) :
    homologyFourCoefficientMap a * referenceFibreCoefficient = 0 :=
  (homologyFourResidualKernelEquiv a).property

/-- This coefficient records the literal original connecting class at every original boundary. -/
theorem homologyFourCoefficientMap_boundary (a : SingularHomology Space 4) (i : Puncture) :
    overlapHomologyEquiv i 3 (starConnectingHomomorphism 3 a i) =
      homologyFourCoefficientMap a • (referenceClasses i).val := by
  have h := residualNativeKernelEquiv.apply_symm_apply
    ((starKernelNativeEquiv 3) (FourthDegree.homologyFourKernelEquiv a))
  have hv := congrArg
    (fun b : LinearMap.ker (nativeCapKernelRegularMap 3) => (b.val i).val) h
  change homologyFourCoefficientMap a • (referenceClasses i).val =
    overlapHomologyEquiv i 3 (starConnectingHomomorphism 3 a i) at hv
  exact hv.symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdDegree
