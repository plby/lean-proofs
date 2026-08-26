/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierScaledKernel
import ErdosProblems.Erdos4b.GeneralFourierTensorTail

/-!
# An integrable polynomial majorant for the main Fourier kernel
-/

namespace Erdos4b

noncomputable section

open MeasureTheory
open scoped BigOperators

def mainFourierTensorMajorant {ι : Type*} [Fintype ι]
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (ξ : ((ι ⊕ ι) × Bool) → ℝ) : ℝ :=
  ∏ ib, (1 + |ξ ib|) * ‖f ib (ξ ib)‖

theorem mainFourierTensorMajorant_nonneg {ι : Type*} [Fintype ι]
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (ξ : ((ι ⊕ ι) × Bool) → ℝ) : 0 ≤ mainFourierTensorMajorant f ξ :=
  Finset.prod_nonneg fun _ _ ↦ mul_nonneg (by positivity) (norm_nonneg _)

theorem integrable_mainFourierTensorMajorant {ι : Type*} [Fintype ι]
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ) :
    Integrable (mainFourierTensorMajorant f) :=
  Integrable.fintype_prod (fun ib ↦ integrable_schwartz_linear_majorant (f ib))

theorem norm_doubledFourierPairKernel_le_coordinate_product
    {ι : Type*} [Fintype ι] (ξ : ((ι ⊕ ι) × Bool) → ℝ) :
    ‖doubledFourierPairKernel ξ‖ ≤ ∏ ib, (1 + |ξ ib|) := by
  rw [doubledFourierPairKernel, norm_prod]
  rw [Fintype.prod_prod_type (fun ib : (ι ⊕ ι) × Bool ↦ (1 + |ξ ib|))]
  apply Finset.prod_le_prod (fun i hi ↦ norm_nonneg _)
  intro i hi
  rw [Fintype.prod_bool]
  have h := norm_fourierLaplacePairKernel_le_polynomial (ξ (i, false)) (ξ (i, true))
  have hnonneg : 0 ≤ (1 + |ξ (i, false)|) * (1 + |ξ (i, true)|) := by positivity
  nlinarith

theorem norm_doubledFourierPairKernel_mul_tensor_le
    {ι : Type*} [Fintype ι] (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (ξ : ((ι ⊕ ι) × Bool) → ℝ) :
    ‖doubledFourierPairKernel ξ * doubledFourierTensor f ξ‖ ≤ mainFourierTensorMajorant f ξ := by
  rw [norm_mul, doubledFourierTensor, norm_prod, mainFourierTensorMajorant,
    Finset.prod_mul_distrib]
  exact mul_le_mul_of_nonneg_right (norm_doubledFourierPairKernel_le_coordinate_product ξ)
    (Finset.prod_nonneg fun i hi ↦ norm_nonneg _)

theorem continuous_doubledFourierPairKernel {ι : Type*} [Fintype ι] :
    Continuous (doubledFourierPairKernel (ι := ι)) := by
  apply continuous_finsetProd
  intro i hi
  unfold fourierLaplacePairKernel
  apply Continuous.div
  · unfold fourierLaplaceParameter
    fun_prop
  · unfold fourierLaplaceParameter
    fun_prop
  · intro ξ
    exact fourierLaplaceParameter_add_ne_zero _ _

theorem integrable_doubledFourierPairKernel_mul_tensor
    {ι : Type*} [Fintype ι] (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ) :
    Integrable (fun ξ ↦ doubledFourierPairKernel ξ * doubledFourierTensor f ξ) := by
  apply (integrable_mainFourierTensorMajorant f).mono'
  · exact continuous_doubledFourierPairKernel.aestronglyMeasurable.mul
      (integrable_doubledFourierTensor f).aestronglyMeasurable
  · exact ae_of_all _ (norm_doubledFourierPairKernel_mul_tensor_le f)

end

end Erdos4b
