/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierCutoffIntegral
import ErdosProblems.Erdos4b.GeneralFourierProfile
import ErdosProblems.Erdos4b.GeneralFourierIncidenceWeights

/-!
# The Fourier integral of an actual divisor coefficient tensor

The finite-dimensional integral is computed by Fubini. Integrability is
proved separately from the identity, using the positive real parts of
the exponents and the Schwartz coefficients.
-/

namespace Erdos4b

noncomputable section

open MeasureTheory
open scoped BigOperators

theorem laplaceFourierProfile_log_div (f : SchwartzMap ℝ ℂ) (L d : ℝ) :
    laplaceFourierProfile f (Real.log d / L) =
      ∫ ξ : ℝ, primeFourierPower d (fourierLaplaceParameter ξ / L) * f ξ := by
  unfold laplaceFourierProfile primeFourierPower
  apply integral_congr_ae
  filter_upwards [] with ξ
  congr 1
  congr 1
  push_cast
  ring

theorem integrable_primeFourierProfile (f : SchwartzMap ℝ ℂ)
    {L d : ℝ} (hL : 0 < L) (hd : 1 ≤ d) :
    Integrable (fun ξ : ℝ ↦ primeFourierPower d (fourierLaplaceParameter ξ / L) * f ξ) := by
  have hcts : Continuous (fun ξ : ℝ ↦ primeFourierPower d (fourierLaplaceParameter ξ / L)) := by
    unfold primeFourierPower fourierLaplaceParameter
    fun_prop
  refine f.integrable.bdd_mul (c := 1) hcts.aestronglyMeasurable ?_
  apply ae_of_all
  intro ξ
  apply norm_primeFourierPower_le_one hd
  simp only [Complex.div_ofReal_re, fourierLaplaceParameter_re]
  positivity

def doubledSelbergProfileTensor {ι : Type*} [Fintype ι]
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ) (L : (ι ⊕ ι) → Bool → ℝ)
    (d : (ι ⊕ ι) → Bool → ℕ) : ℂ :=
  ∏ ib, (ArithmeticFunction.moebius (d ib.1 ib.2) : ℂ) *
    F ib (Real.log (d ib.1 ib.2) / L ib.1 ib.2)

def divisorFourierTensorCoordinate {ι : Type*}
    (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ) (L : (ι ⊕ ι) → Bool → ℝ)
    (d : (ι ⊕ ι) → Bool → ℕ) (ib : (ι ⊕ ι) × Bool) (ξ : ℝ) : ℂ :=
  (ArithmeticFunction.moebius (d ib.1 ib.2) : ℂ) *
    (primeFourierPower (d ib.1 ib.2) (fourierLaplaceParameter ξ / L ib.1 ib.2) * f ib ξ)

theorem doubledDivisorFourierWeight_mul_tensor_eq
    {ι : Type*} [Fintype ι] (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (L : (ι ⊕ ι) → Bool → ℝ) (d : (ι ⊕ ι) → Bool → ℕ)
    (ξ : ((ι ⊕ ι) × Bool) → ℝ) :
    doubledDivisorFourierWeight d (doubledFourierTensorExponents L ξ) * doubledFourierTensor f ξ =
      (∏ ib, divisorFourierTensorCoordinate f L d ib (ξ ib)) /
        ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2) : ℕ) := by
  unfold doubledDivisorFourierWeight doubledFourierTensor doubledFourierTensorExponents
  rw [div_mul_eq_mul_div]
  congr 1
  rw [← Fintype.prod_prod_type (fun ib : (ι ⊕ ι) × Bool ↦
    (ArithmeticFunction.moebius (d ib.1 ib.2) : ℂ) *
      primeFourierPower (d ib.1 ib.2) (fourierLaplaceParameter (ξ ib) / L ib.1 ib.2))]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro ib hib
  exact mul_assoc _ _ _

theorem integrable_doubledDivisorFourierWeight_mul_tensor
    {ι : Type*} [Fintype ι] (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (L : (ι ⊕ ι) → Bool → ℝ) (hL : ∀ i b, 0 < L i b)
    (d : (ι ⊕ ι) → Bool → ℕ) (hd : ∀ i b, 0 < d i b) :
    Integrable (fun ξ ↦ doubledDivisorFourierWeight d (doubledFourierTensorExponents L ξ) *
      doubledFourierTensor f ξ) := by
  have hcoord (ib : (ι ⊕ ι) × Bool) : Integrable (divisorFourierTensorCoordinate f L d ib) :=
    (integrable_primeFourierProfile (f ib) (hL ib.1 ib.2)
      (by exact_mod_cast hd ib.1 ib.2)).const_mul _
  have hprod := Integrable.fintype_prod hcoord
  have hdiv := hprod.div_const
    (((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2) : ℕ) : ℂ)
  exact hdiv.congr (ae_of_all _ fun ξ ↦ (doubledDivisorFourierWeight_mul_tensor_eq f L d ξ).symm)

theorem integral_doubledDivisorFourierWeight_mul_tensor
    {ι : Type*} [Fintype ι] (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (L : (ι ⊕ ι) → Bool → ℝ) (d : (ι ⊕ ι) → Bool → ℕ) :
    (∫ ξ, doubledDivisorFourierWeight d (doubledFourierTensorExponents L ξ) *
      doubledFourierTensor f ξ) =
      doubledSelbergProfileTensor (fun ib ↦ laplaceFourierProfile (f ib)) L d /
        ((Finset.univ : Finset ((ι ⊕ ι) × Bool)).lcm (fun ib ↦ d ib.1 ib.2) : ℕ) := by
  simp_rw [doubledDivisorFourierWeight_mul_tensor_eq f L d]
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const, integral_fintype_prod_volume_eq_prod]
  congr 1
  unfold doubledSelbergProfileTensor divisorFourierTensorCoordinate
  apply Finset.prod_congr rfl
  intro ib hib
  rw [integral_const_mul]
  exact congrArg (fun z : ℂ ↦ (ArithmeticFunction.moebius (d ib.1 ib.2) : ℂ) * z)
    (laplaceFourierProfile_log_div (f ib) (L ib.1 ib.2) (d ib.1 ib.2)).symm

end

end Erdos4b
