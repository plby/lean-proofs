import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Parity and conjugation for integrable real-line Fourier transforms

The lemmas in this file concern mathlib's ordinary Lebesgue Fourier
integral.  They record the correct parity rule for an integrable real odd
kernel.  The manuscript's cutoff quotient `χ(v)/v` is not integrable at
infinity and therefore must instead use the paired principal-value object
constructed in `FixedAwayPVTransform`; it must not be identified with the
definition below merely by notation.
-/

open MeasureTheory
open scoped ComplexConjugate Real RealInnerProductSpace

namespace Erdos1002

noncomputable section

/-- Reflection of an odd integrand makes its Fourier transform odd. -/
theorem fourier_odd_of_odd (f : ℝ → ℂ) (hf : Function.Odd f) :
    Function.Odd (FourierTransform.fourier f) := by
  intro t
  let negIso : ℝ ≃ₗᵢ[ℝ] ℝ := LinearIsometryEquiv.neg ℝ
  have hreflect := Real.fourier_comp_linearIsometry negIso f t
  have hfun : f ∘ negIso = fun x ↦ -f x := by
    funext x
    exact hf x
  calc
    FourierTransform.fourier f (-t) =
        FourierTransform.fourier (f ∘ negIso) t := by
      simpa [negIso] using! hreflect.symm
    _ = FourierTransform.fourier (fun x ↦ -f x) t := by rw [hfun]
    _ = -FourierTransform.fourier f t := by
      simp only [Real.fourier_eq, smul_neg, integral_neg]

/-- A complex-valued integrand fixed by conjugation has the usual Hermitian
Fourier symmetry. -/
theorem conj_fourier_eq_fourier_neg_of_real
    (f : ℝ → ℂ) (hf : ∀ x, conj (f x) = f x) (t : ℝ) :
    conj (FourierTransform.fourier f t) =
      FourierTransform.fourier f (-t) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, Complex.conj_ofReal,
    Complex.conj_I, hf]
  congr 1
  push_cast
  ring_nf

/-- A real odd Fourier transform is purely imaginary: conjugation negates
it pointwise. -/
theorem conj_fourier_eq_neg_of_real_odd
    (f : ℝ → ℂ) (hreal : ∀ x, conj (f x) = f x)
    (hodd : Function.Odd f) (t : ℝ) :
    conj (FourierTransform.fourier f t) =
      -FourierTransform.fourier f t := by
  rw [conj_fourier_eq_fourier_neg_of_real f hreal t]
  exact fourier_odd_of_odd f hodd t

/-- The real quotient kernel associated with a cutoff.  Division is total,
so its value at zero is the stated zero convention. -/
def evenCutoffQuotientKernel (χ : ℝ → ℝ) (v : ℝ) : ℂ :=
  ((χ v / v : ℝ) : ℂ)

theorem odd_evenCutoffQuotientKernel
    (χ : ℝ → ℝ) (hχ : Function.Even χ) :
    Function.Odd (evenCutoffQuotientKernel χ) := by
  intro v
  change ((χ (-v) / (-v) : ℝ) : ℂ) = -((χ v / v : ℝ) : ℂ)
  rw [hχ v, div_neg, Complex.ofReal_neg]

theorem real_evenCutoffQuotientKernel (χ : ℝ → ℝ) (v : ℝ) :
    conj (evenCutoffQuotientKernel χ v) =
      evenCutoffQuotientKernel χ v := by
  simp [evenCutoffQuotientKernel]

/-- The ordinary Lebesgue Fourier transform of the totalized quotient.
For the manuscript's non-`L¹` cutoff this is only a formal comparison
object, not the principal-value transform `Rχ`. -/
def evenCutoffQuotientFourier (χ : ℝ → ℝ) (t : ℝ) : ℂ :=
  FourierTransform.fourier (evenCutoffQuotientKernel χ) t

/-- Correct parity identity: `Rχ(-t) = -Rχ(t)`. -/
theorem evenCutoffQuotientFourier_neg
    (χ : ℝ → ℝ) (hχ : Function.Even χ) (t : ℝ) :
    evenCutoffQuotientFourier χ (-t) =
      -evenCutoffQuotientFourier χ t := by
  exact fourier_odd_of_odd _ (odd_evenCutoffQuotientKernel χ hχ) t

/-- Correct conjugation identity: negative frequency is the conjugate. -/
theorem evenCutoffQuotientFourier_neg_eq_conj
    (χ : ℝ → ℝ) (t : ℝ) :
    evenCutoffQuotientFourier χ (-t) =
      conj (evenCutoffQuotientFourier χ t) := by
  exact (conj_fourier_eq_fourier_neg_of_real
    (evenCutoffQuotientKernel χ)
    (real_evenCutoffQuotientKernel χ) t).symm

/-- In particular, positive and negative frequencies have identical norm,
which is the property actually needed by the square-function estimate. -/
theorem norm_evenCutoffQuotientFourier_neg
    (χ : ℝ → ℝ) (t : ℝ) :
    ‖evenCutoffQuotientFourier χ (-t)‖ =
      ‖evenCutoffQuotientFourier χ t‖ := by
  rw [evenCutoffQuotientFourier_neg_eq_conj]
  exact Complex.norm_conj _

end

end Erdos1002
