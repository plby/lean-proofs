import ErdosProblems.Erdos520.HarperBlockFirstMoment
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory ProbabilityTheory

namespace Erdos
namespace Problem520

/-!
# The product characteristic-function step in Fejér inversion

This isolates the bounded algebraic/Fubini step which turns the difference of
two translated Fourier phases into the difference of the corresponding
characteristic functions.
-/

/-- The exact product-measure characteristic-function identity used by the
Fejér CDF inversion argument.  No moment assumption is needed: both phases
have norm one. -/
theorem integral_prod_exp_neg_translate_sub_eq_charFun_sub
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (t x : ℝ) :
    (∫ p : ℝ × ℝ,
        (Complex.exp (((-t * (x - p.1) : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((-t * (x - p.2) : ℝ) : ℂ) * Complex.I))
        ∂(mu.prod nu)) =
      Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
        (charFun mu t - charFun nu t) := by
  let phase : ℂ := Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I)
  let emu : ℝ → ℂ := fun z ↦
    Complex.exp ((t : ℂ) * (z : ℂ) * Complex.I)
  have hphase (z : ℝ) :
      Complex.exp (((-t * (x - z) : ℝ) : ℂ) * Complex.I) =
        phase * emu z := by
    rw [show phase * emu z = Complex.exp
        (((( -t * x : ℝ) : ℂ) * Complex.I) +
          (((t * z : ℝ) : ℂ) * Complex.I)) by
      simp only [phase, emu, ← Complex.ofReal_mul, Complex.exp_add]]
    congr 1
    push_cast
    ring
  have hmuInt : Integrable emu mu := by
    refine (integrable_const (μ := mu) (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards with z
    simp only [emu, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I, le_refl]
  have hnuInt : Integrable emu nu := by
    refine (integrable_const (μ := nu) (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards with z
    simp only [emu, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I, le_refl]
  have hfst :
      (∫ p : ℝ × ℝ, emu p.1 ∂(mu.prod nu)) = ∫ z, emu z ∂mu := by
    simpa only [probReal_univ, one_smul] using!
      (integral_fun_fst (μ := mu) (ν := nu) emu)
  have hsnd :
      (∫ p : ℝ × ℝ, emu p.2 ∂(mu.prod nu)) = ∫ z, emu z ∂nu := by
    simpa only [probReal_univ, one_smul] using!
      (integral_fun_snd (μ := mu) (ν := nu) emu)
  calc
    (∫ p : ℝ × ℝ,
        (Complex.exp (((-t * (x - p.1) : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((-t * (x - p.2) : ℝ) : ℂ) * Complex.I))
        ∂(mu.prod nu)) =
        ∫ p : ℝ × ℝ, phase * emu p.1 - phase * emu p.2
          ∂(mu.prod nu) := by
      apply integral_congr_ae
      filter_upwards with p
      rw [hphase p.1, hphase p.2]
    _ = phase * (∫ p : ℝ × ℝ, emu p.1 ∂(mu.prod nu)) -
          phase * (∫ p : ℝ × ℝ, emu p.2 ∂(mu.prod nu)) := by
      rw [integral_sub ((hmuInt.comp_fst nu).const_mul phase)
        ((hnuInt.comp_snd mu).const_mul phase)]
      apply congrArg₂ (fun a b : ℂ ↦ a - b)
      · exact integral_const_mul phase (fun p : ℝ × ℝ ↦ emu p.1)
      · exact integral_const_mul phase (fun p : ℝ × ℝ ↦ emu p.2)
    _ = phase * ((∫ z, emu z ∂mu) - ∫ z, emu z ∂nu) := by
      rw [hfst, hsnd]
      ring
    _ = Complex.exp (((-t * x : ℝ) : ℂ) * Complex.I) *
          (charFun mu t - charFun nu t) := by
      simp only [phase, emu, charFun_apply_real]

end Problem520
end Erdos
