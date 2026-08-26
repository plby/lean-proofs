/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierZeta

/-!
# The Laplace integral of the rational Fourier pair kernel

The rational factor is the integral of two decaying Fourier atoms on the
positive half-line.  Polynomially weighted Schwartz transforms supply
the integrable frequency majorants for the subsequent Fubini argument.
-/

namespace Erdos4b

noncomputable section

open MeasureTheory
open scoped SchwartzMap

def laplaceFourierAtom (ξ t : ℝ) : ℂ :=
  fourierLaplaceParameter ξ * Complex.exp (-fourierLaplaceParameter ξ * (t : ℂ))

theorem laplaceFourierAtom_mul (ξ τ t : ℝ) :
    laplaceFourierAtom ξ t * laplaceFourierAtom τ t =
      (fourierLaplaceParameter ξ * fourierLaplaceParameter τ) *
        Complex.exp (-(fourierLaplaceParameter ξ + fourierLaplaceParameter τ) *
          (t : ℂ)) := by
  unfold laplaceFourierAtom
  rw [neg_add, add_mul, Complex.exp_add]
  ring

theorem norm_laplaceFourierAtom (ξ t : ℝ) :
    ‖laplaceFourierAtom ξ t‖ = ‖fourierLaplaceParameter ξ‖ * Real.exp (-t) := by
  rw [laplaceFourierAtom, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, fourierLaplaceParameter_re, neg_one_mul]

theorem integrableOn_laplaceFourierAtom_mul (ξ τ : ℝ) :
    IntegrableOn (fun t : ℝ ↦ laplaceFourierAtom ξ t * laplaceFourierAtom τ t)
      (Set.Ioi 0) := by
  have hre : (-(fourierLaplaceParameter ξ + fourierLaplaceParameter τ)).re < 0 := by
    simp
  have h := (integrableOn_exp_mul_complex_Ioi hre 0).const_mul
    (fourierLaplaceParameter ξ * fourierLaplaceParameter τ)
  simpa only [IntegrableOn, laplaceFourierAtom_mul] using! h

theorem integral_laplaceFourierAtom_mul (ξ τ : ℝ) :
    (∫ t : ℝ in Set.Ioi 0, laplaceFourierAtom ξ t * laplaceFourierAtom τ t) =
      fourierLaplacePairKernel ξ τ := by
  have hre : (-(fourierLaplaceParameter ξ + fourierLaplaceParameter τ)).re < 0 := by
    simp
  simp_rw [laplaceFourierAtom_mul]
  rw [integral_const_mul, integral_exp_mul_complex_Ioi hre 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq,
    fourierLaplacePairKernel, mul_one_div]

theorem integrable_schwartz_linear_majorant (f : SchwartzMap ℝ ℂ) :
    Integrable (fun ξ : ℝ ↦ (1 + |ξ|) * ‖f ξ‖) := by
  simpa only [add_mul, one_mul, Real.norm_eq_abs, pow_one, Pi.add_apply] using!
    f.integrable.norm.add (f.integrable_pow_mul volume 1)

theorem integrable_fourierLaplaceParameter_mul_schwartz (f : SchwartzMap ℝ ℂ) :
    Integrable (fun ξ : ℝ ↦ fourierLaplaceParameter ξ * f ξ) := by
  apply (integrable_schwartz_linear_majorant f).mono'
  · have hf := f.continuous
    unfold fourierLaplaceParameter
    exact (by fun_prop : Continuous (fun ξ : ℝ ↦ (1 + Complex.I * ξ) * f ξ)).aestronglyMeasurable
  · filter_upwards [] with ξ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_fourierLaplaceParameter_le ξ) (norm_nonneg _)

theorem norm_laplaceWeightedTriple (f g : ℝ → ℂ) (t ξ τ : ℝ) :
    ‖(laplaceFourierAtom ξ t * f ξ) * (laplaceFourierAtom τ t * g τ)‖ =
      Real.exp (-2 * t) *
        (‖fourierLaplaceParameter ξ * f ξ‖ * ‖fourierLaplaceParameter τ * g τ‖) := by
  have he : Real.exp (-t) * Real.exp (-t) = Real.exp (-2 * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [norm_mul, norm_laplaceFourierAtom]
  calc
    _ = (‖fourierLaplaceParameter ξ‖ * ‖f ξ‖ *
          (‖fourierLaplaceParameter τ‖ * ‖g τ‖)) *
        (Real.exp (-t) * Real.exp (-t)) := by ring
    _ = _ := by rw [he]; ring

theorem integrable_laplaceWeightedTriple (f g : SchwartzMap ℝ ℂ) :
    Integrable (fun z : ℝ × (ℝ × ℝ) ↦
      (laplaceFourierAtom z.2.1 z.1 * f z.2.1) *
        (laplaceFourierAtom z.2.2 z.1 * g z.2.2))
      ((volume.restrict (Set.Ioi 0)).prod (volume.prod volume)) := by
  have hf := (integrable_fourierLaplaceParameter_mul_schwartz f).norm
  have hg := (integrable_fourierLaplaceParameter_mul_schwartz g).norm
  have hfreq := hf.mul_prod hg
  have ht := integrableOn_exp_mul_Ioi (a := (-2 : ℝ)) (by norm_num) 0
  have hmajor := ht.mul_prod hfreq
  apply hmajor.mono'
  · have hfcont := f.continuous
    have hgcont := g.continuous
    apply Continuous.aestronglyMeasurable
    unfold laplaceFourierAtom fourierLaplaceParameter
    fun_prop
  · filter_upwards [] with z
    exact (norm_laplaceWeightedTriple f g z.1 z.2.1 z.2.2).le

theorem integral_laplaceWeightedPair (f g : ℝ → ℂ) (ξ τ : ℝ) :
    (∫ t : ℝ in Set.Ioi 0,
      (laplaceFourierAtom ξ t * f ξ) * (laplaceFourierAtom τ t * g τ)) =
      fourierLaplacePairKernel ξ τ * (f ξ * g τ) := by
  calc
    _ = ∫ t : ℝ in Set.Ioi 0,
        (laplaceFourierAtom ξ t * laplaceFourierAtom τ t) * (f ξ * g τ) := by
      apply integral_congr_ae
      filter_upwards [] with t
      ring
    _ = (∫ t : ℝ in Set.Ioi 0, laplaceFourierAtom ξ t * laplaceFourierAtom τ t) *
        (f ξ * g τ) := integral_mul_const _ _
    _ = _ := by rw [integral_laplaceFourierAtom_mul]

/-- Fubini for the pair kernel.  The triple integral is absolutely
integrable by the explicit exponential-times-Schwartz majorant above. -/
theorem integral_fourierLaplacePairKernel_mul_schwartz
    (f g : SchwartzMap ℝ ℂ) :
    (∫ z : ℝ × ℝ,
      fourierLaplacePairKernel z.1 z.2 * (f z.1 * g z.2) ∂(volume.prod volume)) =
      ∫ t : ℝ in Set.Ioi 0,
        (∫ ξ : ℝ, laplaceFourierAtom ξ t * f ξ) *
          (∫ τ : ℝ, laplaceFourierAtom τ t * g τ) := by
  calc
    _ = ∫ z : ℝ × ℝ, (∫ t : ℝ in Set.Ioi 0,
        (laplaceFourierAtom z.1 t * f z.1) *
          (laplaceFourierAtom z.2 t * g z.2)) ∂(volume.prod volume) := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact (integral_laplaceWeightedPair f g z.1 z.2).symm
    _ = ∫ t : ℝ in Set.Ioi 0, (∫ z : ℝ × ℝ,
        (laplaceFourierAtom z.1 t * f z.1) *
          (laplaceFourierAtom z.2 t * g z.2) ∂(volume.prod volume)) :=
      (integral_integral_swap (integrable_laplaceWeightedTriple f g)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact integral_prod_mul (fun ξ : ℝ ↦ laplaceFourierAtom ξ t * f ξ)
        (fun τ : ℝ ↦ laplaceFourierAtom τ t * g τ)

def laplaceFourierProfile (f : SchwartzMap ℝ ℂ) (t : ℝ) : ℂ :=
  ∫ ξ : ℝ, Complex.exp (-fourierLaplaceParameter ξ * (t : ℂ)) * f ξ

theorem integrable_laplaceFourierProfile_integrand (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    Integrable (fun ξ : ℝ ↦ Complex.exp (-fourierLaplaceParameter ξ * (t : ℂ)) * f ξ) := by
  apply (f.integrable.norm.const_mul (Real.exp (-t))).mono'
  · have hf := f.continuous
    apply Continuous.aestronglyMeasurable
    unfold fourierLaplaceParameter
    fun_prop
  · filter_upwards [] with ξ
    rw [norm_mul, Complex.norm_exp]
    have hre : (-fourierLaplaceParameter ξ * (t : ℂ)).re = -t := by
      simp
    rw [hre]

theorem hasDerivAt_laplaceFourierProfile_integrand
    (f : ℝ → ℂ) (ξ t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Complex.exp (-fourierLaplaceParameter ξ * (t : ℂ)) * f ξ)
      (-(laplaceFourierAtom ξ t * f ξ)) t := by
  have h := (((hasDerivAt_id (t : ℂ)).const_mul (-fourierLaplaceParameter ξ)).cexp.mul_const
    (f ξ)).comp_ofReal
  convert! h using 1
  dsimp [laplaceFourierAtom]
  ring

theorem hasDerivAt_laplaceFourierProfile (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    HasDerivAt (laplaceFourierProfile f)
      (-(∫ ξ : ℝ, laplaceFourierAtom ξ t * f ξ)) t := by
  let F : ℝ → ℝ → ℂ := fun x ξ ↦ Complex.exp (-fourierLaplaceParameter ξ * (x : ℂ)) * f ξ
  let F' : ℝ → ℝ → ℂ := fun x ξ ↦ -(laplaceFourierAtom ξ x * f ξ)
  let bound : ℝ → ℝ := fun ξ ↦ Real.exp (1 - t) * ‖fourierLaplaceParameter ξ * f ξ‖
  have hFmeas : ∀ᶠ x in nhds t, AEStronglyMeasurable (F x) := by
    apply Filter.Eventually.of_forall
    intro x
    exact (integrable_laplaceFourierProfile_integrand f x).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable (F' t) := by
    have hf := f.continuous
    apply Continuous.aestronglyMeasurable
    dsimp [F', laplaceFourierAtom, fourierLaplaceParameter]
    fun_prop
  have hbound : ∀ᵐ ξ : ℝ, ∀ x ∈ Metric.ball t 1, ‖F' x ξ‖ ≤ bound ξ := by
    filter_upwards [] with ξ
    intro x hx
    have hdist : |x - t| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hx
    have hxt : -x ≤ 1 - t := by
      have := (abs_lt.mp hdist).1
      linarith
    have he : Real.exp (-x) ≤ Real.exp (1 - t) := Real.exp_le_exp.mpr hxt
    dsimp [F', bound]
    simp only [norm_neg, norm_mul, norm_laplaceFourierAtom]
    calc
      _ = Real.exp (-x) * (‖fourierLaplaceParameter ξ‖ * ‖f ξ‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right he (by positivity)
  have hint : Integrable bound :=
    (integrable_fourierLaplaceParameter_mul_schwartz f).norm.const_mul _
  have hdiff : ∀ᵐ ξ : ℝ, ∀ x ∈ Metric.ball t 1, HasDerivAt (fun x ↦ F x ξ) (F' x ξ) x := by
    filter_upwards [] with ξ
    intro x hx
    exact hasDerivAt_laplaceFourierProfile_integrand f ξ x
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds t (by norm_num : (0 : ℝ) < 1)) hFmeas
    (integrable_laplaceFourierProfile_integrand f t) hF'meas hbound hint hdiff
  simpa only [F, F', laplaceFourierProfile, integral_neg] using! h.2

theorem integral_fourierLaplacePairKernel_eq_profile_derivatives
    (f g : SchwartzMap ℝ ℂ) :
    (∫ z : ℝ × ℝ,
      fourierLaplacePairKernel z.1 z.2 * (f z.1 * g z.2) ∂(volume.prod volume)) =
      ∫ t : ℝ in Set.Ioi 0,
        deriv (laplaceFourierProfile f) t * deriv (laplaceFourierProfile g) t := by
  rw [integral_fourierLaplacePairKernel_mul_schwartz]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [(hasDerivAt_laplaceFourierProfile f t).deriv,
    (hasDerivAt_laplaceFourierProfile g t).deriv, neg_mul_neg]

end

end Erdos4b
