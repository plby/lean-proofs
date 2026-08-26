import ErdosProblems.Erdos421.FiniteRealWindowEnergy

/-! # Passing from window energy to integral absolute error -/

namespace Erdos421

open MeasureTheory

theorem interval_abs_integral_le_of_energy {f : ℝ → ℝ} (hf : Continuous f)
    {a b t : ℝ} (hab : a ≤ b) (hlen : b - a ≤ 1) (ht : 0 < t)
    (henergy : (∫ y in a..b, |f y| ^ 2) ≤ t ^ 2) :
    (∫ y in a..b, |f y|) ≤ t := by
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab
    ((continuous_const.mul hf.abs).intervalIntegrable a b)
    ((continuous_const.add (hf.abs.pow 2)).intervalIntegrable a b)
    (show ∀ y ∈ Set.Icc a b, 2 * t * |f y| ≤ t ^ 2 + |f y| ^ 2 from
      fun y _ ↦ by nlinarith [sq_nonneg (|f y| - t)])
  dsimp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply] at hm
  have hsq : IntervalIntegrable (fun y ↦ |f y| ^ 2) volume a b :=
    (hf.abs.pow 2).intervalIntegrable a b
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add intervalIntegrable_const hsq,
    intervalIntegral.integral_const] at hm
  simp only [smul_eq_mul] at hm
  have hc := mul_le_mul_of_nonneg_right hlen (sq_nonneg t)
  nlinarith

theorem interval_nonneg_integral_le_total {f : ℝ → ℝ} (hf : Integrable f)
    (hnonneg : ∀ y, 0 ≤ f y) {a b : ℝ} (hab : a ≤ b) :
    (∫ y in a..b, f y) ≤ ∫ y : ℝ, f y := by
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_le_integral hf (Filter.Eventually.of_forall hnonneg)

theorem logarithmic_dyadic_abs_integral_le_of_energy {f : ℝ → ℝ} (hf : Continuous f)
    {X t : ℝ} (hX : 0 < X) (ht : 0 < t)
    (henergy : (∫ y in Real.log X..Real.log (2 * X), |f y| ^ 2) ≤ t ^ 2) :
    (∫ y in Real.log X..Real.log (2 * X), |f y|) ≤ t := by
  have hab := Real.log_le_log hX (show X ≤ 2 * X by linarith)
  apply interval_abs_integral_le_of_energy hf hab _ ht henergy
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hX.ne']
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

theorem interval_abs_integral_transfer {f g h e₁ e₂ : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (he₁ : Integrable e₁) (he₂ : Integrable e₂)
    (he₁pos : ∀ y, 0 ≤ e₁ y) (he₂pos : ∀ y, 0 ≤ e₂ y)
    (heq : ∀ y, f y = g y - h y + e₁ y - e₂ y)
    {a b : ℝ} (hab : a ≤ b) :
    (∫ y in a..b, |f y|) ≤ (∫ y in a..b, |g y|) + (∫ y in a..b, |h y|) +
      (∫ y : ℝ, e₁ y) + (∫ y : ℝ, e₂ y) := by
  have hpoint : ∀ y, |f y| ≤ |g y| + |h y| + e₁ y + e₂ y := by
    intro y
    rw [heq y]
    calc
      _ ≤ |g y - h y + e₁ y| + |e₂ y| := abs_sub _ _
      _ ≤ (|g y| + |h y| + |e₁ y|) + |e₂ y| := by
        gcongr
        exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ = _ := by rw [abs_of_nonneg (he₁pos y), abs_of_nonneg (he₂pos y)]
  have hm := intervalIntegral.integral_mono_on (μ := volume) hab
    (hf.abs.intervalIntegrable a b)
    ((((hg.abs.intervalIntegrable a b).add (hh.abs.intervalIntegrable a b)).add
      he₁.intervalIntegrable).add he₂.intervalIntegrable)
    (fun y _ ↦ hpoint y)
  rw [intervalIntegral.integral_add
      (((hg.abs.intervalIntegrable a b).add (hh.abs.intervalIntegrable a b)).add
        he₁.intervalIntegrable) he₂.intervalIntegrable,
    intervalIntegral.integral_add
      ((hg.abs.intervalIntegrable a b).add (hh.abs.intervalIntegrable a b)) he₁.intervalIntegrable,
    intervalIntegral.integral_add (hg.abs.intervalIntegrable a b)
      (hh.abs.intervalIntegrable a b)] at hm
  exact hm.trans (add_le_add
    (add_le_add le_rfl (interval_nonneg_integral_le_total he₁ he₁pos hab))
    (interval_nonneg_integral_le_total he₂ he₂pos hab))

end Erdos421
