import ErdosProblems.Erdos964.PrimeLogScaleError

/-!
# Smooth prime sums on fixed logarithmic windows
-/

namespace Erdos964

open Filter MeasureTheory
open scoped Topology

theorem exists_prime_log_window_error :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (L a b : ℝ) (g : ℝ → ℝ), 0 < L → 0 ≤ a → a ≤ b →
      (∀ z ∈ Set.Icc a b, DifferentiableAt ℝ g z) →
      ContinuousOn (deriv g) (Set.Icc a b) →
      |primeLogScaleSum L (Real.exp (L * a)) (Real.exp (L * b)) g -
        (∫ z in a..b, g z)| ≤
        (E / L) * (|g a| + |g b| + ∫ z in a..b, |deriv g z|) := by
  obtain ⟨E, hE, herror⟩ := exists_prime_log_scale_error
  refine ⟨E, hE, ?_⟩
  intro L a b g hL ha hab hg hg'
  have hx : 1 ≤ Real.exp (L * a) := Real.one_le_exp_iff.mpr (mul_nonneg hL.le ha)
  have hxy : Real.exp (L * a) ≤ Real.exp (L * b) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab hL.le)
  have hxlog : Real.log (Real.exp (L * a)) / L = a := by
    rw [Real.log_exp, mul_div_cancel_left₀ _ hL.ne']
  have hylog : Real.log (Real.exp (L * b)) / L = b := by
    rw [Real.log_exp, mul_div_cancel_left₀ _ hL.ne']
  have h := herror L (Real.exp (L * a)) (Real.exp (L * b)) g hL hx hxy
  simp only [hxlog, hylog] at h
  exact h hg hg'

theorem tendsto_primeLogScaleSum_window (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (g : ℝ → ℝ) (hg : ∀ z ∈ Set.Icc a b, DifferentiableAt ℝ g z)
    (hg' : ContinuousOn (deriv g) (Set.Icc a b)) :
    Tendsto (fun L : ℝ => primeLogScaleSum L (Real.exp (L * a)) (Real.exp (L * b)) g)
      atTop (𝓝 (∫ z in a..b, g z)) := by
  obtain ⟨E, hE, herror⟩ := exists_prime_log_window_error
  let C := E * (|g a| + |g b| + ∫ z in a..b, |deriv g z|)
  have htail : Tendsto (fun L : ℝ => C / L) atTop (𝓝 0) :=
    tendsto_id.const_div_atTop C
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun L => norm_nonneg _)) _ htail
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
  rw [Real.norm_eq_abs]
  have h := herror L a b g (by linarith) ha hab hg hg'
  calc
    _ ≤ (E / L) * (|g a| + |g b| + ∫ z in a..b, |deriv g z|) := h
    _ = C / L := by dsimp only [C]; ring

end Erdos964
