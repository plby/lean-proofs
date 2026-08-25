import ErdosProblems.Erdos964.PrimeLogAbel
import ErdosProblems.Erdos964.LogScaleChangeVariables

/-!
# Uniform prime quadrature after logarithmic rescaling
-/

namespace Erdos964

open MeasureTheory

noncomputable def primeLogScaleSum (L x y : ℝ) (g : ℝ → ℝ) : ℝ :=
  ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
    (Real.log p / (p : ℝ)) * g (Real.log p / L) / L

theorem exists_prime_log_scale_error :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (L x y : ℝ) (g : ℝ → ℝ), 0 < L → 1 ≤ x → x ≤ y →
      (∀ z ∈ Set.Icc (Real.log x / L) (Real.log y / L), DifferentiableAt ℝ g z) →
      ContinuousOn (deriv g) (Set.Icc (Real.log x / L) (Real.log y / L)) →
      |primeLogScaleSum L x y g -
        (∫ z in (Real.log x / L)..(Real.log y / L), g z)| ≤
        (E / L) * (|g (Real.log x / L)| + |g (Real.log y / L)| +
          ∫ z in (Real.log x / L)..(Real.log y / L), |deriv g z|) := by
  obtain ⟨E, hE, herror⟩ := exists_prime_log_abel_error
  refine ⟨E, hE, ?_⟩
  intro L x y g hL hx hxy hg hg'
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hf : ∀ t ∈ Set.Icc x y, DifferentiableAt ℝ (logScaleTest L g) t := by
    intro t ht
    exact (hasDerivAt_logScaleTest L t (hx0.trans_le ht.1).ne' g
      (hg _ (logScale_mem L x y t hL hx0 ht))).differentiableAt
  have hf' := continuousOn_logScaleTest_deriv L x y hL hx0 g hg hg'
  have h := herror x y (logScaleTest L g) hx hxy hf hf'
  have hsum : (∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
      logScaleTest L g p * (Real.log p / (p : ℝ))) = primeLogScaleSum L x y g := by
    unfold primeLogScaleSum
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only [logScaleTest]
    ring
  have hmain : (∫ t in x..y, logScaleTest L g t / t) =
      ∫ z in (Real.log x / L)..(Real.log y / L), g z := by
    calc
      _ = ∫ t in x..y, g (Real.log t / L) / (L * t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only [logScaleTest]
        ring
      _ = _ := integral_logScale L x y hL hx0 hxy g
        (fun z hz => (hg z hz).continuousAt.continuousWithinAt)
  rw [hsum, hmain, integral_abs_deriv_logScaleTest L x y hL hx0 hxy g hg hg'] at h
  simp only [logScaleTest, abs_div, abs_of_pos hL] at h
  calc
    _ ≤ E * (|g (Real.log x / L)| / L + |g (Real.log y / L)| / L +
        (∫ z in (Real.log x / L)..(Real.log y / L), |deriv g z|) / L) := h
    _ = _ := by ring

end Erdos964
