import ErdosProblems.Erdos587.SmoothLocator
import ErdosProblems.Erdos587.LocatorBudget
import ErdosProblems.Erdos587.HarmonicOneSixth

/-! A one-sided locator with the polynomial budget delta^7 N^3. -/

open scoped BigOperators

namespace Erdos587

theorem exists_integer_above_of_difference_bounds :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℕ → ℝ) (N : ℕ) (F C δ : ℝ),
      0 < N → (N : ℝ) ≤ F → 1 ≤ C → 0 < δ → δ ≤ 1 →
      (∀ n, n + 1 < N →
        -(C * (F / (N : ℝ) ^ 2)) ≤ phaseIncrement (phaseIncrement f) n) →
      (∀ n, n + 1 < N →
        phaseIncrement (phaseIncrement f) n ≤ -(F / (N : ℝ) ^ 2)) →
      (∀ n, n + 2 < N →
        F / (N : ℝ) ^ 3 ≤ phaseIncrement (phaseIncrement (phaseIncrement f)) n) →
      (∀ n, n + 2 < N →
        phaseIncrement (phaseIncrement (phaseIncrement f)) n ≤ C * (F / (N : ℝ) ^ 3)) →
      K * C ^ 6 * F < (N : ℝ) ^ 3 * δ ^ 7 →
      ∃ n < N, ∃ k : ℤ, 0 < (k : ℝ) - f n ∧ (k : ℝ) - f n < δ := by
  obtain ⟨D, hD, hlocator⟩ := exists_integer_above_of_harmonic_bound
  refine ⟨(100 * D) ^ 6, by positivity, ?_⟩
  intro f N F C δ hN hF hC hδ hδ1 h₂lo h₂hi h₃lo h₃hi hbudget
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hFpos : 0 < F := hNR.trans_le hF
  have hCpos : 0 < C := by linarith
  have hbudget' : (100 * D * C) ^ 6 * F < (N : ℝ) ^ 3 * δ ^ 7 := by
    simpa only [mul_pow] using hbudget
  have hsmall := sixth_power_locator_budget (by positivity : 0 ≤ 100 * D * C)
    hFpos.le hNR hδ hbudget'
  apply hlocator f N δ (100 * C * F ^ (1 / 6 : ℝ) * Real.sqrt N) hδ hδ1 (by positivity)
  · exact norm_phase_integer_harmonic_sum_le f hN hF hC h₂lo h₂hi h₃lo h₃hi
  · convert hsmall using 1
    ring

end Erdos587
