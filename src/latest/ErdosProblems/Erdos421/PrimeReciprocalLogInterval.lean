import ErdosProblems.Erdos421.PrimeIntervalAsymptotic
import ErdosProblems.Erdos421.InverseLogInterval

/-! # Reciprocal logarithmic prime mass on a short interval -/

namespace Erdos421

open MeasureTheory

theorem prime_reciprocal_log_le_card {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∑ p ∈ primesInRealInterval a b, 1 / ((p : ℝ) * Real.log p)) ≤
      (primesInRealInterval a b).card / (a * Real.log a) := by
  have hap : 0 < a := by linarith
  have hla := Real.log_pos ha
  calc
    _ ≤ ∑ _p ∈ primesInRealInterval a b, 1 / (a * Real.log a) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨_, hpa, _⟩ := (mem_primesInRealInterval hap.le hab p).mp hp
      apply one_div_le_one_div_of_le (mul_pos hap hla)
      exact mul_le_mul hpa.le (Real.log_le_log hap hpa.le) hla.le
        (by exact_mod_cast (Nat.zero_le p))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]

theorem prime_reciprocal_log_interval {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ X₀ > 1, ∀ a b : ℝ, X₀ ≤ a → a ≤ b →
      (∑ p ∈ primesInRealInterval a b, 1 / ((p : ℝ) * Real.log p)) ≤
        ((b - a) / Real.log a + ε * b / (Real.log a) ^ A) / (a * Real.log a) := by
  obtain ⟨X₀, hX₀, hprime⟩ := prime_interval_logarithmic_integral hA hε
  refine ⟨X₀, hX₀, ?_⟩
  intro a b ha hab
  have ha1 := hX₀.trans_le ha
  have hp := hprime a b ha hab
  have hi := (inverse_log_integral_bounds ha1 hab).2
  have hcount : ((primesInRealInterval a b).card : ℝ) ≤
      (b - a) / Real.log a + ε * b / (Real.log a) ^ A := by
    have hs := (le_abs_self _).trans hp
    rw [div_eq_mul_inv (b - a)]
    linarith
  exact (prime_reciprocal_log_le_card ha1 hab).trans
    (div_le_div_of_nonneg_right hcount (mul_nonneg (by linarith) (Real.log_pos ha1).le))

end Erdos421
