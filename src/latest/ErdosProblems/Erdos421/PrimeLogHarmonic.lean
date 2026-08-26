import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.BigOperators.Module
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-! # An elementary logarithmic bound for the prime harmonic log sum -/

namespace Erdos421

noncomputable def primeLogCoefficient (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

theorem sum_primeLogCoefficient (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), primeLogCoefficient n) = Chebyshev.theta N := by
  rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (f := primeLogCoefficient)
    (Nat.zero_le N)]
  simp only [primeLogCoefficient, Nat.not_prime_zero, if_false, zero_add,
    Chebyshev.theta, Nat.floor_natCast, Finset.sum_filter]

theorem primeLogCoefficient_nonneg (n : ℕ) : 0 ≤ primeLogCoefficient n := by
  unfold primeLogCoefficient
  split_ifs with hn
  · exact Real.log_nonneg (by exact_mod_cast hn.one_lt.le)
  · rfl

theorem prime_log_harmonic_abel {N : ℕ} (hN : 0 < N) :
    (∑ n ∈ Finset.Icc 1 N, primeLogCoefficient n / (n : ℝ)) =
      Chebyshev.theta N / N +
        ∑ n ∈ Finset.Icc 1 (N - 1), Chebyshev.theta n / ((n : ℝ) * (n + 1)) := by
  have hb := Finset.sum_Ioc_by_parts (fun n : ℕ ↦ (n : ℝ)⁻¹) primeLogCoefficient hN
  simp only [zero_add, smul_eq_mul] at hb
  simp only [sum_primeLogCoefficient, Nat.cast_zero, Chebyshev.theta_zero, mul_zero, sub_zero] at hb
  have hinterval (k : ℕ) : Finset.Ioc 0 k = Finset.Icc 1 k := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hinterval N, hinterval (N - 1)] at hb
  have he : (∑ n ∈ Finset.Icc 1 (N - 1),
      (((n + 1 : ℕ) : ℝ)⁻¹ - (n : ℝ)⁻¹) * Chebyshev.theta n) =
      -(∑ n ∈ Finset.Icc 1 (N - 1), Chebyshev.theta n / ((n : ℝ) * (n + 1))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    push_cast
    field_simp
    ring
  rw [he, sub_neg_eq_add] at hb
  simpa only [primeLogCoefficient, div_eq_mul_inv, mul_comm] using hb

end Erdos421
