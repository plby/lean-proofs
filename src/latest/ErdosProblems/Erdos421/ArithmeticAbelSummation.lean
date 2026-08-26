import Mathlib.NumberTheory.AbelSummation

/-! # Abel summation with counts measured from a fixed real left endpoint -/

namespace Erdos421

open MeasureTheory

noncomputable def intervalCoefficient (a : ℝ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  if ⌊a⌋₊ < n then c n else 0

theorem sum_intervalCoefficient_prefix (a t : ℝ) (c : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, intervalCoefficient a c n) =
      ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊t⌋₊, c n := by
  classical
  have hset : (Finset.Icc 0 ⌊t⌋₊).filter (fun n ↦ ⌊a⌋₊ < n) =
      Finset.Ioc ⌊a⌋₊ ⌊t⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  simp only [intervalCoefficient, ← Finset.sum_filter, hset]

theorem arithmetic_interval_weighted_sum_eq (c : ℕ → ℝ) {g : ℝ → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hg : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ g t)
    (hg' : IntegrableOn (deriv g) (Set.Icc a b)) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, g n * c n) =
      g b * (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, c n) -
        ∫ t in a..b, deriv g t * ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊t⌋₊, c n := by
  have h := sum_mul_eq_sub_sub_integral_mul (intervalCoefficient a c) ha hab hg hg'
  simp_rw [sum_intervalCoefficient_prefix] at h
  simp only [Finset.Ioc_self, Finset.sum_empty, mul_zero, sub_zero] at h
  rw [← intervalIntegral.integral_of_le hab] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro n hn
  rw [intervalCoefficient, if_pos (Finset.mem_Ioc.mp hn).1]

theorem integrableOn_deriv_mul_intervalSum (c : ℕ → ℝ) {g : ℝ → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hg' : IntegrableOn (deriv g) (Set.Icc a b)) :
    IntegrableOn (fun t ↦ deriv g t * ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊t⌋₊, c n) (Set.Icc a b) := by
  have h := integrableOn_mul_sum_Icc (intervalCoefficient a c) (m := 0) ha hg'
  simpa only [sum_intervalCoefficient_prefix] using h

end Erdos421
