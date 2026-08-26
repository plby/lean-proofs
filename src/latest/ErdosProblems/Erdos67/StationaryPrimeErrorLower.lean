import ErdosProblems.Erdos67.StationaryChebyshevLower

/-! # A nonzero correlation would force a positive mean prime error -/

open scoped BigOperators Topology
open Finset Filter MeasureTheory

namespace Erdos67.StationaryModel

theorem eventually_prime_correlation_small_card (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    [NullSingletonClass (σ : Measure FrequencyCircle)] (d : ℕ+)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ P : ℕ in atTop,
      |∑ p ∈ Nat.primesLE (2 * P), correlation Q ((d.val * p : ℕ) : ℤ)| ≤
        ε * ((Nat.primesLE (2 * P)).card : ℝ) := by
  have ht := (tendsto_prime_correlation_normalized Q hQ σ hσ d).abs
  have hs := ht.eventually (gt_mem_nhds (show |(0 : ℝ)| < ε * (Real.log 2 / 2) by
    rw [abs_zero]; positivity))
  filter_upwards [hs, eventually_prime_count_log_lower, eventually_ge_atTop 2]
    with P hs hc hP
  have hPR : (0 : ℝ) < P := Nat.cast_pos.mpr (by omega)
  have hlog : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast hP)
  rw [abs_div, abs_mul, abs_of_pos hPR, abs_of_pos hlog] at hs
  have hsmall : |∑ p ∈ Nat.primesLE (2 * P), correlation Q ((d.val * p : ℕ) : ℤ)| ≤
      ε * ((Real.log 2 / 2) * (P : ℝ) / Real.log (P : ℝ)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hlog).mpr
    have hh := (div_lt_iff₀ hPR).mp hs
    nlinarith only [hh]
  exact hsmall.trans (mul_le_mul_of_nonneg_left hc hε.le)

theorem square_error_sum_lower {ι : Type*} (A : Finset ι) (f : ι → ℝ) (r : ℝ)
    (hsmall : |∑ p ∈ A, f p| ≤ |r| / 4 * (A.card : ℝ)) :
    (r ^ 2 / 2) * (A.card : ℝ) ≤ ∑ p ∈ A, (r - f p) ^ 2 := by
  have he : (∑ p ∈ A, (r - f p) ^ 2) =
      (A.card : ℝ) * r ^ 2 - 2 * r * (∑ p ∈ A, f p) + ∑ p ∈ A, f p ^ 2 := by
    simp_rw [sub_sq]
    simp only [sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul]
    rw [← mul_sum]
  have hn : 0 ≤ ∑ p ∈ A, f p ^ 2 := sum_nonneg fun _ _ ↦ sq_nonneg _
  have hm := mul_le_mul_of_nonneg_left hsmall (abs_nonneg r)
  have hr := le_abs_self (r * ∑ p ∈ A, f p)
  rw [abs_mul] at hr
  rw [he]
  nlinarith [sq_abs r]

theorem eventually_prime_error_lower (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    [NullSingletonClass (σ : Measure FrequencyCircle)] (d : ℕ+)
    (hr : correlation Q (d.val : ℤ) ≠ 0) :
    ∀ᶠ P : ℕ in atTop,
      (correlation Q (d.val : ℤ) ^ 2 / 2) * ((Nat.primesLE (2 * P)).card : ℝ) ≤
        ∑ p ∈ Nat.primesLE (2 * P),
          (correlation Q (d.val : ℤ) - correlation Q ((d.val * p : ℕ) : ℤ)) ^ 2 := by
  have hs := eventually_prime_correlation_small_card Q hQ σ hσ d
    (|correlation Q (d.val : ℤ)| / 4) (div_pos (abs_pos.mpr hr) (by norm_num))
  exact hs.mono fun P hP ↦ square_error_sum_lower _ _ _ hP

end Erdos67.StationaryModel
