import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Oscillatory kernels for Dirichlet-polynomial mean values

These elementary integral estimates begin the analytic infrastructure for
the long-gap argument. They do not assert Li's almost-all interval theorem.
-/

namespace Erdos421

open Complex MeasureTheory
open scoped ComplexConjugate

noncomputable def oscillatoryPhase (ω t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))

theorem oscillatoryPhase_continuous (ω : ℝ) : Continuous (oscillatoryPhase ω) := by
  unfold oscillatoryPhase
  fun_prop

@[simp] theorem norm_oscillatoryPhase (ω t : ℝ) : ‖oscillatoryPhase ω t‖ = 1 := by
  simp [oscillatoryPhase, Complex.norm_exp]

@[simp] theorem oscillatoryPhase_zero (t : ℝ) : oscillatoryPhase 0 t = 1 := by
  simp [oscillatoryPhase]

theorem oscillatoryPhase_mul_conj (ω ν t : ℝ) :
    oscillatoryPhase ω t * conj (oscillatoryPhase ν t) = oscillatoryPhase (ω - ν) t := by
  unfold oscillatoryPhase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_sub]
  ring

theorem norm_integral_oscillatoryPhase {ω : ℝ} (hω : ω ≠ 0) (a b : ℝ) :
    ‖∫ t in a..b, oscillatoryPhase ω t‖ ≤ 2 / |ω| := by
  have hc : Complex.I * (ω : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hω)
  have hnorm : ‖Complex.I * (ω : ℂ)‖ = |ω| := by simp
  have hsub : ‖oscillatoryPhase ω b - oscillatoryPhase ω a‖ ≤ 2 := by
    simpa only [norm_oscillatoryPhase, one_add_one_eq_two] using
      norm_sub_le (oscillatoryPhase ω b) (oscillatoryPhase ω a)
  unfold oscillatoryPhase at *
  rw [integral_exp_mul_complex hc, norm_div, hnorm]
  exact div_le_div_of_nonneg_right hsub (abs_nonneg ω)

theorem norm_integral_weighted_phase {ω : ℝ} (hω : ω ≠ 0) (c : ℂ) (a b : ℝ) :
    ‖∫ t in a..b, c * oscillatoryPhase ω t‖ ≤ 2 * ‖c‖ / |ω| := by
  rw [intervalIntegral.integral_const_mul, norm_mul]
  calc
    _ ≤ ‖c‖ * (2 / |ω|) :=
      mul_le_mul_of_nonneg_left (norm_integral_oscillatoryPhase hω a b) (norm_nonneg _)
    _ = _ := by ring

/-- Frequencies of distinct positive integer terms are separated logarithmically. -/
theorem logarithmic_frequency_ne {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    Real.log (m : ℝ) - Real.log (n : ℝ) ≠ 0 := by
  intro h
  have heq : Real.log (m : ℝ) = Real.log (n : ℝ) := sub_eq_zero.mp h
  have hmn' : (m : ℝ) = n := Real.log_injOn_pos
    (by simpa only [Set.mem_Ioi, Nat.cast_pos] using hm)
    (by simpa only [Set.mem_Ioi, Nat.cast_pos] using hn) heq
  exact hmn (by exact_mod_cast hmn')

noncomputable def exponentialSum (S : Finset ℕ) (c : ℕ → ℂ) (ω : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, c n * oscillatoryPhase (ω n) t

theorem exponentialSum_continuous (S : Finset ℕ) (c : ℕ → ℂ) (ω : ℕ → ℝ) :
    Continuous (exponentialSum S c ω) := by
  exact continuous_finsetSum S (fun n _ ↦
    continuous_const.mul (oscillatoryPhase_continuous (ω n)))

theorem exponentialSum_mul_conj (S : Finset ℕ) (c : ℕ → ℂ) (ω : ℕ → ℝ) (t : ℝ) :
    exponentialSum S c ω t * conj (exponentialSum S c ω t) =
      ∑ m ∈ S, ∑ n ∈ S, (c m * conj (c n)) * oscillatoryPhase (ω m - ω n) t := by
  unfold exponentialSum
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_mul]
  calc
    _ = (c m * conj (c n)) *
        (oscillatoryPhase (ω m) t * conj (oscillatoryPhase (ω n) t)) := by ring
    _ = _ := by rw [oscillatoryPhase_mul_conj]

theorem integral_exponentialSum_mul_conj (S : Finset ℕ) (c : ℕ → ℂ) (ω : ℕ → ℝ)
    (a b : ℝ) :
    (∫ t in a..b, exponentialSum S c ω t * conj (exponentialSum S c ω t)) =
      ∑ m ∈ S, ∑ n ∈ S, (c m * conj (c n)) *
        (∫ t in a..b, oscillatoryPhase (ω m - ω n) t) := by
  have hint : ∀ m n, IntervalIntegrable
      (fun t ↦ (c m * conj (c n)) * oscillatoryPhase (ω m - ω n) t) volume a b := by
    intro m n
    exact (continuous_const.mul (oscillatoryPhase_continuous _)).intervalIntegrable a b
  have hintsum : ∀ m, IntervalIntegrable
      (fun t ↦ ∑ n ∈ S, (c m * conj (c n)) * oscillatoryPhase (ω m - ω n) t)
      volume a b := by
    intro m
    exact (continuous_finsetSum S (fun n _ ↦
      continuous_const.mul (oscillatoryPhase_continuous _))).intervalIntegrable a b
  simp_rw [exponentialSum_mul_conj]
  rw [intervalIntegral.integral_finsetSum (fun m _ ↦ hintsum m)]
  apply Finset.sum_congr rfl
  intro m _
  rw [intervalIntegral.integral_finsetSum (fun n _ ↦ hint m n)]
  simp_rw [intervalIntegral.integral_const_mul]

theorem norm_integral_phase_correlation {ω ν : ℝ} (h : ω ≠ ν)
    (c d : ℂ) (a b : ℝ) :
    ‖(c * conj d) * (∫ t in a..b, oscillatoryPhase (ω - ν) t)‖ ≤
      2 * ‖c‖ * ‖d‖ / |ω - ν| := by
  rw [← intervalIntegral.integral_const_mul]
  have hbound := norm_integral_weighted_phase (sub_ne_zero.mpr h) (c * conj d) a b
  simpa only [norm_mul, Complex.norm_conj, mul_assoc] using hbound

/-- The elementary logarithmic lower bound for two distinct positive terms. -/
theorem log_difference_lower {m n : ℝ} (hm : 0 < m) (hmn : m < n) :
    (n - m) / n ≤ Real.log n - Real.log m := by
  have hn : 0 < n := hm.trans hmn
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hn hm)
  rw [Real.log_div hn.ne' hm.ne', inv_div] at h
  have heq : 1 - m / n = (n - m) / n := by field_simp
  rwa [heq] at h

theorem inverse_log_difference_bound {m n N : ℝ} (hm : 0 < m) (hmn : m < n)
    (hnN : n ≤ N) :
    1 / (Real.log n - Real.log m) ≤ N / (n - m) := by
  have hn : 0 < n := hm.trans hmn
  have hdiff : 0 < n - m := sub_pos.mpr hmn
  have hlog := log_difference_lower hm hmn
  have hlogpos : 0 < Real.log n - Real.log m := (div_pos hdiff hn).trans_le hlog
  apply (div_le_div_iff₀ hlogpos hdiff).mpr
  have hmul : n - m ≤ (Real.log n - Real.log m) * n := (div_le_iff₀ hn).mp hlog
  nlinarith

/-- The off-diagonal error in a finite exponential-sum mean square. -/
theorem exponentialSum_mean_square_error (S : Finset ℕ) (c : ℕ → ℂ) (ω : ℕ → ℝ)
    (hω : Set.InjOn ω S) (a b : ℝ) :
    ‖(∫ t in a..b, exponentialSum S c ω t * conj (exponentialSum S c ω t)) -
      ((b - a : ℝ) : ℂ) * (∑ m ∈ S, c m * conj (c m))‖ ≤
      ∑ m ∈ S, ∑ n ∈ S.erase m, 2 * ‖c m‖ * ‖c n‖ / |ω m - ω n| := by
  classical
  let K : ℕ → ℕ → ℂ := fun m n ↦ (c m * conj (c n)) *
    (∫ t in a..b, oscillatoryPhase (ω m - ω n) t)
  have hdiag : ∀ m, K m m = ((b - a : ℝ) : ℂ) * (c m * conj (c m)) := by
    intro m
    simp only [K, sub_self, oscillatoryPhase_zero, intervalIntegral.integral_const,
      Complex.real_smul, mul_one]
    ring
  have hsplit : (∑ m ∈ S, ∑ n ∈ S, K m n) =
      ((b - a : ℝ) : ℂ) * (∑ m ∈ S, c m * conj (c m)) +
        ∑ m ∈ S, ∑ n ∈ S.erase m, K m n := by
    calc
      _ = ∑ m ∈ S, (K m m + ∑ n ∈ S.erase m, K m n) := by
        apply Finset.sum_congr rfl
        intro m hm
        exact (Finset.add_sum_erase S (K m) hm).symm
      _ = _ := by simp_rw [hdiag, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [integral_exponentialSum_mul_conj]
  change ‖(∑ m ∈ S, ∑ n ∈ S, K m n) - _‖ ≤ _
  rw [hsplit, add_sub_cancel_left]
  calc
    _ ≤ ∑ m ∈ S, ‖∑ n ∈ S.erase m, K m n‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ S, ∑ n ∈ S.erase m, ‖K m n‖ :=
      Finset.sum_le_sum (fun m _ ↦ norm_sum_le _ _)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      have hnS := Finset.mem_of_mem_erase hn
      have hmn : ω m ≠ ω n := by
        intro heq
        exact (Finset.ne_of_mem_erase hn) (hω hm hnS heq).symm
      exact norm_integral_phase_correlation hmn (c m) (c n) a b

end Erdos421
