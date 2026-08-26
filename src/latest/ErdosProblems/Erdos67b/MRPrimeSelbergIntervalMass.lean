import ErdosProblems.Erdos67b.MRPrimeSelbergKernelReduction
import ErdosProblems.Erdos67b.MRIntervalSieve

/-!
# Unconditional interval mass of the positive prime weight

Exact floor differences discharge the progression error with constant one.
This is the total-mass input; oscillatory progression cancellation is a
separate analytic step.
-/

open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrInterval_multiples_complex_error_le_one {L U : ℕ} (hLU : L ≤ U)
    {q : ℕ} (hq : 0 < q) :
    ‖(∑ n ∈ Finset.Ioc L U with q ∣ n, (1 : ℂ)) - ((U - L : ℕ) : ℂ) / (q : ℂ)‖ ≤ 1 := by
  classical
  have hcountR : (∑ n ∈ Finset.Ioc L U with q ∣ n, (1 : ℝ)) =
      ((U / q : ℕ) : ℝ) - ((L / q : ℕ) : ℝ) := by
    rw [Finset.sum_filter]
    exact MRIntervalSieve.sum_dvdIndicator_Ioc_interval hLU q
  have hcountC : (∑ n ∈ Finset.Ioc L U with q ∣ n, (1 : ℂ)) =
      ((U / q : ℕ) : ℂ) - ((L / q : ℕ) : ℂ) := by exact_mod_cast hcountR
  have heq : (∑ n ∈ Finset.Ioc L U with q ∣ n, (1 : ℂ)) -
      ((U - L : ℕ) : ℂ) / (q : ℂ) =
      ((((U / q : ℕ) : ℝ) - ((L / q : ℕ) : ℝ) - ((U - L : ℕ) : ℝ) / q : ℝ) : ℂ) := by
    rw [hcountC]
    simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  have hlo := MRIntervalSieve.cast_div_interval_lower hLU q hq
  have hhi := MRIntervalSieve.cast_div_interval_upper hLU q hq
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem mrSum_primeSelbergMajorant_interval_le (D : ℕ) (hD : 2 ≤ D)
    {L U : ℕ} (hLU : L ≤ U) :
    (∑ n ∈ Finset.Ioc L U, mrPrimeSelbergMajorant D (by omega) n) ≤
      ((U - L : ℕ) : ℝ) / Real.log (D : ℝ) + (D : ℝ) ^ 2 := by
  have hh := mrNorm_primeSelberg_weighted_sum_le D hD (Finset.Ioc L U)
    (fun _ ↦ (1 : ℂ)) ((U - L : ℕ) : ℂ) (E := 1) zero_le_one
    (fun q hq _hqD ↦ mrInterval_multiples_complex_error_le_one hLU hq)
  simp only [mul_one, Complex.norm_natCast] at hh
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg
      (fun n hn ↦ mrPrimeSelbergMajorant_nonneg D (by omega) n))] at hh
  exact hh

theorem mrCard_primes_above_cutoff_interval_le (D : ℕ) (hD : 2 ≤ D)
    {L U : ℕ} (hLU : L ≤ U) :
    (((Finset.Ioc L U).filter (fun n ↦ n.Prime ∧ D < n)).card : ℝ) ≤
      ((U - L : ℕ) : ℝ) / Real.log (D : ℝ) + (D : ℝ) ^ 2 := by
  classical
  have hs : (∑ n ∈ Finset.Ioc L U, if n.Prime ∧ D < n then (1 : ℝ) else 0) ≤
      ∑ n ∈ Finset.Ioc L U, mrPrimeSelbergMajorant D (by omega) n :=
    Finset.sum_le_sum (fun n hn ↦ mrPrimeIndicator_le_selbergMajorant D (by omega) n)
  simp only [Finset.sum_boole] at hs
  exact hs.trans (mrSum_primeSelbergMajorant_interval_le D hD hLU)

end

end Erdos67b
