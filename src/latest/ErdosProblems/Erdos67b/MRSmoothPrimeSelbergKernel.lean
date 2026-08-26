import ErdosProblems.Erdos67b.MRSmoothPrimeProgressions
import ErdosProblems.Erdos67b.MRPrimeSelbergKernelReduction

/-!
# The finite positive prime kernel in the small-frequency range

The displayed bound holds for all frequencies, but its explicit Riemann
error is useful only at small heights. Large-frequency cancellation still
requires the separate controlled-Weyl progression estimate.
-/

open scoped BigOperators

namespace Erdos67b

noncomputable section

def mrSmoothPrimeKernelSupport (P : ℝ) : Finset ℕ := Finset.Icc ⌈P / 2⌉₊ ⌊3 * P⌋₊

def mrSmoothPrimeSelbergKernel (D : ℕ) (hD : 1 ≤ D) (P t : ℝ) : ℂ :=
  ∑ n ∈ mrSmoothPrimeKernelSupport P,
    (mrPrimeSelbergMajorant D hD n : ℂ) * mrSmoothPrimeKernelIntegrand P t n

theorem norm_mrSmoothPrimeSelbergKernel_le (D : ℕ) (hD : 2 ≤ D) {P : ℝ}
    (hP : 0 < P) (hDP : 2 * (D : ℝ) ^ 2 ≤ P) (t : ℝ) :
    ‖mrSmoothPrimeSelbergKernel D (by omega) P t‖ ≤
      2000 * P / (Real.log (D : ℝ) * (1 + t ^ 2)) + 400 * (D : ℝ) ^ 2 * (1 + |t|) := by
  have hh := mrNorm_primeSelberg_weighted_sum_le D hD (mrSmoothPrimeKernelSupport P)
    (fun n ↦ mrSmoothPrimeKernelIntegrand P t n) (mrScaledPrimeMellinIntegral P t)
    (E := 400 * (1 + |t|)) (by positivity) (by
      intro q hq hqD
      have hqDR : (q : ℝ) ≤ (D : ℝ) ^ 2 := by exact_mod_cast hqD
      exact mrSmoothPrime_progression_error_le hP hq (by linarith) t)
  have hlog : 0 < Real.log (D : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < D by omega))
  apply hh.trans
  calc
    _ ≤ (2000 * P / (1 + t ^ 2)) / Real.log (D : ℝ) +
        (D : ℝ) ^ 2 * (400 * (1 + |t|)) :=
      add_le_add (div_le_div_of_nonneg_right (norm_mrScaledPrimeMellinIntegral_le hP t) hlog.le) le_rfl
    _ = _ := by rw [div_div, mul_comm (1 + t ^ 2) (Real.log (D : ℝ))]; ring

theorem mrMem_smoothPrimeKernelSupport {P : ℝ} (hP : 0 < P) {n : ℕ}
    (hn : (n : ℝ) ∈ Set.Icc P (2 * P)) : n ∈ mrSmoothPrimeKernelSupport P := by
  apply Finset.mem_Icc.mpr
  exact ⟨Nat.ceil_le.mpr (by linarith [hn.1]), Nat.le_floor (by linarith [hn.2])⟩

theorem mrSmoothPrimeSelbergWeight_ge_one (D : ℕ) (hD : 1 ≤ D) {P : ℝ} (hP : 0 < P)
    {p : ℕ} (hp : p.Prime) (hDp : D < p) (hpP : (p : ℝ) ∈ Set.Icc P (2 * P)) :
    1 ≤ mrPrimeSelbergMajorant D hD p * mrPrimeWeightPolynomial ((p : ℝ) / P) := by
  rw [mrPrimeSelbergMajorant_prime D hD hp hDp, one_mul]
  apply mrPrimeWeightPolynomial_ge_one
  exact ⟨(le_div_iff₀ hP).2 (by simpa using hpP.1), (div_le_iff₀ hP).2 hpP.2⟩

theorem mrSmoothPrimeSelbergWeight_nonneg (D : ℕ) (hD : 1 ≤ D) (P : ℝ) (n : ℕ) :
    0 ≤ mrPrimeSelbergMajorant D hD n * mrPrimeWeightPolynomial ((n : ℝ) / P) :=
  mul_nonneg (mrPrimeSelbergMajorant_nonneg D hD n) (mrPrimeWeightPolynomial_nonneg _)

end

end Erdos67b
