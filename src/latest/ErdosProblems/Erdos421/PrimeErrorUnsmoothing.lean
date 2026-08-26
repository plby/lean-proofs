import ErdosProblems.Erdos421.PrimeErrorPerron
import ErdosProblems.Erdos421.FiniteUnsmoothing

/-! # Finite unsmoothing for the von Mangoldt-minus-one coefficients -/

namespace Erdos421

open Complex

noncomputable def primeErrorPrefix (x : ℝ) : ℂ :=
  finiteRealPrefix (fun n ↦ LSeries.term primeErrorCoefficient 0 n) x

theorem primeError_term_norm_le_log (n : ℕ) :
    ‖LSeries.term primeErrorCoefficient 0 n‖ ≤ Real.log (n : ℝ) + 1 := by
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero, norm_zero, Nat.cast_zero, Real.log_zero, zero_add, zero_le_one]
  have hΛ : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤ Real.log (n : ℝ) := by
    rw [Complex.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact ArithmeticFunction.vonMangoldt_le_log
  rw [LSeries.term_of_ne_zero hn, cpow_zero, div_one, primeErrorCoefficient]
  have hb := norm_sub_le (ArithmeticFunction.vonMangoldt n : ℂ) 1
  rw [norm_one] at hb
  exact hb.trans (add_le_add hΛ le_rfl)

theorem finiteTriangularSum_primeError {x : ℝ} (hx : 0 < x) :
    finiteTriangularSum (fun n ↦ LSeries.term primeErrorCoefficient 0 n) x =
      (x : ℂ) * smoothedPrimeErrorSum x := by
  unfold finiteTriangularSum smoothedPrimeErrorSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have he : ((x - n : ℝ) : ℂ) = (x : ℂ) * ((1 - (n : ℝ) / x : ℝ) : ℂ) := by
    rw [← ofReal_mul]
    congr 1
    field_simp
  rw [he]
  ring

theorem primeErrorPrefix_unsmoothing_bound {x h : ℝ} (hx : 1 ≤ x) (hh : 0 < h) :
    ‖primeErrorPrefix x‖ ≤
      ((x + h) * ‖smoothedPrimeErrorSum (x + h)‖ + x * ‖smoothedPrimeErrorSum x‖) / h +
        (h + 1) * (Real.log (x + h) + 1) := by
  have hxp : 0 < x := by linarith
  have hsum : 0 < x + h := by linarith
  have hlog : 0 ≤ Real.log (x + h) + 1 := by
    have hl := Real.log_nonneg (by linarith : 1 ≤ x + h)
    linarith
  have hb := finiteTriangularSum_unsmoothing_bound
    (fun n ↦ LSeries.term primeErrorCoefficient 0 n) hxp.le hh hlog (fun n hn ↦ by
      have hnmem := Finset.mem_Ico.mp hn
      have hnpos : 0 < n := by omega
      have hnu : (n : ℝ) ≤ x + h :=
        (Nat.cast_le.mpr (by omega : n ≤ ⌊x + h⌋₊)).trans (Nat.floor_le hsum.le)
      exact (primeError_term_norm_le_log n).trans
        (add_le_add (Real.log_le_log (Nat.cast_pos.mpr hnpos) hnu) le_rfl))
  rw [finiteTriangularSum_primeError hsum, finiteTriangularSum_primeError hxp,
    norm_mul, norm_mul, Complex.norm_of_nonneg hsum.le, Complex.norm_of_nonneg hxp.le] at hb
  exact hb

end Erdos421
