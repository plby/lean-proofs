import ErdosProblems.Erdos421.FiniteUnsmoothing
import ErdosProblems.Erdos421.VonMangoldtPerron

/-! # Finite unsmoothing for the actual von Mangoldt coefficients -/

namespace Erdos421

open Complex

noncomputable def vonMangoldtTwistSum (x t : ℝ) : ℂ :=
  finiteRealPrefix (fun n ↦ LSeries.term
    (fun m ↦ (ArithmeticFunction.vonMangoldt m : ℂ)) (t * I) n) x

theorem vonMangoldt_twist_term_norm_le_log (t : ℝ) (n : ℕ) :
    ‖LSeries.term (fun m ↦ (ArithmeticFunction.vonMangoldt m : ℂ)) (t * I) n‖ ≤
      Real.log (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero, norm_zero, Nat.cast_zero, Real.log_zero, le_refl]
  have hΛ : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ = ArithmeticFunction.vonMangoldt n :=
    Complex.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg
  simpa only [LSeries.norm_term_eq, if_neg hn, mul_I_re, ofReal_im, neg_zero,
    Real.rpow_zero, div_one, hΛ] using (ArithmeticFunction.vonMangoldt_le_log (n := n))

theorem finiteTriangularSum_vonMangoldt {x : ℝ} (hx : 0 < x) (t : ℝ) :
    finiteTriangularSum (fun n ↦ LSeries.term
      (fun m ↦ (ArithmeticFunction.vonMangoldt m : ℂ)) (t * I) n) x =
        (x : ℂ) * smoothedVonMangoldtSum x t := by
  unfold finiteTriangularSum smoothedVonMangoldtSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have he : ((x - n : ℝ) : ℂ) = (x : ℂ) * ((1 - (n : ℝ) / x : ℝ) : ℂ) := by
    rw [← ofReal_mul]
    congr 1
    field_simp
  rw [he]
  ring

theorem vonMangoldtTwistSum_unsmoothing_bound {x h : ℝ} (hx : 1 ≤ x) (hh : 0 < h)
    (t : ℝ) :
    ‖vonMangoldtTwistSum x t‖ ≤
      ((x + h) * ‖smoothedVonMangoldtSum (x + h) t‖ + x * ‖smoothedVonMangoldtSum x t‖) / h +
        (h + 1) * Real.log (x + h) := by
  have hxp : 0 < x := by linarith
  have hsum : 0 < x + h := by linarith
  have hlog : 0 ≤ Real.log (x + h) := Real.log_nonneg (by linarith)
  have hb := finiteTriangularSum_unsmoothing_bound
    (fun n ↦ LSeries.term (fun m ↦ (ArithmeticFunction.vonMangoldt m : ℂ)) (t * I) n)
    hxp.le hh hlog (fun n hn ↦ by
      have hnmem := Finset.mem_Ico.mp hn
      have hnpos : 0 < n := by omega
      have hnu : (n : ℝ) ≤ x + h :=
        (Nat.cast_le.mpr (by omega : n ≤ ⌊x + h⌋₊)).trans (Nat.floor_le hsum.le)
      exact (vonMangoldt_twist_term_norm_le_log t n).trans
        (Real.log_le_log (Nat.cast_pos.mpr hnpos) hnu))
  rw [finiteTriangularSum_vonMangoldt hsum t, finiteTriangularSum_vonMangoldt hxp t,
    norm_mul, norm_mul, Complex.norm_of_nonneg hsum.le, Complex.norm_of_nonneg hxp.le] at hb
  exact hb

end Erdos421
