import ErdosProblems.Erdos421.ZetaErrorIdentity
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # A quantitative finite-sum approximation in the positive half-plane -/

namespace Erdos421

theorem rpow_tail_sum_le {N : ℕ} (hN : 0 < N) {σ : ℝ} (hσ : 0 < σ) :
    (∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ (-σ - 1)) ≤ (N : ℝ) ^ (-σ) / σ := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : AntitoneOn (fun x : ℝ ↦ x ^ (-σ - 1)) (Set.Ici (N : ℝ)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (hNp.trans_le hx) hxy (by linarith)
  have hb := ha.tsum_comp_add_le_integral N
    (integrableOn_Ioi_rpow_of_lt (by linarith : -σ - 1 < -1) hNp)
    (fun x hx ↦ Real.rpow_nonneg (hNp.trans hx).le _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -σ - 1 < -1) hNp] at hb
  simpa only [sub_add_cancel, neg_div_neg_eq] using hb

theorem norm_tsum_zetaErrorTerm_tail_le {N : ℕ} (hN : 0 < N) {s : ℂ} (hs : 0 < s.re) :
    ‖∑' n : ℕ, zetaErrorTerm (n + N) s‖ ≤
      ‖s - 1‖ * (‖s‖ / s.re * (N : ℝ) ^ (-s.re)) := by
  have hp : Summable (fun n : ℕ ↦ ((n + N + 1 : ℕ) : ℝ) ^ (-s.re - 1)) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (N + 1) (f := fun n : ℕ ↦ (n : ℝ) ^ (-s.re - 1))).mpr
        (Real.summable_nat_rpow.mpr (by linarith))
  have hb : ∀ n : ℕ, ‖zetaErrorTerm (n + N) s‖ ≤
      (‖s - 1‖ * ‖s‖) * ((n + N + 1 : ℕ) : ℝ) ^ (-s.re - 1) :=
    fun n ↦ zetaErrorTerm_norm_le (n + N) hs
  have hmajor := hp.mul_left (‖s - 1‖ * ‖s‖)
  have hnorm : Summable (fun n : ℕ ↦ ‖zetaErrorTerm (n + N) s‖) :=
    Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) hb hmajor
  calc
    _ ≤ ∑' n : ℕ, ‖zetaErrorTerm (n + N) s‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, (‖s - 1‖ * ‖s‖) * ((n + N + 1 : ℕ) : ℝ) ^ (-s.re - 1) :=
      Summable.tsum_le_tsum hb hnorm hmajor
    _ = (‖s - 1‖ * ‖s‖) * ∑' n : ℕ, ((n + N + 1 : ℕ) : ℝ) ^ (-s.re - 1) :=
      tsum_mul_left
    _ ≤ (‖s - 1‖ * ‖s‖) * ((N : ℝ) ^ (-s.re) / s.re) :=
      mul_le_mul_of_nonneg_left (rpow_tail_sum_le hN hs) (by positivity)
    _ = _ := by ring

theorem riemannZeta_eq_finite_add_tail (N : ℕ) {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = zetaBlock 1 N s + ((N + 1 : ℕ) : ℂ) ^ (1 - s) / (s - 1) +
      (∑' n : ℕ, zetaErrorTerm (n + N) s) / (s - 1) := by
  rw [riemannZeta_eq_error_series hs hs1,
    ← (summable_zetaErrorTerm hs).sum_add_tsum_nat_add N, sum_zetaErrorTerm]
  have hn : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

/-- A fully quantified truncation estimate for Mathlib's zeta function,
valid on both sides of `Re(s) = 1` as long as `Re(s)>0` and `s≠1`. -/
theorem riemannZeta_finite_sum_error_bound {N : ℕ} (hN : 0 < N)
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s - zetaBlock 1 N s - ((N + 1 : ℕ) : ℂ) ^ (1 - s) / (s - 1)‖ ≤
      ‖s‖ / s.re * (N : ℝ) ^ (-s.re) := by
  rw [riemannZeta_eq_finite_add_tail N hs hs1]
  have he : zetaBlock 1 N s + ((N + 1 : ℕ) : ℂ) ^ (1 - s) / (s - 1) +
      (∑' n : ℕ, zetaErrorTerm (n + N) s) / (s - 1) - zetaBlock 1 N s -
      ((N + 1 : ℕ) : ℂ) ^ (1 - s) / (s - 1) =
        (∑' n : ℕ, zetaErrorTerm (n + N) s) / (s - 1) := by ring
  rw [he, norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs1))).mpr
  have hb := norm_tsum_zetaErrorTerm_tail_le hN hs
  simpa only [mul_comm ‖s - 1‖] using hb

end Erdos421
