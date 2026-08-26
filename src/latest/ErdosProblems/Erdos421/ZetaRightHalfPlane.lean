import ErdosProblems.Erdos421.ZetaTruncation
import Mathlib.NumberTheory.LSeries.Dirichlet

/-! # Explicit upper and reciprocal bounds on the right half-plane -/

namespace Erdos421

theorem positive_integer_rpow_sum_le {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hs : Summable (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ (-σ)) :=
    (summable_nat_add_iff 1 (f := fun n : ℕ ↦ (n : ℝ) ^ (-σ))).mpr
      (Real.summable_nat_rpow.mpr (by linarith))
  have ht := rpow_tail_sum_le (N := 1) (by decide) (sub_pos.mpr hσ)
  have hexp : -(σ - 1) - 1 = -σ := by ring
  simp only [hexp, Nat.cast_one, Real.one_rpow] at ht
  rw [hs.tsum_eq_zero_add]
  simpa only [Nat.zero_add, Nat.cast_one, Real.one_rpow] using add_le_add (le_refl 1) ht

theorem norm_LSeries_le_of_coeff_norm_le_one {f : ℕ → ℂ} {s : ℂ}
    (hf : ∀ n ≠ 0, ‖f n‖ ≤ 1) (hs : 1 < s.re) :
    ‖LSeries f s‖ ≤ 1 + 1 / (s.re - 1) := by
  have hsum := LSeriesSummable_of_bounded_of_one_lt_re hf hs
  have hnorm := hsum.norm
  have hp : Summable (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ (-s.re)) :=
    (summable_nat_add_iff 1 (f := fun n : ℕ ↦ (n : ℝ) ^ (-s.re))).mpr
      (Real.summable_nat_rpow.mpr (by linarith))
  have hterm : ∀ n : ℕ, ‖LSeries.term f s (n + 1)‖ ≤ ((n + 1 : ℕ) : ℝ) ^ (-s.re) := by
    intro n
    rw [LSeries.norm_term_eq, if_neg (by omega : n + 1 ≠ 0), Real.rpow_neg (by positivity)]
    exact (div_le_div_of_nonneg_right (hf _ (by omega)) (by positivity)).trans_eq (one_div _)
  calc
    ‖LSeries f s‖ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hnorm
    _ = ∑' n : ℕ, ‖LSeries.term f s (n + 1)‖ := by
      rw [hnorm.tsum_eq_zero_add, LSeries.term_zero, norm_zero, zero_add]
    _ ≤ ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-s.re) :=
      Summable.tsum_le_tsum hterm ((summable_nat_add_iff 1).mpr hnorm) hp
    _ ≤ _ := positive_integer_rpow_sum_le hs

theorem norm_riemannZeta_right_halfPlane_le {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ 1 + 1 / (s.re - 1) := by
  rw [← LSeries_one_eq_riemannZeta hs]
  exact norm_LSeries_le_of_coeff_norm_le_one (by simp) hs

theorem norm_inv_riemannZeta_right_halfPlane_le {s : ℂ} (hs : 1 < s.re) :
    ‖(riemannZeta s)⁻¹‖ ≤ 1 + 1 / (s.re - 1) := by
  let m : ℕ → ℂ := fun n ↦ (ArithmeticFunction.moebius n : ℂ)
  have hm : ∀ n ≠ 0, ‖m n‖ ≤ 1 := by
    intro n _
    dsimp only [m]
    norm_cast
    exact ArithmeticFunction.abs_moebius_le_one
  have hprod : riemannZeta s * LSeries m s = 1 := by
    rw [← LSeries_one_eq_riemannZeta hs]
    exact LSeries_one_mul_Lseries_moebius hs
  have he : LSeries m s = (riemannZeta s)⁻¹ := by
    exact eq_inv_of_mul_eq_one_right hprod
  rw [← he]
  exact norm_LSeries_le_of_coeff_norm_le_one hm hs

end Erdos421
