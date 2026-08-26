import ErdosProblems.Erdos421.ZetaRightHalfPlane
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # A logarithmic height bound including the line Re(s) = 1 -/

namespace Erdos421

theorem zetaBlock_one_norm_le_harmonic (N : ℕ) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖zetaBlock 1 N s‖ ≤ (harmonic N : ℝ) := by
  calc
    ‖zetaBlock 1 N s‖ ≤ ∑ n ∈ Finset.range N, ‖((1 + n : ℕ) : ℂ) ^ (-s)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n _
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
        Complex.neg_re, Nat.add_comm 1]
      have hbase : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      simpa only [Real.rpow_neg_one] using
        Real.rpow_le_rpow_of_exponent_le hbase (show -s.re ≤ -1 by linarith)
    _ = (harmonic N : ℝ) := by simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem riemannZeta_right_height_bound (s : ℂ) (hs : 1 ≤ s.re) (ht : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 3 + Real.log (|s.im| + 2) := by
  let N : ℕ := ⌈|s.im|⌉₊ + 1
  have hN : 0 < N := by dsimp only [N]; omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNT : |s.im| + 1 ≤ (N : ℝ) := by
    dsimp only [N]
    push_cast
    linarith [Nat.le_ceil |s.im|]
  have hNT' : (N : ℝ) ≤ |s.im| + 2 := by
    have hn := Nat.ceil_lt_add_one (abs_nonneg s.im)
    dsimp only [N]
    push_cast
    linarith
  have hs0 : 0 < s.re := by linarith
  have hsne : s ≠ 1 := by
    intro he
    rw [he, Complex.one_im, abs_zero] at ht
    linarith
  have herror := riemannZeta_finite_sum_error_bound hN hs0 hsne
  have hp : (N : ℝ) ^ (-s.re) ≤ (N : ℝ)⁻¹ := by
    simpa only [Real.rpow_neg_one] using
      Real.rpow_le_rpow_of_exponent_le hN1 (show -s.re ≤ -1 by linarith)
  have hsnorm : ‖s‖ / s.re ≤ 1 + |s.im| := by
    apply (div_le_iff₀ hs0).mpr
    have hn := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg hs0.le] at hn
    nlinarith [abs_nonneg s.im]
  have htail : ‖s‖ / s.re * (N : ℝ) ^ (-s.re) ≤ 1 := by
    calc
      _ ≤ (1 + |s.im|) * (N : ℝ)⁻¹ :=
        mul_le_mul hsnorm hp (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
      _ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one hNp]; linarith
  have hweight : ((N + 1 : ℕ) : ℝ) ^ (1 - s.re) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N + 1 by omega)) (sub_nonpos.mpr hs)
  have hden : 1 ≤ ‖s - 1‖ := ht.trans (by
    simpa only [Complex.sub_im, Complex.one_im, sub_zero] using Complex.abs_im_le_norm (s - 1))
  have hpole : ‖((N + 1 : ℕ) : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 1 := by
    rw [norm_div, ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.sub_re, Complex.one_re]
    exact (div_le_one (by linarith : 0 < ‖s - 1‖)).mpr (hweight.trans hden)
  have hsum := (zetaBlock_one_norm_le_harmonic N s hs).trans (harmonic_le_one_add_log N)
  have hlog := Real.log_le_log hNp hNT'
  have htriangle : ‖riemannZeta s‖ ≤
      ‖riemannZeta s - zetaBlock 1 N s - ((N + 1 : ℕ) : ℂ) ^ (1 - s) / (s - 1)‖ +
      ‖zetaBlock 1 N s‖ + ‖((N + 1 : ℕ) : ℂ) ^ (1 - s) / (s - 1)‖ := by
    have he : riemannZeta s =
        (riemannZeta s - zetaBlock 1 N s - ((N + 1 : ℕ) : ℂ) ^ (1 - s) / (s - 1)) +
        zetaBlock 1 N s + ((N + 1 : ℕ) : ℂ) ^ (1 - s) / (s - 1) := by ring
    calc
      ‖riemannZeta s‖ = ‖(riemannZeta s - zetaBlock 1 N s -
          ((N + 1 : ℕ) : ℂ) ^ (1 - s) / (s - 1)) + zetaBlock 1 N s +
          ((N + 1 : ℕ) : ℂ) ^ (1 - s) / (s - 1)‖ := congrArg norm he
      _ ≤ _ := (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)
  linarith

end Erdos421
