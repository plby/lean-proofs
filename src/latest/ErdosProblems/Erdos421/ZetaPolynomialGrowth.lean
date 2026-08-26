import ErdosProblems.Erdos421.ZetaPolynomialBlocks
import ErdosProblems.Erdos421.ZetaHeightBound
import ErdosProblems.Erdos421.ZetaHeightWeight

/-! # Polynomial-degree growth estimates for the actual zeta function -/

namespace Erdos421

theorem riemannZeta_polynomial_dyadic_bound {J L K : ℕ}
    (hJL : J ≤ L) (hL : 0 < L) (hK : 12 ≤ K) (s : ℂ)
    (hs : 0 < s.re) (hs1 : s.re ≤ 1)
    (hstrip : 1 - s.re ≤ polynomialLogarithmicExponent K / 2)
    (hlo : (((2 ^ L : ℕ) : ℝ)) ^ (1 / 4 : ℝ) ≤ |s.im|)
    (hhi : |s.im| ≤ (((2 ^ J : ℕ) : ℝ)) ^ K) :
    ‖riemannZeta s‖ ≤ J * (((2 ^ J : ℕ) : ℝ)) ^ (1 - s.re) +
      polynomialZetaStripConstant K + (((2 ^ L : ℕ) : ℝ)) ^ (1 - s.re) / ‖s - 1‖ +
      ‖s‖ / s.re * (((2 ^ L - 1 : ℕ) : ℝ)) ^ (-s.re) := by
  have hpow : 1 < 2 ^ L := Nat.one_lt_pow (by omega) (by omega)
  have hN : 0 < 2 ^ L - 1 := by omega
  have hNsucc : 2 ^ L - 1 + 1 = 2 ^ L := by omega
  have hsp : 0 < |s.im| :=
    (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < (2 ^ L : ℕ)) _).trans_le hlo
  have hsne : s ≠ 1 := by
    intro h
    simp only [h, Complex.one_im, abs_zero, lt_self_iff_false] at hsp
  have hb := zetaBlock_polynomial_initial_bound hJL hK s hs.le hs1 hstrip hlo hhi
  have he := norm_tsum_zetaErrorTerm_tail_le hN hs
  have htail : ‖(∑' n : ℕ, zetaErrorTerm (n + (2 ^ L - 1)) s) / (s - 1)‖ ≤
      ‖s‖ / s.re * (((2 ^ L - 1 : ℕ) : ℝ)) ^ (-s.re) := by
    rw [norm_div]
    apply (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hsne))).mpr
    simpa only [mul_comm ‖s - 1‖] using he
  rw [riemannZeta_eq_finite_add_tail (2 ^ L - 1) hs hsne, hNsucc]
  have hmain := norm_add_le (zetaBlock 1 (2 ^ L - 1) s)
    ((((2 ^ L : ℕ) : ℂ)) ^ (1 - s) / (s - 1))
  rw [norm_div, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)] at hmain
  simp only [Complex.sub_re, Complex.one_re] at hmain
  exact (norm_add_le _ _).trans (add_le_add (hmain.trans (add_le_add hb le_rfl)) htail)

theorem riemannZeta_polynomial_height_bound {u K : ℕ} (hu : 0 < u) (hK : 12 ≤ K)
    (s : ℂ) (hs : 0 < s.re) (hs1 : s.re ≤ 1)
    (hstrip : 1 - s.re ≤ polynomialLogarithmicExponent K / 2)
    (hlo : ((2 ^ (K * u) : ℕ) : ℝ) ≤ |s.im|)
    (hhi : |s.im| ≤ ((2 ^ (K * (u + 1)) : ℕ) : ℝ)) :
    ‖riemannZeta s‖ ≤ (u + 1 : ℕ) * (((2 ^ (u + 1) : ℕ) : ℝ)) ^ (1 - s.re) +
      polynomialZetaStripConstant K + 9 := by
  let V := K * (u + 1)
  have hV : 0 < V := by dsimp only [V]; positivity
  have hL : 0 < 2 * V := by positivity
  have hJL : u + 1 ≤ 2 * V := by
    have hv : u + 1 ≤ V := by dsimp only [V]; nlinarith
    omega
  have hlow : (((2 ^ (2 * V) : ℕ) : ℝ)) ^ (1 / 4 : ℝ) ≤ |s.im| := by
    apply le_trans _ hlo
    apply dyadic_rpow_le_dyadic
    have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    dsimp only [V]
    push_cast
    nlinarith
  have hhigh : |s.im| ≤ (((2 ^ (u + 1) : ℕ) : ℝ)) ^ K := by
    have he : (((2 ^ (u + 1) : ℕ) : ℝ)) ^ K = ((2 ^ (K * (u + 1)) : ℕ) : ℝ) := by
      rw [← Nat.cast_pow, ← pow_mul, Nat.mul_comm (u + 1)]
    rwa [he]
  have hb := riemannZeta_polynomial_dyadic_bound hJL hL hK s hs hs1 hstrip hlow hhigh
  have hd := polynomialLogarithmicExponent_le_half K
  have hη : 1 - s.re ≤ 1 / 4 := by linarith
  have hhalf : 1 / 2 ≤ s.re := by linarith
  have hweight : (((2 ^ (2 * V) : ℕ) : ℝ)) ^ (1 - s.re) ≤ |s.im| := by
    apply le_trans _ hlo
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ K)] using
      zeta_height_scale_pole_weight hu (K - 1) hη
  have hpole := zeta_pole_term_le_one (by positivity : 0 < 2 ^ (2 * V)) s hweight
  have hN : 0 < 2 ^ (2 * V) - 1 := by
    have h := Nat.one_lt_pow (by omega : 2 * V ≠ 0) (by omega : 1 < 2)
    omega
  have hB : (2 : ℝ) ≤ (2 ^ V : ℕ) := by
    exact_mod_cast (show 2 ≤ 2 ^ V by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < 2) hV)
  have htail := zeta_tail_error_le_eight hN hB (quadratic_dyadic_cutoff hV) s hhalf hs1 hhi
  linarith

/-- The degree may vary with the height: the strip width is of order `K⁻³`
and the exponential-sum constant has a polynomial logarithm. -/
theorem riemannZeta_polynomial_growth_bound {K : ℕ} (hK : 12 ≤ K)
    (s : ℂ) (hs1 : s.re ≤ 1)
    (hstrip : 1 - s.re ≤ polynomialLogarithmicExponent K / 2)
    (ht : (2 : ℝ) ^ K ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ (1 + Real.log |s.im| / ((K : ℝ) * Real.log 2)) *
      (2 : ℝ) ^ (1 - s.re) * |s.im| ^ ((1 - s.re) / (K : ℝ)) +
      polynomialZetaStripConstant K + 9 := by
  have hb : (1 : ℝ) < 2 ^ K := by
    exact_mod_cast Nat.one_lt_pow (by omega : K ≠ 0) (by omega : 1 < 2)
  obtain ⟨u, hu₁, hu₂⟩ := exists_nat_pow_near (hb.le.trans ht) hb
  have hu : 0 < u := by
    by_contra hn
    have he : u = 0 := by omega
    rw [he, zero_add, pow_one] at hu₂
    exact (not_lt_of_ge ht) hu₂
  have hlo : ((2 ^ (K * u) : ℕ) : ℝ) ≤ |s.im| := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, pow_mul] using hu₁
  have hhi : |s.im| ≤ ((2 ^ (K * (u + 1)) : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, pow_mul] using hu₂.le
  have hd := polynomialLogarithmicExponent_le_half K
  have hs : 0 < s.re := by linarith
  have h := riemannZeta_polynomial_height_bound hu hK s hs hs1 hstrip hlo hhi
  have hw := dyadic_initial_zeta_weight_bound u (K - 1) (sub_nonneg.mpr hs1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ K)] using hlo)
  have he : ((K - 1 : ℕ) : ℝ) + 1 = K := by
    exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ K)
  rw [he] at hw
  linarith

end Erdos421
