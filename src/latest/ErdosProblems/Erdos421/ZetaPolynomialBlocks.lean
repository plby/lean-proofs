import ErdosProblems.Erdos421.LogPolynomialUniform
import ErdosProblems.Erdos421.ZetaDyadic

/-! # Zeta-block estimates with polynomial dependence on the frequency degree -/

namespace Erdos421

theorem zetaBlock_polynomial_norm_bound {M N K : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (hK : 12 ≤ K) (s : ℂ) (hs : 0 ≤ s.re)
    (hlo : (M : ℝ) ^ (1 / 4 : ℝ) ≤ |s.im|) (hhi : |s.im| ≤ (M : ℝ) ^ K) :
    ‖zetaBlock M N s‖ ≤ polynomialLogarithmicConstant K *
      (M : ℝ) ^ (1 - s.re - polynomialLogarithmicExponent K) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hc := polynomialLogarithmicConstant_pos K
  have hprefix : ∀ n ≤ N, ‖logarithmicSum M n (-s.im)‖ ≤
      polynomialLogarithmicConstant K *
        (M : ℝ) ^ (1 - polynomialLogarithmicExponent K) := by
    intro n hn
    apply logarithmicSum_polynomial_uniform_bound hM (hn.trans hN) hK
    · simpa only [abs_neg] using hlo
    · simpa only [abs_neg] using hhi
  have hb := zetaBlock_norm_le_of_prefix_bounds hM N s hs (by positivity) hprefix
  apply hb.trans_eq
  rw [show 1 - s.re - polynomialLogarithmicExponent K =
    -s.re + (1 - polynomialLogarithmicExponent K) by ring, Real.rpow_add hMp]
  ring

theorem zetaBlock_polynomial_strip_bound {M N K : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (hK : 12 ≤ K) (s : ℂ) (hs : 0 ≤ s.re)
    (hstrip : 1 - s.re ≤ polynomialLogarithmicExponent K / 2)
    (hlo : (M : ℝ) ^ (1 / 4 : ℝ) ≤ |s.im|) (hhi : |s.im| ≤ (M : ℝ) ^ K) :
    ‖zetaBlock M N s‖ ≤ polynomialLogarithmicConstant K *
      (M : ℝ) ^ (-polynomialLogarithmicExponent K / 2) := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  apply (zetaBlock_polynomial_norm_bound hM hN hK s hs hlo hhi).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hM1 (by linarith))
    (polynomialLogarithmicConstant_pos K).le

noncomputable def polynomialZetaStripConstant (K : ℕ) : ℝ :=
  polynomialLogarithmicConstant K /
    (1 - (2 : ℝ) ^ (-polynomialLogarithmicExponent K / 2))

theorem polynomialZetaStripConstant_pos (K : ℕ) :
    0 < polynomialZetaStripConstant K := by
  have hd := polynomialLogarithmicExponent_pos K
  unfold polynomialZetaStripConstant
  exact div_pos (polynomialLogarithmicConstant_pos K)
    (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)))

theorem zetaBlock_polynomial_dyadic_band_bound (J L K : ℕ) (hK : 12 ≤ K)
    (s : ℂ) (hs : 0 ≤ s.re)
    (hstrip : 1 - s.re ≤ polynomialLogarithmicExponent K / 2)
    (hlo : (((2 ^ L : ℕ) : ℝ)) ^ (1 / 4 : ℝ) ≤ |s.im|)
    (hhi : |s.im| ≤ (((2 ^ J : ℕ) : ℝ)) ^ K) :
    ‖∑ j ∈ Finset.Ico J L, zetaBlock (2 ^ j) (2 ^ j) s‖ ≤
      polynomialZetaStripConstant K := by
  have hd := polynomialLogarithmicExponent_pos K
  have hc := polynomialLogarithmicConstant_pos K
  let q : ℝ := (2 : ℝ) ^ (-polynomialLogarithmicExponent K / 2)
  have hq : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpoint : ∀ j ∈ Finset.Ico J L, ‖zetaBlock (2 ^ j) (2 ^ j) s‖ ≤
      polynomialLogarithmicConstant K * q ^ j := by
    intro j hj
    obtain ⟨hjJ, hjL⟩ := Finset.mem_Ico.mp hj
    have hlow : (((2 ^ j : ℕ) : ℝ)) ^ (1 / 4 : ℝ) ≤ |s.im| := by
      apply le_trans _ hlo
      apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by norm_num)
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) hjL.le
    have hhigh : |s.im| ≤ (((2 ^ j : ℕ) : ℝ)) ^ K := by
      apply hhi.trans
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) hjJ
    have hb := zetaBlock_polynomial_strip_bound (by positivity : 0 < 2 ^ j) le_rfl
      hK s hs hstrip hlow hhigh
    have he : (((2 ^ j : ℕ) : ℝ)) ^ (-polynomialLogarithmicExponent K / 2) = q ^ j := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_pow_comm (by norm_num)]
    rwa [he] at hb
  calc
    _ ≤ ∑ j ∈ Finset.Ico J L, ‖zetaBlock (2 ^ j) (2 ^ j) s‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.Ico J L, polynomialLogarithmicConstant K * q ^ j :=
      Finset.sum_le_sum hpoint
    _ = polynomialLogarithmicConstant K * ∑ j ∈ Finset.Ico J L, q ^ j :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ polynomialLogarithmicConstant K * ∑' j : ℕ, q ^ j :=
      mul_le_mul_of_nonneg_left
        ((summable_geometric_of_lt_one hq hq1).sum_le_tsum _ (fun j _ ↦ pow_nonneg hq j))
        hc.le
    _ = _ := by rw [tsum_geometric_of_lt_one hq hq1]; rfl

theorem zetaBlock_polynomial_initial_bound {J L K : ℕ} (hJL : J ≤ L) (hK : 12 ≤ K)
    (s : ℂ) (hs : 0 ≤ s.re) (hs1 : s.re ≤ 1)
    (hstrip : 1 - s.re ≤ polynomialLogarithmicExponent K / 2)
    (hlo : (((2 ^ L : ℕ) : ℝ)) ^ (1 / 4 : ℝ) ≤ |s.im|)
    (hhi : |s.im| ≤ (((2 ^ J : ℕ) : ℝ)) ^ K) :
    ‖zetaBlock 1 (2 ^ L - 1) s‖ ≤
      J * (((2 ^ J : ℕ) : ℝ)) ^ (1 - s.re) + polynomialZetaStripConstant K := by
  have he : zetaBlock 1 (2 ^ L - 1) s = zetaBlock 1 (2 ^ J - 1) s +
      ∑ j ∈ Finset.Ico J L, zetaBlock (2 ^ j) (2 ^ j) s := by
    rw [zetaBlock_one_dyadic, zetaBlock_one_dyadic]
    exact (Finset.sum_range_add_sum_Ico _ hJL).symm
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (zetaBlock_one_dyadic_trivial_bound J s hs hs1)
    (zetaBlock_polynomial_dyadic_band_bound J L K hK s hs hstrip hlo hhi))

end Erdos421
