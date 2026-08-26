import ErdosProblems.Erdos421.ZetaDyadic
import ErdosProblems.Erdos421.ZetaTruncation

/-! # Quantitative zeta bounds in an explicit strip adjacent to Re(s) = 1 -/

namespace Erdos421

noncomputable def zetaStripConstant (R K : ℕ) : ℝ :=
  4 * logarithmicSavingConstant R /
    (1 - (2 : ℝ) ^ (-logarithmicSavingExponent R K / 2))

theorem zetaBlock_dyadic_band_norm_bound (J L R K : ℕ) (hK : 2 * R + 4 ≤ K)
    (s : ℂ) (hs : 0 ≤ s.re) (hstrip : 1 - s.re ≤ logarithmicSavingExponent R K / 2)
    (hlo : (((2 ^ L : ℕ) : ℝ)) ^ (2 / (K : ℝ)) ≤ |s.im|)
    (hhi : |s.im| ≤ (((2 ^ J : ℕ) : ℝ)) ^ (R + 1)) :
    ‖∑ j ∈ Finset.Ico J L, zetaBlock (2 ^ j) (2 ^ j) s‖ ≤ zetaStripConstant R K := by
  have hδ := logarithmicSavingExponent_pos R (by omega : 0 < K)
  have hc := logarithmicSavingConstant_pos R
  let q : ℝ := (2 : ℝ) ^ (-logarithmicSavingExponent R K / 2)
  have hq : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpoint : ∀ j ∈ Finset.Ico J L, ‖zetaBlock (2 ^ j) (2 ^ j) s‖ ≤
      4 * logarithmicSavingConstant R * q ^ j := by
    intro j hj
    obtain ⟨hjJ, hjL⟩ := Finset.mem_Ico.mp hj
    have hlow : (((2 ^ j : ℕ) : ℝ)) ^ (2 / (K : ℝ)) ≤ |s.im| := by
      apply le_trans _ hlo
      apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by positivity)
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) hjL.le
    have hhigh : |s.im| ≤ (((2 ^ j : ℕ) : ℝ)) ^ (R + 1) := by
      apply hhi.trans
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) hjJ
    have hb := zetaBlock_uniform_strip_bound (by positivity : 0 < 2 ^ j) le_rfl
      R K hK s hs hstrip hlow hhigh
    have he : (((2 ^ j : ℕ) : ℝ)) ^ (-logarithmicSavingExponent R K / 2) = q ^ j := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_pow_comm (by norm_num)]
    rwa [he] at hb
  calc
    _ ≤ ∑ j ∈ Finset.Ico J L, ‖zetaBlock (2 ^ j) (2 ^ j) s‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.Ico J L, 4 * logarithmicSavingConstant R * q ^ j :=
      Finset.sum_le_sum hpoint
    _ = 4 * logarithmicSavingConstant R * ∑ j ∈ Finset.Ico J L, q ^ j :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ 4 * logarithmicSavingConstant R * ∑' j : ℕ, q ^ j :=
      mul_le_mul_of_nonneg_left
        ((summable_geometric_of_lt_one hq hq1).sum_le_tsum _ (fun j _ ↦ pow_nonneg hq j))
        (by positivity)
    _ = _ := by rw [tsum_geometric_of_lt_one hq hq1]; rfl

theorem zetaBlock_strip_bound {J L : ℕ} (hJL : J ≤ L) (R K : ℕ) (hK : 2 * R + 4 ≤ K)
    (s : ℂ) (hs : 0 ≤ s.re) (hs1 : s.re ≤ 1)
    (hstrip : 1 - s.re ≤ logarithmicSavingExponent R K / 2)
    (hlo : (((2 ^ L : ℕ) : ℝ)) ^ (2 / (K : ℝ)) ≤ |s.im|)
    (hhi : |s.im| ≤ (((2 ^ J : ℕ) : ℝ)) ^ (R + 1)) :
    ‖zetaBlock 1 (2 ^ L - 1) s‖ ≤
      J * (((2 ^ J : ℕ) : ℝ)) ^ (1 - s.re) + zetaStripConstant R K := by
  have he : zetaBlock 1 (2 ^ L - 1) s = zetaBlock 1 (2 ^ J - 1) s +
      ∑ j ∈ Finset.Ico J L, zetaBlock (2 ^ j) (2 ^ j) s := by
    rw [zetaBlock_one_dyadic, zetaBlock_one_dyadic]
    exact (Finset.sum_range_add_sum_Ico _ hJL).symm
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (zetaBlock_one_dyadic_trivial_bound J s hs hs1)
    (zetaBlock_dyadic_band_norm_bound J L R K hK s hs hstrip hlo hhi))

/-- An explicit strip bound for the actual zeta function, with a free
dyadic split and truncation point. The two remaining errors are displayed. -/
theorem riemannZeta_dyadic_strip_bound {J L : ℕ} (hJL : J ≤ L) (hL : 0 < L)
    (R K : ℕ) (hK : 2 * R + 4 ≤ K) (s : ℂ) (hs : 0 < s.re) (hs1 : s.re ≤ 1)
    (hstrip : 1 - s.re ≤ logarithmicSavingExponent R K / 2)
    (hlo : (((2 ^ L : ℕ) : ℝ)) ^ (2 / (K : ℝ)) ≤ |s.im|)
    (hhi : |s.im| ≤ (((2 ^ J : ℕ) : ℝ)) ^ (R + 1)) :
    ‖riemannZeta s‖ ≤ J * (((2 ^ J : ℕ) : ℝ)) ^ (1 - s.re) + zetaStripConstant R K +
      (((2 ^ L : ℕ) : ℝ)) ^ (1 - s.re) / ‖s - 1‖ +
      ‖s‖ / s.re * (((2 ^ L - 1 : ℕ) : ℝ)) ^ (-s.re) := by
  have hpow : 1 < 2 ^ L := Nat.one_lt_pow (by omega) (by omega)
  have hN : 0 < 2 ^ L - 1 := by omega
  have hNsucc : 2 ^ L - 1 + 1 = 2 ^ L := by omega
  have hsp : 0 < |s.im| :=
    (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < (2 ^ L : ℕ)) _).trans_le hlo
  have hsne : s ≠ 1 := by
    intro h
    simp only [h, Complex.one_im, abs_zero, lt_self_iff_false] at hsp
  have hb := zetaBlock_strip_bound hJL R K hK s hs.le hs1 hstrip hlo hhi
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

end Erdos421
