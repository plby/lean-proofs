import Arxiv.Arxiv2411_18291.ExplicitNibbleExponents
import Arxiv.Arxiv2411_18291.ExplicitNibbleBinomial

/-! # All finite nibble parameters from the paper's initial density -/

namespace Arxiv2411_18291

theorem nibble_parameters_paper_threshold {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hk : 3 ≤ q.choose r) (hn : paperSizeThreshold q r ≤ n) {g : ℝ}
    (hg : (1 / 2 : ℝ) * n.choose r ≤ g) :
    let k := q.choose r
    let a := (n : ℝ) ^ (-(1 / 9 : ℝ))
    let D := (n.choose (q - r) : ℝ) / 2
    let p₀ := (n : ℝ) ^ (-(1 / (9 * k) : ℝ))
    let L := (n : ℝ) ^ (q - r - 1)
    NibbleComparisonParameters k a g D p₀ L ∧ NibbleCountConditions k a g D p₀ L ∧
      NibbleEndConditions k a g n p₀ (q - r + 1) ∧
      NibbleExponentConditions k (q - r + 1) a g D n L ((n : ℝ) ^ (1 / 6 : ℝ))
        (1 / (4 * r.factorial)) := by
  dsimp only
  have hglower : (n : ℝ) ^ r / (4 * r.factorial) ≤ g := by
    calc
      _ = (1 / 2 : ℝ) * ((n : ℝ) ^ r / (2 * r.factorial)) := by ring
      _ ≤ (1 / 2 : ℝ) * n.choose r := mul_le_mul_of_nonneg_left
        (paper_threshold_choose_ge_half_power hr hqr hn hqr.le) (by norm_num)
      _ ≤ g := hg
  have hDlower : (n : ℝ) ^ (q - r) / (4 * (q - r).factorial) ≤
      (n.choose (q - r) : ℝ) / 2 := by
    calc
      _ = ((n : ℝ) ^ (q - r) / (2 * (q - r).factorial)) / 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (paper_threshold_choose_ge_half_power hr hqr hn (Nat.sub_le _ _)) (by norm_num)
  exact ⟨nibble_comparison_paper_threshold hr hqr hk hn hglower hDlower,
    nibble_count_paper_threshold hr hqr hk hn hglower hDlower,
    nibble_end_paper_threshold hr hqr hk hn hglower,
    nibble_exponents_paper_threshold hr hqr hn hglower hDlower⟩

end Arxiv2411_18291
