import ErdosProblems.Erdos1148.FiniteEntropyThreeClasses

/-! # An entropy gap from two nested families of words -/

namespace Erdos1148.DukeArithmetic

theorem finiteEntropy_le_gap_of_word_families {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G H : Finset ι) (hGH : G ⊆ H) {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) {L d q A B : ℝ} (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hGcard : (G.card : ℝ) ≤ A * Real.exp ((1 - d + d / 16) * L))
    (hHcard : (H.card : ℝ) ≤ B * Real.exp ((1 + d / 16) * L))
    (hcard : (Fintype.card ι : ℝ) ≤ Real.exp (q * L))
    (hGmass : (1 / 2 : ℝ) ≤ ∑ i ∈ G, p i)
    (hbad : (1 - ∑ i ∈ H, p i) * q ≤ d / 16) :
    finiteEntropy p ≤ Real.log 3 + Real.log A + Real.log B + (1 - 3 * d / 8) * L := by
  classical
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hG0 : 0 ≤ ∑ i ∈ G, p i := Finset.sum_nonneg (fun i _ => hp i)
  have hH1 : (∑ i ∈ H, p i) ≤ 1 := by
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H) (fun i _ _ => hp i)
  have hGHmass : (∑ i ∈ G, p i) ≤ ∑ i ∈ H, p i :=
    Finset.sum_le_sum_of_subset_of_nonneg hGH (fun i _ _ => hp i)
  have hG1 := hGHmass.trans hH1
  have hdiff1 : (∑ i ∈ H, p i) - ∑ i ∈ G, p i ≤ 1 := by linarith only [hH1, hG0]
  have hga := mul_le_mul_of_nonneg_right hG1 (Real.log_nonneg hA)
  have hhb := mul_le_mul_of_nonneg_right hdiff1 (Real.log_nonneg hB)
  have hr1 := mul_le_mul_of_nonneg_right hH1 (show 0 ≤ 1 + d / 16 by positivity)
  have hr2 := mul_le_mul_of_nonneg_right hGmass hd
  have hrate : (∑ i ∈ H, p i) * (1 + d / 16) - (∑ i ∈ G, p i) * d +
      (1 - ∑ i ∈ H, p i) * q ≤ 1 - 3 * d / 8 := by
    linarith only [hr1, hr2, hbad]
  have hscaled := mul_le_mul_of_nonneg_right hrate hL
  have hent := finiteEntropy_le_three_class_bound G H hGH
    (mul_pos hApos (Real.exp_pos _)) (mul_pos hBpos (Real.exp_pos _))
    (Real.exp_pos _) hGcard hHcard hcard hp hsum
  rw [Real.log_mul hApos.ne' (Real.exp_ne_zero _),
    Real.log_mul hBpos.ne' (Real.exp_ne_zero _)] at hent
  simp only [Real.log_exp] at hent
  nlinarith only [hent, hga, hhb, hscaled]

end Erdos1148.DukeArithmetic
