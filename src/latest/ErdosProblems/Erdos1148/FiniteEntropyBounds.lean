import ErdosProblems.Erdos1148.FiniteEntropySubadditivity

/-! # Bounds and continuity for finite Shannon entropy -/

namespace Erdos1148.DukeArithmetic

theorem finiteEntropy_nonneg {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) : 0 ≤ finiteEntropy p := by
  classical
  apply Finset.sum_nonneg
  intro i hi
  apply Real.negMulLog_nonneg (hp i)
  rw [← hsum]
  exact Finset.single_le_sum (fun j _ => hp j) hi

theorem finiteEntropy_le_log_card {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    finiteEntropy p ≤ Real.log (Fintype.card ι) := by
  have hn : 0 < Fintype.card ι := by
    by_contra h
    have hn0 := Nat.eq_zero_of_not_pos h
    let : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn0
    simp at hsum
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hqsum : (∑ _i : ι, (1 : ℝ) / Fintype.card ι) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have h := finiteEntropy_le_crossEntropy hp (fun _ => (one_div_pos.mpr hnR).le)
    (fun _ _ => one_div_pos.mpr hnR) hsum hqsum
  simpa only [← Finset.sum_mul, hsum, one_mul, one_div, Real.log_inv, neg_neg] using h

theorem continuous_finiteEntropy {ι : Type*} [Fintype ι] :
    Continuous (finiteEntropy : (ι → ℝ) → ℝ) := by
  unfold finiteEntropy
  fun_prop

end Erdos1148.DukeArithmetic
