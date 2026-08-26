import ErdosProblems.Erdos421.ProductWindowArithmetic
import ErdosProblems.Erdos421.LogarithmicPrimeMinorant

/-! # Rectangular product windows equal the truncated cofactor counts on their support -/

namespace Erdos421

theorem logarithmic_product_sum_extend (a : ℕ → ℝ) {B q : ℕ} (hq : 0 < q)
    {δ y : ℝ} (hδ : 0 < δ) (hB : Real.exp (y + δ) ≤ B) :
    (∑ m ∈ Finset.Icc 1 (B / q), a m * (logarithmicIntegerWeight δ y (q * m)).re) =
      ∑ m ∈ Finset.Icc 1 B, a m * (logarithmicIntegerWeight δ y (q * m)).re := by
  apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (Nat.div_le_self B q))
  intro m hm hnot
  have hmp := (Finset.mem_Icc.mp hm).1
  have hlarge : B < q * m := by
    have hdiv : B / q < m := by
      by_contra h
      exact hnot (Finset.mem_Icc.mpr ⟨hmp, by omega⟩)
    have hmul := (Nat.div_lt_iff_lt_mul hq).mp hdiv
    simpa only [mul_comm m q] using hmul
  have hzero : logarithmicIntegerWeight δ y (q * m) = 0 := by
    by_contra hn
    have hlt := (logarithmicIntegerWeight_nonzero hδ (Nat.mul_pos hq hmp) hn).2
    have hlargeR : (B : ℝ) < q * m := by exact_mod_cast hlarge
    rw [Nat.cast_mul] at hlt
    linarith
  rw [hzero, Complex.zero_re, mul_zero]

theorem logarithmic_weighted_cofactor_sum (a : ℕ → ℝ) {B q : ℕ} (hq : 0 < q)
    {δ y : ℝ} (hδ : 0 < δ) (hB : Real.exp (y + δ) ≤ B) :
    (q : ℝ)⁻¹ * (∑ m ∈ Finset.Icc 1 (B / q),
      a m * (logarithmicIntegerWeight δ (y - Real.log q) m).re) =
        ∑ m ∈ Finset.Icc 1 B, a m * (logarithmicIntegerWeight δ y (q * m)).re := by
  rw [← logarithmic_product_sum_extend a hq hδ hB, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [logarithmicIntegerWeight_mul_re hq (Finset.mem_Icc.mp hm).1]
  ring

theorem logarithmicPrimeCofactorWindow_product (Q : Finset ℕ) (hQ : ∀ q ∈ Q, 0 < q)
    (B z : ℕ) {δ y : ℝ} (hδ : 0 < δ) (hB : Real.exp (y + δ) ≤ B) :
    logarithmicPrimeCofactorWindow Q B z δ y =
      (scaledProductWindow (Finset.Icc 1 B) Q (fun m ↦ (roughIndicator m z : ℂ))
        (fun _ ↦ 1) 1 oneSidedSchwartzWindow δ y).re := by
  rw [scaledProductWindow_real_coefficients _ _ _ (fun m hm ↦ (Finset.mem_Icc.mp hm).1) hQ]
  unfold logarithmicPrimeCofactorWindow
  apply Finset.sum_congr rfl
  intro q hq
  rw [logarithmicRoughWindow_real_sum]
  exact logarithmic_weighted_cofactor_sum _ (hQ q hq) hδ hB

theorem logarithmic_double_cofactor_product (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p) (hQ : ∀ q ∈ Q, 0 < q) (B z : ℕ)
    {δ y : ℝ} (hδ : 0 < δ) (hB : Real.exp (y + δ) ≤ B) :
    (∑ q ∈ Q, (q : ℝ)⁻¹ *
      logarithmicPrimeCofactorWindow P (B / q) z δ (y - Real.log q)) =
        (scaledProductWindow (Finset.Icc 1 B) Q
          (fun m ↦ (primeCofactorWeight P z m : ℂ)) (fun _ ↦ 1)
            1 oneSidedSchwartzWindow δ y).re := by
  rw [scaledProductWindow_real_coefficients _ _ _ (fun m hm ↦ (Finset.mem_Icc.mp hm).1) hQ]
  apply Finset.sum_congr rfl
  intro q hq
  rw [logarithmicPrimeCofactorWindow_merge P hP]
  exact logarithmic_weighted_cofactor_sum _ (hQ q hq) hδ hB

end Erdos421
