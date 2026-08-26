import ErdosProblems.Erdos67b.MRScheduledDensityGeometry

/-! # Actual tail blocks of a scheduled typical family -/

open scoped BigOperators

namespace Erdos67b

noncomputable section

def mrScheduledTailBlocks (p q : ℝ) (K J : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc K J).image (mrScheduledPrimeInterval p q)

theorem mrScheduledBlocks_mono (p q : ℝ) {K J : ℕ} (hKJ : K ≤ J) :
    mrScheduledBlocks p q K ⊆ mrScheduledBlocks p q J := by
  apply Finset.image_subset_image
  intro j hj
  obtain ⟨hj1, hjK⟩ := Finset.mem_Icc.mp hj
  exact Finset.mem_Icc.mpr ⟨hj1, hjK.trans hKJ⟩

theorem mrScheduledTailBlocks_subset (p q : ℝ) (K J : ℕ) :
    mrScheduledTailBlocks p q K J ⊆ mrScheduledBlocks p q J := by
  apply Finset.image_subset_image
  intro j hj
  obtain ⟨hKj, hjJ⟩ := Finset.mem_Ioc.mp hj
  exact Finset.mem_Icc.mpr ⟨by omega, hjJ⟩

/-- The decomposition is an exact image identity, without assuming injectivity. -/
theorem mrScheduledBlocks_eq_union_tail (p q : ℝ) {K J : ℕ} (hKJ : K ≤ J) :
    mrScheduledBlocks p q J = mrScheduledBlocks p q K ∪ mrScheduledTailBlocks p q K J := by
  have hs : Finset.Icc 1 J = Finset.Icc 1 K ∪ Finset.Ioc K J := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  unfold mrScheduledBlocks mrScheduledTailBlocks
  rw [hs, Finset.image_union]

theorem mrSum_Ioc_inv_sq_le_inv {K : ℕ} (hK : 0 < K) (J : ℕ) :
    (∑ j ∈ Finset.Ioc K J, ((j : ℝ) ^ 2)⁻¹) ≤ (K : ℝ)⁻¹ := by
  by_cases hKJ : K ≤ J
  · exact (sum_Ioc_inv_sq_le_sub hK.ne' hKJ).trans
      (sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg J)))
  · rw [Finset.Ioc_eq_empty_of_le (by omega : J ≤ K), Finset.sum_empty]
    positivity

/-- Rounded logarithmic ratios retain the inverse starting-index saving. -/
theorem mrScheduledTailBlocks_sum_logRatio_le
    {eta p q : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p) (hq : 1 ≤ q)
    (hpq : 2 * p ≤ q) (hlogq : 1 ≤ Real.log q) (hbudget : 4096 * Real.log q ≤ eta * p)
    {K : ℕ} (hK : 0 < K) (J : ℕ) :
    (∑ I ∈ mrScheduledTailBlocks p q K J,
      Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)) ≤ (2 * p / q) / K := by
  have hinj : Set.InjOn (mrScheduledPrimeInterval p q) (↑(Finset.Ioc K J) : Set ℕ) := by
    apply (mrScheduledPrimeInterval_injOn heta hp hq hpq hlogq hbudget J).mono
    intro j hj
    obtain ⟨hKj, hjJ⟩ := Finset.mem_Ioc.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega, hjJ⟩
  rw [mrScheduledTailBlocks, Finset.sum_image hinj]
  calc
    _ ≤ ∑ j ∈ Finset.Ioc K J, (2 * p / q) * ((j : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      exact mrScheduledPrimeInterval_logRatio_le hp hq hpq
        (by have := (Finset.mem_Ioc.mp hj).1; omega)
    _ = (2 * p / q) * ∑ j ∈ Finset.Ioc K J, ((j : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ (2 * p / q) * (K : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left (mrSum_Ioc_inv_sq_le_inv hK J) (by positivity)
    _ = _ := by simp only [div_eq_mul_inv]

end

end Erdos67b
