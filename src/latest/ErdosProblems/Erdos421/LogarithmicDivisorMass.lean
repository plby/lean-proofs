import ErdosProblems.Erdos421.LogarithmicKernelMass

/-! # Logarithmic windows of multiples and their harmonic mass -/

namespace Erdos421

open MeasureTheory

noncomputable def logarithmicDivisorWindow (B d : ℕ) (δ y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 B, if d ∣ n then (logarithmicIntegerWeight δ y n).re else 0

theorem logarithmicDivisorWindow_nonneg (B d : ℕ) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    0 ≤ logarithmicDivisorWindow B d δ y := by
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact logarithmicIntegerWeight_real_nonneg hδ y n
  · exact le_rfl

theorem logarithmicDivisorWindow_integrable (B d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (logarithmicDivisorWindow B d δ) := by
  apply integrable_finsetSum
  intro n hn
  by_cases hd : d ∣ n
  · simpa only [hd, ↓reduceIte] using logarithmicIntegerWeight_re_integrable hδ n
  · simp only [hd, ↓reduceIte]
    exact integrable_zero _ _ _

theorem logarithmicDivisorWindow_integral (B : ℕ) {d : ℕ} (hd : 0 < d)
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ y : ℝ, logarithmicDivisorWindow B d δ y) = (harmonic (B / d) : ℝ) / d := by
  have heq (y : ℝ) : logarithmicDivisorWindow B d δ y =
      ∑ n ∈ (Finset.Icc 1 B).filter (fun n ↦ d ∣ n),
        (logarithmicIntegerWeight δ y n).re := by
    rw [Finset.sum_filter]
    rfl
  simp_rw [heq]
  rw [integral_finsetSum _ (fun n _ ↦ logarithmicIntegerWeight_re_integrable hδ n)]
  simp_rw [logarithmicIntegerWeight_re_integral hδ]
  rw [Finset.sum_filter, ← sum_positive_multiples (fun n ↦ (n : ℝ)⁻¹) hd B]
  simp only [Nat.cast_mul, mul_inv, ← Finset.mul_sum, harmonic_eq_sum_Icc,
    Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, div_eq_mul_inv]
  ring

theorem harmonic_cast_mono {a b : ℕ} (hab : a ≤ b) :
    (harmonic a : ℝ) ≤ (harmonic b : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc le_rfl hab
  · intro n hn hn'
    exact inv_nonneg.mpr (Nat.cast_nonneg n)

theorem logarithmicDivisorWindow_integral_le (B : ℕ) {d : ℕ} (hd : 0 < d)
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ y : ℝ, logarithmicDivisorWindow B d δ y) ≤ (harmonic B : ℝ) / d := by
  rw [logarithmicDivisorWindow_integral B hd hδ]
  exact div_le_div_of_nonneg_right (harmonic_cast_mono (Nat.div_le_self B d))
    (Nat.cast_nonneg d)

theorem logarithmicDivisorWindow_mul (B d : ℕ) {q : ℕ} (hq : 0 < q) (δ y : ℝ) :
    (q : ℝ)⁻¹ * logarithmicDivisorWindow (B / q) d δ (y - Real.log q) =
      logarithmicDivisorWindow B (q * d) δ y := by
  rw [logarithmicDivisorWindow, Finset.mul_sum]
  calc
    _ = ∑ m ∈ Finset.Icc 1 (B / q), if d ∣ m then
        (logarithmicIntegerWeight δ y (q * m)).re else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      split_ifs
      · exact (logarithmicIntegerWeight_mul_re hq (Finset.mem_Icc.mp hm).1 δ y).symm
      · exact mul_zero _
    _ = ∑ m ∈ Finset.Icc 1 (B / q), if q * d ∣ q * m then
        (logarithmicIntegerWeight δ y (q * m)).re else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Nat.mul_dvd_mul_iff_left hq]
    _ = _ := by
      rw [sum_positive_multiples
        (fun n ↦ if q * d ∣ n then (logarithmicIntegerWeight δ y n).re else 0) hq B]
      unfold logarithmicDivisorWindow
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hqd : q * d ∣ n
      · simp only [hqd, dvd_trans (dvd_mul_right q d) hqd, ↓reduceIte]
      · simp only [hqd, ↓reduceIte, ite_self]

end Erdos421
