import ErdosProblems.Erdos421.LogarithmicPrimeCofactors

/-! # A pointwise prime minorant in the actual logarithmic windows -/

namespace Erdos421

noncomputable def logarithmicPrimeWindow (B : ℕ) (δ y : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 B).filter Nat.Prime, (logarithmicIntegerWeight δ y n).re

theorem logarithmicIntegerWeight_nonzero {δ y : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 0 < n)
    (hne : logarithmicIntegerWeight δ y n ≠ 0) :
    Real.exp y < n ∧ (n : ℝ) < Real.exp (y + δ) := by
  have hφ : oneSidedSchwartzWindow ((y - Real.log n) / δ) ≠ 0 := by
    intro hz
    apply hne
    simp only [logarithmicIntegerWeight, hz, smul_zero]
  obtain ⟨hlo, hhi⟩ := oneSidedSchwartzWindow_nonzero hφ
  have hlo' := (lt_div_iff₀ hδ).mp hlo
  have hhi' := (div_lt_iff₀ hδ).mp hhi
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · have h := Real.exp_lt_exp.mpr (show y < Real.log n by linarith)
    simpa only [Real.exp_log hnp] using h
  · have h := Real.exp_lt_exp.mpr (show Real.log n < y + δ by linarith)
    simpa only [Real.exp_log hnp] using h

theorem logarithmicRoughWindow_le_primeWindow (B z : ℕ) {δ y : ℝ} (hδ : 0 < δ)
    (hy : 0 ≤ y) (hz : Real.exp (y + δ) ≤ (z : ℝ) ^ 2) :
    logarithmicRoughWindow B z δ y ≤ logarithmicPrimeWindow B δ y := by
  classical
  rw [logarithmicRoughWindow_eq_sifted, sifted, logarithmicPrimeWindow,
    Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hp : n.Prime
  · rw [if_pos hp]
    split_ifs
    · exact le_rfl
    · exact logarithmicIntegerWeight_real_nonneg hδ y n
  · rw [if_neg hp]
    by_cases hr : RoughAt n z
    · rw [if_pos hr]
      have hzero : (logarithmicIntegerWeight δ y n).re = 0 := by
        by_contra hne
        have hcomplex : logarithmicIntegerWeight δ y n ≠ 0 := by
          intro hzero
          exact hne (by rw [hzero, Complex.zero_re])
        obtain ⟨hlo, hhi⟩ := logarithmicIntegerWeight_nonzero hδ (Finset.mem_Icc.mp hn).1 hcomplex
        have he : (1 : ℝ) ≤ Real.exp y := Real.one_le_exp_iff.mpr hy
        have hn1 : 1 < n := by exact_mod_cast he.trans_lt hlo
        have hnz : n < z ^ 2 := by exact_mod_cast hhi.trans_le hz
        exact hp (roughAt_prime_of_lt_square hn1 hnz hr)
      rw [hzero]
    · rw [if_neg hr]

theorem logarithmic_prime_minorant (B : ℕ) {w z : ℕ} (hwz : w ≤ z) {δ y : ℝ}
    (hδ : 0 < δ) (hy : 0 ≤ y) (hz : Real.exp (y + δ) ≤ (z : ℝ) ^ 2) :
    logarithmicRoughWindow B w δ y -
      logarithmicPrimeCofactorWindow (sievePrimes w z) B w δ y ≤ logarithmicPrimeWindow B δ y := by
  have hsum : (∑ p ∈ sievePrimes w z, (p : ℝ)⁻¹ *
      logarithmicRoughWindow (B / p) p δ (y - Real.log p)) ≤
        logarithmicPrimeCofactorWindow (sievePrimes w z) B w δ y := by
    apply Finset.sum_le_sum
    intro p hp
    have hwp := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
    exact mul_le_mul_of_nonneg_left
      (logarithmicRoughWindow_antitone (B / p) hδ (y - Real.log p) hwp)
      (inv_nonneg.mpr (Nat.cast_nonneg p))
  have hid := logarithmicRoughWindow_buchstab B hwz δ y
  have hprime := logarithmicRoughWindow_le_primeWindow B z hδ hy hz
  linarith

end Erdos421
