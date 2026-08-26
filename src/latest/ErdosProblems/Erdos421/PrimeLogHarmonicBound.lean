import ErdosProblems.Erdos421.PrimeLogHarmonic

/-! # A uniform elementary bound for the prime harmonic log sum -/

namespace Erdos421

theorem prime_log_harmonic_le (N : ℕ) (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, primeLogCoefficient n / (n : ℝ)) ≤ 16 * Real.log N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have htheta : Chebyshev.theta N / N ≤ Real.log 4 := by
    apply (div_le_iff₀ hNp).mpr
    exact Chebyshev.theta_le_log4_mul_x hNp.le
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 (N - 1)) :
      Chebyshev.theta n / ((n : ℝ) * (n + 1)) ≤ Real.log 4 * (n : ℝ)⁻¹ := by
    have hnp : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    calc
      _ ≤ (Real.log 4 * n) / ((n : ℝ) * (n + 1)) :=
        div_le_div_of_nonneg_right (Chebyshev.theta_le_log4_mul_x hnp.le) (by positivity)
      _ = Real.log 4 / ((n : ℝ) + 1) := by field_simp
      _ ≤ Real.log 4 / (n : ℝ) :=
        div_le_div_of_nonneg_left h4 hnp (by linarith)
      _ = _ := div_eq_mul_inv _ _
  have hsum : (∑ n ∈ Finset.Icc 1 (N - 1), Chebyshev.theta n / ((n : ℝ) * (n + 1))) ≤
      Real.log 4 * (harmonic N : ℝ) := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 (N - 1), Real.log 4 * (n : ℝ)⁻¹ := Finset.sum_le_sum hterm
      _ ≤ ∑ n ∈ Finset.Icc 1 N, Real.log 4 * (n : ℝ)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
          exact Finset.mem_Icc.mpr ⟨hn1, by omega⟩
        · intro n hn hn'
          positivity
      _ = _ := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
          Finset.mul_sum]
  have hb := harmonic_le_one_add_log N
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hLN : (1 / 2 : ℝ) ≤ Real.log N := hhalf.trans
    (Real.log_le_log (by norm_num) (by exact_mod_cast hN))
  have h4upper : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at h
    exact h
  rw [prime_log_harmonic_abel (by omega : 0 < N)]
  calc
    _ ≤ Real.log 4 + Real.log 4 * (harmonic N : ℝ) := add_le_add htheta hsum
    _ ≤ Real.log 4 * (2 + Real.log N) := by
      have h := mul_le_mul_of_nonneg_left hb h4
      nlinarith
    _ ≤ 3 * (2 + Real.log N) := mul_le_mul_of_nonneg_right h4upper (by linarith)
    _ ≤ _ := by linarith

theorem finite_prime_log_harmonic_le (S : Finset ℕ) {z : ℝ} (hz : 2 ≤ z)
    (hS : ∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ z) :
    (∑ p ∈ S, Real.log (p : ℝ) / p) ≤ 16 * Real.log z := by
  have hN : 2 ≤ ⌊z⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by exact_mod_cast hz)
  have hsub : S ⊆ Finset.Icc 1 ⌊z⌋₊ := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(hS p hp).1.pos,
      (Nat.le_floor_iff (by linarith)).mpr (hS p hp).2⟩
  have he : (∑ p ∈ S, Real.log (p : ℝ) / p) = ∑ p ∈ S, primeLogCoefficient p / (p : ℝ) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [primeLogCoefficient, if_pos (hS p hp).1]
  rw [he]
  calc
    _ ≤ ∑ p ∈ Finset.Icc 1 ⌊z⌋₊, primeLogCoefficient p / (p : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun p _ _ ↦ div_nonneg (primeLogCoefficient_nonneg p) (Nat.cast_nonneg p))
    _ ≤ 16 * Real.log ⌊z⌋₊ := prime_log_harmonic_le _ hN
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊z⌋₊))
        (Nat.floor_le (by linarith))) (by norm_num)

end Erdos421
