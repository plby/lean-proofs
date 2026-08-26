import ErdosProblems.Erdos421.PrimeDivisorConvolution

/-! # Subpower bounds survive convolution with a bounded number of large primes -/

namespace Erdos421

theorem primeDivisorConvolution_abs_le (P : Finset ℕ) (a : ℕ → ℝ)
    {w n k : ℕ} (hw : 0 < w) (hn : 0 < n) (hnk : n < w ^ k)
    (hP : ∀ p ∈ P, p.Prime ∧ w ≤ p) {C η : ℝ} (hC : 0 ≤ C) (hη : 0 ≤ η)
    (ha : ∀ d, 0 < d → |a d| ≤ C * (d : ℝ) ^ η) :
    |primeDivisorConvolution P a n| ≤ (k : ℝ) * C * (n : ℝ) ^ η := by
  have hcard := large_prime_divisor_card_lt (P.filter (fun p ↦ p ∣ n)) hw hn hnk (by
    intro p hp
    obtain ⟨hpP, hpn⟩ := Finset.mem_filter.mp hp
    exact ⟨(hP p hpP).1, (hP p hpP).2, hpn⟩)
  have heq : primeDivisorConvolution P a n =
      ∑ p ∈ P.filter (fun p ↦ p ∣ n), a (n / p) := by
    rw [Finset.sum_filter]
    rfl
  rw [heq]
  calc
    _ ≤ ∑ p ∈ P.filter (fun p ↦ p ∣ n), |a (n / p)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ P.filter (fun p ↦ p ∣ n), C * (n : ℝ) ^ η := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpP, hpn⟩ := Finset.mem_filter.mp hp
      have hd : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) (hP p hpP).1.pos
      exact (ha _ hd).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.div_le_self n p) hη) hC)
    _ = ((P.filter (fun p ↦ p ∣ n)).card : ℝ) * (C * (n : ℝ) ^ η) := by simp
    _ ≤ (k : ℝ) * (C * (n : ℝ) ^ η) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard.le) (by positivity)
    _ = _ := by ring

end Erdos421
