import ErdosProblems.Erdos421.RoughBuchstabMain

/-! # The lower prime endpoint in Buchstab summation -/

namespace Erdos421

theorem sieve_square_erase_lower {b : ℝ} {z : ℕ} (hz : (z : ℝ) ≤ Real.sqrt b) :
    (sievePrimes z (roughSquareCutoff b)).erase z = primesInRealInterval z (Real.sqrt b) := by
  ext p
  rw [Finset.mem_erase, mem_sievePrimes_square_cutoff,
    mem_primesInRealInterval (Nat.cast_nonneg z) hz]
  constructor
  · rintro ⟨hne, hp, hzp, hps⟩
    exact ⟨hp, by exact_mod_cast (show z < p by omega), hps⟩
  · rintro ⟨hp, hzp, hps⟩
    have hzp' : z < p := by exact_mod_cast hzp
    exact ⟨by omega, hp, hzp'.le, hps⟩

theorem sieve_square_prime_sum_eq (f : ℕ → ℝ) {b : ℝ} {z : ℕ}
    (hz : (z : ℝ) ≤ Real.sqrt b) :
    (∑ p ∈ sievePrimes z (roughSquareCutoff b), f p) =
      (∑ p ∈ primesInRealInterval z (Real.sqrt b), f p) + if z.Prime then f z else 0 := by
  classical
  rw [← sieve_square_erase_lower hz]
  by_cases hp : z.Prime
  · rw [if_pos hp]
    exact (Finset.sum_erase_add _ f
      ((mem_sievePrimes_square_cutoff b z z).mpr ⟨hp, le_rfl, hz⟩)).symm
  · have hnot : z ∉ sievePrimes z (roughSquareCutoff b) := by
      intro h
      exact hp ((mem_sievePrimes_square_cutoff b z z).mp h).1
    rw [if_neg hp, Finset.erase_eq_of_notMem hnot, add_zero]

theorem sieve_square_buchstab_endpoint_error (n : ℕ) {b : ℝ} {z : ℕ}
    (hb : 1 < b) (hz : 2 ≤ z) (hzs : (z : ℝ) ≤ Real.sqrt b) :
    |(∑ p ∈ sievePrimes z (roughSquareCutoff b),
      finiteBuchstab n (logarithmicBuchstabArgument b p) / ((p : ℝ) * Real.log p)) -
      ∑ p ∈ primesInRealInterval z (Real.sqrt b),
        finiteBuchstab n (logarithmicBuchstabArgument b p) / ((p : ℝ) * Real.log p)| ≤
      1 / ((z : ℝ) * Real.log z) := by
  have hz1 : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hzp : (0 : ℝ) < z := by linarith
  have hlz := Real.log_pos hz1
  have harg := logarithmicBuchstabArgument_antitone hb hz1 (hz1.trans_le hzs) hzs
  rw [logarithmicBuchstabArgument_sqrt hb] at harg
  rw [sieve_square_prime_sum_eq _ hzs, add_sub_cancel_left]
  split_ifs with hp
  · rw [abs_of_pos (div_pos (finiteBuchstab_pos _ _) (mul_pos hzp hlz))]
    exact div_le_div_of_nonneg_right (finiteBuchstab_le_one n harg) (by positivity)
  · simp only [abs_zero]
    positivity

end Erdos421
