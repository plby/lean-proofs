import ErdosProblems.Erdos421.RoughPrimeComparison
import Mathlib.Analysis.Real.Sqrt

/-! # Exact square-root cutoff in the rough-number recurrence -/

namespace Erdos421

noncomputable def roughSquareCutoff (b : ℝ) : ℕ := ⌊Real.sqrt b⌋₊ + 1

theorem sqrt_lt_roughSquareCutoff (b : ℝ) : Real.sqrt b < roughSquareCutoff b := by
  simpa only [roughSquareCutoff, Nat.cast_add, Nat.cast_one] using
    Nat.lt_floor_add_one (Real.sqrt b)

theorem roughSquareCutoff_le_half {b : ℝ} (hb : 16 ≤ b) :
    (roughSquareCutoff b : ℝ) ≤ b / 2 := by
  have hs : 4 ≤ Real.sqrt b := Real.le_sqrt_of_sq_le (by norm_num; exact hb)
  have hsq := Real.sq_sqrt (show 0 ≤ b by linarith)
  have hf := Nat.floor_le (Real.sqrt_nonneg b)
  dsimp only [roughSquareCutoff]
  push_cast
  nlinarith

theorem mem_sievePrimes_square_cutoff (b : ℝ) (z p : ℕ) :
    p ∈ sievePrimes z (roughSquareCutoff b) ↔
      p.Prime ∧ z ≤ p ∧ (p : ℝ) ≤ Real.sqrt b := by
  simp only [sievePrimes, Finset.mem_filter, Finset.mem_Ico, roughSquareCutoff]
  have hp : p < ⌊Real.sqrt b⌋₊ + 1 ↔ (p : ℝ) ≤ Real.sqrt b := by
    rw [Nat.lt_add_one_iff, Nat.le_floor_iff (Real.sqrt_nonneg b)]
  rw [hp]
  tauto

theorem rough_real_interval_eq_primes {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    {z : ℕ} (hza : (z : ℝ) ≤ a) (hbz : b < (z : ℝ) ^ 2) :
    roughInRealInterval a b z = primesInRealInterval a b := by
  apply Finset.Subset.antisymm
  · intro n hn
    have hsub := rough_real_interval_subset_prime_square ha hab hbz.le hn
    rcases Finset.mem_union.mp hsub with hp | hs
    · exact hp
    · have heq := Finset.mem_singleton.mp hs
      obtain ⟨_, hnb, _⟩ := (mem_roughInRealInterval (by linarith) hab n z).mp hn
      rw [heq] at hnb
      have hnb' : (z : ℝ) ^ 2 ≤ b := by exact_mod_cast hnb
      exact (not_lt_of_ge hnb' hbz).elim
  · exact primes_real_interval_subset_rough (by linarith) hab hza

theorem rough_square_cutoff_buchstab {a b : ℝ} (hb : 16 ≤ b)
    (ha : b / 2 ≤ a) (hab : a ≤ b) {z : ℕ} (hz : (z : ℝ) ≤ Real.sqrt b) :
    (roughInRealInterval a b z).card = (primesInRealInterval a b).card +
      ∑ p ∈ sievePrimes z (roughSquareCutoff b),
        (roughInRealInterval (a / p) (b / p) p).card := by
  have hzcut : z ≤ roughSquareCutoff b := by
    exact_mod_cast hz.trans (sqrt_lt_roughSquareCutoff b).le
  have hcut0 : (0 : ℝ) ≤ roughSquareCutoff b := Nat.cast_nonneg _
  have hsq : b < (roughSquareCutoff b : ℝ) ^ 2 :=
    (Real.sqrt_lt (by linarith : 0 ≤ b) hcut0).mp (sqrt_lt_roughSquareCutoff b)
  rw [roughInRealInterval_buchstab (by linarith : 0 ≤ a) hab hzcut]
  rw [rough_real_interval_eq_primes (by linarith : 1 ≤ a) hab
    ((roughSquareCutoff_le_half hb).trans ha) hsq]

end Erdos421
