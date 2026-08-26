import ErdosProblems.Erdos421.MertensPrimeIntervals
import ErdosProblems.Erdos421.Buchstab

/-! # Reciprocal-prime upper bounds with the sieve endpoint conventions -/

namespace Erdos421

theorem sievePrimes_reciprocal_le_open {z Q : ℕ} (hzQ : z ≤ Q) :
    (∑ p ∈ sievePrimes z Q, (p : ℝ)⁻¹) ≤
      (∑ p ∈ primesInRealInterval z Q, (p : ℝ)⁻¹) + (z : ℝ)⁻¹ := by
  classical
  have hzQr : (z : ℝ) ≤ Q := by exact_mod_cast hzQ
  have hsub : sievePrimes z Q ⊆ insert z (primesInRealInterval z Q) := by
    intro p hp
    obtain ⟨hpI, hpp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hzp, hpQ⟩ := Finset.mem_Ico.mp hpI
    by_cases hpz : p = z
    · exact Finset.mem_insert.mpr (Or.inl hpz)
    · apply Finset.mem_insert.mpr (Or.inr ?_)
      exact (mem_primesInRealInterval (Nat.cast_nonneg z) hzQr p).mpr
        ⟨hpp, by exact_mod_cast (show z < p by omega), by exact_mod_cast hpQ.le⟩
  have hznot : z ∉ primesInRealInterval z Q := by
    intro h
    exact (lt_irrefl (z : ℝ)) ((mem_primesInRealInterval (Nat.cast_nonneg z) hzQr z).mp h).2.1
  calc
    _ ≤ ∑ p ∈ insert z (primesInRealInterval z Q), (p : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
    _ = _ := by rw [Finset.sum_insert hznot]; ring

theorem mertens_sieve_interval {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℝ, X₀ > 1 ∧ ∀ z Q : ℕ, X₀ ≤ z → z ≤ Q → 1 ≤ Real.log z →
      Real.log Q ≤ 3 * Real.log z →
      (∑ p ∈ sievePrimes z Q, (p : ℝ)⁻¹) ≤
        Real.log (Real.log Q / Real.log z) + ε + (z : ℝ)⁻¹ := by
  obtain ⟨X₀, hX₀, hmertens⟩ := mertens_prime_interval hε
  refine ⟨X₀, hX₀, ?_⟩
  intro z Q hz hzQ hlog hscale
  have h := hmertens z Q hz (by exact_mod_cast hzQ) hlog hscale
  have hupper := (abs_le.mp h).2
  have hs := sievePrimes_reciprocal_le_open hzQ
  linarith

end Erdos421
