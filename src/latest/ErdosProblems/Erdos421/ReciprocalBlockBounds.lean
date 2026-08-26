import ErdosProblems.Erdos421.LogarithmicBlockMass

/-! # Reciprocal mass of disjoint narrow blocks -/

namespace Erdos421

theorem reciprocal_sum_le_harmonic (S : Finset ℕ) {B : ℕ}
    (hS : S ⊆ Finset.Icc 1 B) :
    (∑ n ∈ S, (n : ℝ)⁻¹) ≤ (harmonic B : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  exact Finset.sum_le_sum_of_subset_of_nonneg hS
    (fun n _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg n))

theorem sievePrimes_reciprocal_le {w : ℕ} (hw : 0 < w) (z : ℕ) :
    (∑ p ∈ sievePrimes w z, (p : ℝ)⁻¹) ≤ (z - w : ℕ) / (w : ℝ) := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  calc
    _ ≤ ∑ _p ∈ sievePrimes w z, (w : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      exact inv_anti₀ hwR (by exact_mod_cast
        (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1)
    _ = ((sievePrimes w z).card : ℝ) / w := by simp [div_eq_mul_inv]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hwR.le
      exact_mod_cast (show (sievePrimes w z).card ≤ z - w from
        (Finset.card_filter_le _ _).trans_eq (Nat.card_Ico w z))

theorem reciprocal_block_square_sum_le {ι : Type*}
    (I : Finset ι) (S : ι → Finset ℕ) {B : ℕ} {γ : ℝ}
    (hγ : 0 ≤ γ) (hS : ∀ i ∈ I, S i ⊆ Finset.Icc 1 B)
    (hdisj : (I : Set ι).PairwiseDisjoint S)
    (hsmall : ∀ i ∈ I, (∑ n ∈ S i, (n : ℝ)⁻¹) ≤ γ) :
    (∑ i ∈ I, (∑ n ∈ S i, (n : ℝ)⁻¹) ^ 2) ≤ γ * (harmonic B : ℝ) := by
  classical
  calc
    _ ≤ ∑ i ∈ I, γ * ∑ n ∈ S i, (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right (hsmall i hi)
        (Finset.sum_nonneg (fun n _ ↦ inv_nonneg.mpr (Nat.cast_nonneg n)))
    _ = γ * ∑ n ∈ I.biUnion S, (n : ℝ)⁻¹ := by
      rw [Finset.sum_biUnion hdisj, Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hγ
      apply reciprocal_sum_le_harmonic
      intro n hn
      obtain ⟨i, hi, hn⟩ := Finset.mem_biUnion.mp hn
      exact hS i hi hn

theorem sievePrimes_narrow_reciprocal_le {H N w z : ℕ} (hH : 0 < H) (hN : 0 < N)
    (hHw : H ≤ w) (hlen : z - w ≤ H / N + 1) :
    (∑ p ∈ sievePrimes w z, (p : ℝ)⁻¹) ≤ (N : ℝ)⁻¹ + (H : ℝ)⁻¹ := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hHwR : (H : ℝ) ≤ w := by exact_mod_cast hHw
  have hlenR : ((z - w : ℕ) : ℝ) ≤ H / (N : ℝ) + 1 := by
    calc
      _ ≤ ((H / N + 1 : ℕ) : ℝ) := by exact_mod_cast hlen
      _ = ((H / N : ℕ) : ℝ) + 1 := by norm_cast
      _ ≤ _ := add_le_add (Nat.cast_div_le (α := ℝ) (m := H) (n := N)) le_rfl
  calc
    _ ≤ (z - w : ℕ) / (w : ℝ) := sievePrimes_reciprocal_le (hH.trans_le hHw) z
    _ ≤ (H / (N : ℝ) + 1) / H := by
      apply div_le_div₀ (by positivity) hlenR hHR hHwR
    _ = _ := by field_simp

end Erdos421
