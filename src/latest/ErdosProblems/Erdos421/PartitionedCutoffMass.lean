import ErdosProblems.Erdos421.ReciprocalBlockBounds

/-! # Total mass of the cutoff error over disjoint prime blocks -/

namespace Erdos421

open MeasureTheory

theorem partitioned_rough_cutoff_mass {ι : Type*}
    (I : Finset ι) (w z : ι → ℕ) (B : ℕ) {γ δ : ℝ} (hγ : 0 ≤ γ) (hδ : 0 < δ)
    (hsub : ∀ i ∈ I, sievePrimes (w i) (z i) ⊆ Finset.Icc 1 B)
    (hdisj : (I : Set ι).PairwiseDisjoint (fun i ↦ sievePrimes (w i) (z i)))
    (hsmall : ∀ i ∈ I, (∑ n ∈ sievePrimes (w i) (z i), (n : ℝ)⁻¹) ≤ γ) :
    (∫ y : ℝ, ∑ i ∈ I, logarithmicRoughBlockError B (w i) (z i) δ y) ≤
      γ * (harmonic B : ℝ) ^ 2 := by
  have hH : (0 : ℝ) ≤ harmonic B := by
    simpa only [harmonic_zero, Rat.cast_zero] using harmonic_cast_mono (Nat.zero_le B)
  calc
    _ = ∑ i ∈ I, ∫ y : ℝ, logarithmicRoughBlockError B (w i) (z i) δ y :=
      integral_finsetSum I (fun i _ ↦ logarithmicRoughBlockError_integrable B (w i) (z i) hδ)
    _ ≤ ∑ i ∈ I, (harmonic B : ℝ) *
        (∑ n ∈ sievePrimes (w i) (z i), (n : ℝ)⁻¹) ^ 2 :=
      Finset.sum_le_sum (fun i _ ↦ logarithmicRoughBlockError_integral_le B (w i) (z i) hδ)
    _ = (harmonic B : ℝ) * ∑ i ∈ I,
        (∑ n ∈ sievePrimes (w i) (z i), (n : ℝ)⁻¹) ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ (harmonic B : ℝ) * (γ * (harmonic B : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (reciprocal_block_square_sum_le I _ hγ hsub hdisj hsmall) hH
    _ = _ := by ring

theorem partitioned_cofactor_cutoff_mass {ι : Type*}
    (I : Finset ι) (w z : ι → ℕ) (P : Finset ℕ) (B : ℕ) {γ δ : ℝ}
    (hγ : 0 ≤ γ) (hδ : 0 < δ) (hP : P ⊆ Finset.Icc 1 B)
    (hsub : ∀ i ∈ I, sievePrimes (w i) (z i) ⊆ Finset.Icc 1 B)
    (hdisj : (I : Set ι).PairwiseDisjoint (fun i ↦ sievePrimes (w i) (z i)))
    (hsmall : ∀ i ∈ I, (∑ n ∈ sievePrimes (w i) (z i), (n : ℝ)⁻¹) ≤ γ) :
    (∫ y : ℝ, ∑ i ∈ I, logarithmicCofactorBlockError P B (w i) (z i) δ y) ≤
      γ * (harmonic B : ℝ) ^ 3 := by
  have hH : (0 : ℝ) ≤ harmonic B := by
    simpa only [harmonic_zero, Rat.cast_zero] using harmonic_cast_mono (Nat.zero_le B)
  have hPpos : ∀ p ∈ P, 0 < p := fun p hp ↦ (Finset.mem_Icc.mp (hP hp)).1
  have hPsum : 0 ≤ ∑ p ∈ P, (p : ℝ)⁻¹ :=
    Finset.sum_nonneg (fun p _ ↦ inv_nonneg.mpr (Nat.cast_nonneg p))
  calc
    _ = ∑ i ∈ I, ∫ y : ℝ, logarithmicCofactorBlockError P B (w i) (z i) δ y :=
      integral_finsetSum I (fun i _ ↦
        logarithmicCofactorBlockError_integrable P B (w i) (z i) hδ)
    _ ≤ ∑ i ∈ I, ((harmonic B : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)) *
        (∑ n ∈ sievePrimes (w i) (z i), (n : ℝ)⁻¹) ^ 2 :=
      Finset.sum_le_sum (fun i _ ↦
        logarithmicCofactorBlockError_integral_le P hPpos B (w i) (z i) hδ)
    _ = ((harmonic B : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)) *
        ∑ i ∈ I, (∑ n ∈ sievePrimes (w i) (z i), (n : ℝ)⁻¹) ^ 2 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ ((harmonic B : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹)) * (γ * (harmonic B : ℝ)) :=
      mul_le_mul_of_nonneg_left (reciprocal_block_square_sum_le I _ hγ hsub hdisj hsmall)
        (mul_nonneg hH hPsum)
    _ ≤ ((harmonic B : ℝ) * (harmonic B : ℝ)) * (γ * (harmonic B : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (reciprocal_sum_le_harmonic P hP) hH) (mul_nonneg hγ hH)
    _ = _ := by ring

end Erdos421
