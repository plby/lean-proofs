import ErdosProblems.Erdos67b.MRTDualRamareBlock

/-! # Summing a finite partition of actual minor-arc Ramaré prime blocks -/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

theorem mrtRawRamarePrimeSum_partition (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ)
    (V : Finset ℕ) (D : ℕ → Finset ℕ)
    (hpartition : Set.PairwiseDisjoint (↑V) D) (hcover : V.biUnion D = primesInBlock I)
    (Z : ℕ) (f : ℕ → ℂ) (n H : ℕ) (α : ℝ) :
    mrtRawRamarePrimeSum blocks I (primesInBlock I) Z f n H α =
      ∑ j ∈ V, mrtRawRamarePrimeSum blocks I (D j) Z f n H α := by
  unfold mrtRawRamarePrimeSum
  rw [← hcover, Finset.sum_biUnion hpartition]

theorem mrtNorm_sum_pow_four_le_card_four {ι : Type*} (V : Finset ι) (A : ι → ℂ)
    {B : ℝ} (hB : ∀ j ∈ V, ‖A j‖ ^ 4 ≤ B) :
    ‖∑ j ∈ V, A j‖ ^ 4 ≤ (V.card : ℝ) ^ 4 * B := by
  calc
    _ ≤ (∑ j ∈ V, ‖A j‖) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 4
    _ ≤ (V.card : ℝ) ^ 3 * ∑ j ∈ V, ‖A j‖ ^ 4 :=
      sum_norm_pow_four_le_card_cube_mul_fourthMoment V A
    _ ≤ (V.card : ℝ) ^ 3 * ∑ _j ∈ V, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hB) (by positivity)
    _ = _ := by simp; ring

theorem mrtMinorArc_log_denominator_discard {P W : ℕ} {A : ℝ}
    (hW : 0 < W) (hA : 0 ≤ A) (hlog : 1 ≤ Real.log P) :
    A / ((W : ℝ) * Real.log P ^ 4) ≤ A / W := by
  have hp : (1 : ℝ) ≤ Real.log P ^ 4 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hlog 4
  apply div_le_div_of_nonneg_left hA (by exact_mod_cast hW)
  simpa using mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg W)

theorem mrtExists_finiteRamare_minorArc_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ H W q : ℕ, ∀ a : ℤ, ∀ α : ℝ,
      2 ≤ W → W ≤ q → q ≤ H / W + 1 →
      Nat.Coprime a.natAbs q → |α - (a : ℝ) / q| ≤ (W : ℝ) / ((H : ℝ) * q) →
      ∀ (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ) (V : Finset ℕ)
        (D : ℕ → Finset ℕ) (P : ℕ → ℕ) (Z Y : ℕ) (f θ : ℕ → ℂ),
        H ≤ Y → 1 ≤ H → Set.PairwiseDisjoint (↑V) D → V.biUnion D = primesInBlock I →
        (∀ j ∈ V, D j ⊆ dyadicPrimeBlock (P j) 0) →
        (∀ j ∈ V, W ^ 200 ≤ P j ∧ P j ≤ H / W ^ 3 ∧ 1 ≤ Real.log (P j)) →
        (∀ J ∈ blocks, J ≠ I → Disjoint (primesInBlock I) (primesInBlock J)) →
        (∀ r, 0 < r → ‖f r‖ ≤ 1) → (∀ n ∈ Finset.Ioc Y (2 * Y), ‖θ n‖ ≤ 1) →
        ‖∑ n ∈ Finset.Ioc Y (2 * Y),
          θ n * mrtRawRamarePrimeSum blocks I (primesInBlock I) Z f n H α‖ ^ 4 ≤
          C * (V.card : ℝ) ^ 4 * (H : ℝ) ^ 4 * (Y : ℝ) ^ 4 * Real.log H / W := by
  obtain ⟨C, hC, hsaving⟩ := mrtExists_rawRamareBlock_minorArc_saving
  refine ⟨C, hC, ?_⟩
  intro H W q a α hW hWq hq ha hα blocks I V D P Z Y f θ hHY hH hpart hcover hD hP hdisj hf hθ
  have hlog : 0 ≤ Real.log H := Real.log_nonneg (by exact_mod_cast hH)
  have hblock (j : ℕ) (hj : j ∈ V) :
      ‖∑ n ∈ Finset.Ioc Y (2 * Y), θ n * mrtRawRamarePrimeSum blocks I (D j) Z f n H α‖ ^ 4 ≤
        C * (H : ℝ) ^ 4 * (Y : ℝ) ^ 4 * Real.log H / W := by
    have hDI : D j ⊆ primesInBlock I := by
      rw [← hcover]
      exact Finset.subset_biUnion_of_mem D hj
    apply (hsaving H W (P j) q a α hW hWq hq (hP j hj).1 (hP j hj).2.1 ha hα
      blocks I (D j) Z Y f θ hHY hDI (hD j hj) hdisj hf hθ).trans
    exact mrtMinorArc_log_denominator_discard (by omega) (by positivity) (hP j hj).2.2
  have hsum : (∑ n ∈ Finset.Ioc Y (2 * Y),
      θ n * mrtRawRamarePrimeSum blocks I (primesInBlock I) Z f n H α) =
      ∑ j ∈ V, ∑ n ∈ Finset.Ioc Y (2 * Y),
        θ n * mrtRawRamarePrimeSum blocks I (D j) Z f n H α := by
    simp_rw [mrtRawRamarePrimeSum_partition blocks I V D hpart hcover, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hsum]
  apply (mrtNorm_sum_pow_four_le_card_four V _ hblock).trans_eq
  ring

end

end Erdos67b
