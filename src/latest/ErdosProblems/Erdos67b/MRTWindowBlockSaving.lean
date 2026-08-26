import ErdosProblems.Erdos67b.MRTWindowFourthBound

/-! # Root-free minor-arc saving for one actual dual-window prime block -/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

theorem mrtNorm_weighted_sum_pow_four_le {ι : Type*} (S : Finset ι) (d A : ι → ℂ)
    (hd : ∀ m ∈ S, ‖d m‖ ≤ 1) :
    ‖∑ m ∈ S, d m * A m‖ ^ 4 ≤ (S.card : ℝ) ^ 3 * ∑ m ∈ S, ‖A m‖ ^ 4 := by
  apply (pow_le_pow_left₀ (norm_nonneg _) (show ‖∑ m ∈ S, d m * A m‖ ≤
      ∑ m ∈ S, ‖A m‖ from ?_) 4).trans
    (sum_norm_pow_four_le_card_cube_mul_fourthMoment S A)
  calc
    _ ≤ ∑ m ∈ S, ‖d m * A m‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hd m hm) (norm_nonneg _)).trans_eq (one_mul _)

theorem mrtWindowBlock_pow_four_le_mass (S : Finset ℕ) (Z H M Y P : ℕ)
    (c d θ : ℕ → ℂ) (α : ℝ) (hP : 0 < P) (hPH : P ≤ H)
    (hS : S ⊆ dyadicPrimeBlock P 0) (hc : ∀ p ∈ S, ‖c p‖ ≤ 1)
    (hd : ∀ m ∈ Finset.Icc 1 M, ‖d m‖ ≤ 1)
    (hθ : ∀ n ∈ Finset.Ioc Y (2 * Y), ‖θ n‖ ≤ 1) :
    ‖∑ m ∈ Finset.Icc 1 M, d m * mrtWindowPrimeRow S Z H Y c θ α m‖ ^ 4 ≤
      (M : ℝ) ^ 3 * (128 * Y * H ^ 3 * minorArcPrimeQuadrupleMass H P α) := by
  have hholder := mrtNorm_weighted_sum_pow_four_le (Finset.Icc 1 M) d
    (mrtWindowPrimeRow S Z H Y c θ α) hd
  have hcard : (Finset.Icc 1 M).card = M := by simp
  rw [hcard] at hholder
  exact hholder.trans (mul_le_mul_of_nonneg_left
    (mrtWindowPrimeRow_fourthMoment_le S Z H M Y P c θ α hP hPH hS hc hθ) (by positivity))

theorem mrtWindowBlock_pow_four_le_estimate (S : Finset ℕ) (Z H M Y P W : ℕ)
    (c d θ : ℕ → ℂ) (α C : ℝ) (hC : 0 < C) (hP : 0 < P) (hPH : P ≤ H)
    (hM : (M : ℝ) ≤ 3 * Y / P)
    (hS : S ⊆ dyadicPrimeBlock P 0) (hc : ∀ p ∈ S, ‖c p‖ ≤ 1)
    (hd : ∀ m ∈ Finset.Icc 1 M, ‖d m‖ ≤ 1)
    (hθ : ∀ n ∈ Finset.Ioc Y (2 * Y), ‖θ n‖ ≤ 1)
    (hquad : minorArcPrimeQuadrupleMass H P α ≤
      C * Real.log H * (H : ℝ) * (P : ℝ) ^ 3 / ((W : ℝ) * Real.log P ^ 4)) :
    ‖∑ m ∈ Finset.Icc 1 M, d m * mrtWindowPrimeRow S Z H Y c θ α m‖ ^ 4 ≤
      3456 * C * (H : ℝ) ^ 4 * (Y : ℝ) ^ 4 * Real.log H /
        ((W : ℝ) * Real.log P ^ 4) := by
  have hlog : 0 ≤ Real.log H := Real.log_nonneg (by exact_mod_cast hP.trans_le hPH)
  have hP' : (P : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hP
  have hbudget : 0 ≤ 128 * (Y : ℝ) * (H : ℝ) ^ 3 *
      (C * Real.log H * (H : ℝ) * (P : ℝ) ^ 3 / ((W : ℝ) * Real.log P ^ 4)) := by
    positivity
  calc
    _ ≤ (M : ℝ) ^ 3 * (128 * Y * H ^ 3 * minorArcPrimeQuadrupleMass H P α) :=
      mrtWindowBlock_pow_four_le_mass S Z H M Y P c d θ α hP hPH hS hc hd hθ
    _ ≤ (M : ℝ) ^ 3 * (128 * Y * H ^ 3 *
        (C * Real.log H * (H : ℝ) * (P : ℝ) ^ 3 / ((W : ℝ) * Real.log P ^ 4))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hquad (by positivity)
    _ ≤ (3 * Y / P) ^ 3 * (128 * Y * H ^ 3 *
        (C * Real.log H * (H : ℝ) * (P : ℝ) ^ 3 / ((W : ℝ) * Real.log P ^ 4))) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hM 3) hbudget
    _ = _ := by
      rw [div_pow]
      field_simp
      ring

theorem mrtExists_windowBlock_minorArc_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ H W P q : ℕ, ∀ a : ℤ, ∀ α : ℝ,
      2 ≤ W → W ≤ q → q ≤ H / W + 1 → W ^ 200 ≤ P → P ≤ H / W ^ 3 →
      Nat.Coprime a.natAbs q → |α - (a : ℝ) / q| ≤ (W : ℝ) / ((H : ℝ) * q) →
      ∀ (S : Finset ℕ) (Z Y : ℕ) (c d θ : ℕ → ℂ),
        S ⊆ dyadicPrimeBlock P 0 → (∀ p ∈ S, ‖c p‖ ≤ 1) →
        (∀ m ∈ Finset.Icc 1 (3 * Y / P), ‖d m‖ ≤ 1) →
        (∀ n ∈ Finset.Ioc Y (2 * Y), ‖θ n‖ ≤ 1) →
        ‖∑ m ∈ Finset.Icc 1 (3 * Y / P), d m * mrtWindowPrimeRow S Z H Y c θ α m‖ ^ 4 ≤
          C * (H : ℝ) ^ 4 * (Y : ℝ) ^ 4 * Real.log H /
            ((W : ℝ) * Real.log P ^ 4) := by
  obtain ⟨C, hC, hquad⟩ := mrtMinorArcQuadrupleEstimate
  refine ⟨3456 * C, by positivity, ?_⟩
  intro H W P q a α hW hWq hq hWP hPH ha hα S Z Y c d θ hS hc hd hθ
  have hP : 0 < P := (pow_pos (by omega : 0 < W) 200).trans_le hWP
  have hPH' : P ≤ H := hPH.trans (Nat.div_le_self _ _)
  apply mrtWindowBlock_pow_four_le_estimate S Z H (3 * Y / P) Y P W c d θ α C hC hP hPH'
    _ hS hc hd hθ (hquad H W P q a α hW hWq hq hWP hPH ha hα)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    (Nat.cast_div_le (m := 3 * Y) (n := P) (α := ℝ))

end

end Erdos67b
