import ErdosProblems.Erdos421.FrozenBlockVariance
import ErdosProblems.Erdos421.LogarithmicPrimePartition

/-! # The logarithmic partition loss is absorbed in the proved block variance -/

namespace Erdos421

open MeasureTheory Filter Topology

theorem prime_partition_variance_loss {K N : ℕ} {L A ε : ℝ} (hL : 0 < L) (hε : 0 ≤ ε)
    (hsize : ((K * N : ℕ) : ℝ) ≤ 6 * L ^ (11 : ℕ)) :
    ((K * N : ℕ) : ℝ) ^ 2 * (ε / 36 / L ^ (A + 22)) ≤ ε / L ^ A := by
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (K * N)) hsize 2
  apply (mul_le_mul_of_nonneg_right hs
    (div_nonneg (div_nonneg hε (by norm_num)) (Real.rpow_nonneg hL.le _))).trans_eq
  rw [Real.rpow_add hL]
  norm_num only [Real.rpow_ofNat]
  have hLA : L ^ A ≠ 0 := (Real.rpow_pos_of_pos hL A).ne'
  field_simp
  ring

theorem frozenRoughBuchstabWindow_log_saving {β θ e A ε : ℝ}
    (hβ : 0 < β) (hθ : θ < 1 / 5) (he : 0 < e) (he' : e < 9 / 10)
    (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ L : ℝ, 2 ≤ L ∧ ∀ᶠ X : ℕ in atTop,
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ (Real.log X) ^ (-L) ∧
      ∀ W Z B : ℕ, W ≤ Z → 3 * X ≤ B →
      (X : ℝ) ^ β ≤ (W - 1 : ℕ) → (Z : ℝ) ≤ (X : ℝ) ^ θ → ∀ ρ₁ ρ₂ : ℝ,
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ₁ → ρ₁ ≤ (Real.log X) ^ (-L) →
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ₂ → ρ₂ ≤ (Real.log X) ^ (-L) →
      (∫ y in Real.log (X : ℝ)..Real.log (2 * X : ℝ),
        |frozenRoughBuchstabWindow W Z (primePartitionDepth Z) (primePartitionCount X) B ρ₁ y -
          frozenRoughBuchstabWindow W Z (primePartitionDepth Z)
            (primePartitionCount X) B ρ₂ y| ^ 2) ≤
            ε / (Real.log X) ^ A := by
  obtain ⟨L, hL, hmean⟩ := frozenRoughBuchstabWindow_variance hβ hθ he he'
    (by linarith : 0 ≤ A + 22) (by positivity : 0 < ε / 36)
  refine ⟨L, hL, ?_⟩
  have hloglarge : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log X :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hmean, hloglarge, eventually_ge_atTop 1] with X hmeanX hlog hX
  refine ⟨hmeanX.1, ?_⟩
  intro W Z B hWZ hB hW hZ ρ₁ ρ₂ hρ₁lo hρ₁hi hρ₂lo hρ₂hi
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  have hZpos : 0 < Z := by
    have hWpos : 0 < W - 1 := by
      exact_mod_cast (Real.rpow_pos_of_pos hXp β).trans_le hW
    omega
  have hZX : (Z : ℝ) ≤ X := hZ.trans
    (Real.rpow_le_self_of_one_le (by exact_mod_cast hX) (by linarith))
  have hm := hmeanX.2 W Z (primePartitionDepth Z) (primePartitionCount X) B hB hW hZ
    ρ₁ ρ₂ hρ₁lo hρ₁hi hρ₂lo hρ₂hi
  exact hm.trans (prime_partition_variance_loss (by linarith) hε.le
    (primePartition_size_le hZpos hZX hlog))

theorem frozenCofactorBuchstabWindow_log_saving {k : ℕ} (hk : 0 < k) {β θ e A ε : ℝ}
    (hβ : 0 < β) (hθ : θ < 1 / 5) (he : 0 < e) (he' : e < 9 / 10)
    (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ L : ℝ, 2 ≤ L ∧ ∀ᶠ X : ℕ in atTop,
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ (Real.log X) ^ (-L) ∧
      ∀ W Z B w : ℕ, W ≤ Z → 3 * X ≤ B → 0 < w → B < w ^ k →
      (X : ℝ) ^ β ≤ (W - 1 : ℕ) → (Z : ℝ) ≤ (X : ℝ) ^ θ →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ w ≤ p) → ∀ ρ₁ ρ₂ : ℝ,
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ₁ → ρ₁ ≤ (Real.log X) ^ (-L) →
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ₂ → ρ₂ ≤ (Real.log X) ^ (-L) →
      (∫ y in Real.log (X : ℝ)..Real.log (2 * X : ℝ),
        |frozenCofactorBuchstabWindow P W Z (primePartitionDepth Z)
            (primePartitionCount X) B ρ₁ y -
          frozenCofactorBuchstabWindow P W Z (primePartitionDepth Z)
            (primePartitionCount X) B ρ₂ y| ^ 2) ≤ ε / (Real.log X) ^ A := by
  obtain ⟨L, hL, hmean⟩ := frozenCofactorBuchstabWindow_variance hk hβ hθ he he'
    (by linarith : 0 ≤ A + 22) (by positivity : 0 < ε / 36)
  refine ⟨L, hL, ?_⟩
  have hloglarge : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log X :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hmean, hloglarge, eventually_ge_atTop 1] with X hmeanX hlog hX
  refine ⟨hmeanX.1, ?_⟩
  intro W Z B w hWZ hB hw hBw hW hZ P hP ρ₁ ρ₂ hρ₁lo hρ₁hi hρ₂lo hρ₂hi
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  have hZpos : 0 < Z := by
    have hWpos : 0 < W - 1 := by
      exact_mod_cast (Real.rpow_pos_of_pos hXp β).trans_le hW
    omega
  have hZX : (Z : ℝ) ≤ X := hZ.trans
    (Real.rpow_le_self_of_one_le (by exact_mod_cast hX) (by linarith))
  have hm := hmeanX.2 W Z (primePartitionDepth Z) (primePartitionCount X) B w hB hw hBw hW hZ P hP
    ρ₁ ρ₂ hρ₁lo hρ₁hi hρ₂lo hρ₂hi
  exact hm.trans (prime_partition_variance_loss (by linarith) hε.le
    (primePartition_size_le hZpos hZX hlog))

end Erdos421
