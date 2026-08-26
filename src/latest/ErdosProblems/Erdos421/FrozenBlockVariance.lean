import ErdosProblems.Erdos421.ActualPrimeBlockVariance
import ErdosProblems.Erdos421.ClippedBuchstabWindows
import ErdosProblems.Erdos421.FiniteRealWindowEnergy

/-! # Variance of all frozen prime blocks with the exact finite partition loss -/

namespace Erdos421

open MeasureTheory Filter Topology

theorem frozenRoughBuchstabWindow_variance {β θ e A ε : ℝ}
    (hβ : 0 < β) (hθ : θ < 1 / 5) (he : 0 < e) (he' : e < 9 / 10)
    (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ L : ℝ, 2 ≤ L ∧ ∀ᶠ X : ℕ in atTop,
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ (Real.log X) ^ (-L) ∧
      ∀ W Z K N B : ℕ, 3 * X ≤ B →
      (X : ℝ) ^ β ≤ (W - 1 : ℕ) → (Z : ℝ) ≤ (X : ℝ) ^ θ → ∀ ρ₁ ρ₂ : ℝ,
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ₁ → ρ₁ ≤ (Real.log X) ^ (-L) →
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ₂ → ρ₂ ≤ (Real.log X) ^ (-L) →
      (∫ y in Real.log (X : ℝ)..Real.log (2 * X : ℝ),
        |frozenRoughBuchstabWindow W Z K N B ρ₁ y -
          frozenRoughBuchstabWindow W Z K N B ρ₂ y| ^ 2) ≤
          ((K * N : ℕ) : ℝ) ^ 2 * (ε / (Real.log X) ^ A) := by
  obtain ⟨L, hL, hmean⟩ := logarithmic_prime_block_variance hβ hθ he he' hA hε
  refine ⟨L, hL, ?_⟩
  filter_upwards [hmean, eventually_ge_atTop 1] with X hmeanX hX
  refine ⟨hmeanX.1, ?_⟩
  intro W Z K N B hB hW hZ ρ₁ ρ₂ hρ₁lo hρ₁hi hρ₂lo hρ₂hi
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  have hE : 0 ≤ ε / (Real.log X) ^ A :=
    div_nonneg hε.le (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hX)) _)
  have hblocks : ∀ i ∈ clippedPrimeIndices W Z K N,
      (∫ y in Real.log (X : ℝ)..Real.log (2 * X : ℝ),
        |logarithmicPrimeCofactorWindow (clippedPrimeBlock W Z N i) B
            (clippedPrimeLower W N i) ρ₁ y -
          logarithmicPrimeCofactorWindow (clippedPrimeBlock W Z N i) B
            (clippedPrimeLower W N i) ρ₂ y| ^ 2) ≤ ε / (Real.log X) ^ A := by
    intro i hi
    obtain ⟨H, J, hH, hWH, hHZ, hJ, heq⟩ := clippedPrimeBlock_parameters hi
    have hHlo : (X : ℝ) ^ β ≤ H := hW.trans (by exact_mod_cast (show W - 1 ≤ H by omega))
    have hHhi : (H : ℝ) ≤ (X : ℝ) ^ θ := (by exact_mod_cast hHZ.le : (H : ℝ) ≤ Z).trans hZ
    rw [heq]
    exact hmeanX.2 H J B (clippedPrimeLower W N i) hH hJ hB hHlo hHhi
      ρ₁ ρ₂ hρ₁lo hρ₁hi hρ₂lo hρ₂hi
  have hb := finite_real_window_energy_bound (clippedPrimeIndices W Z K N)
    (fun i ↦ logarithmicPrimeCofactorWindow (clippedPrimeBlock W Z N i) B
      (clippedPrimeLower W N i) ρ₁)
    (fun i ↦ logarithmicPrimeCofactorWindow (clippedPrimeBlock W Z N i) B
      (clippedPrimeLower W N i) ρ₂)
    (fun _ _ ↦ logarithmicPrimeCofactorWindow_continuous _ _ _ _)
    (fun _ _ ↦ logarithmicPrimeCofactorWindow_continuous _ _ _ _)
    (Real.log_le_log hXp (by linarith)) hblocks
  have hcard : ((clippedPrimeIndices W Z K N).card : ℝ) ≤ (K * N : ℕ) := by
    exact_mod_cast clippedPrimeIndices_card_le W Z K N
  exact hb.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) hE)

theorem frozenCofactorBuchstabWindow_variance {k : ℕ} (hk : 0 < k) {β θ e A ε : ℝ}
    (hβ : 0 < β) (hθ : θ < 1 / 5) (he : 0 < e) (he' : e < 9 / 10)
    (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ L : ℝ, 2 ≤ L ∧ ∀ᶠ X : ℕ in atTop,
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ (Real.log X) ^ (-L) ∧
      ∀ W Z K N B w : ℕ, 3 * X ≤ B → 0 < w → B < w ^ k →
      (X : ℝ) ^ β ≤ (W - 1 : ℕ) → (Z : ℝ) ≤ (X : ℝ) ^ θ →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ w ≤ p) → ∀ ρ₁ ρ₂ : ℝ,
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ₁ → ρ₁ ≤ (Real.log X) ^ (-L) →
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ₂ → ρ₂ ≤ (Real.log X) ^ (-L) →
      (∫ y in Real.log (X : ℝ)..Real.log (2 * X : ℝ),
        |frozenCofactorBuchstabWindow P W Z K N B ρ₁ y -
          frozenCofactorBuchstabWindow P W Z K N B ρ₂ y| ^ 2) ≤
            ((K * N : ℕ) : ℝ) ^ 2 * (ε / (Real.log X) ^ A) := by
  obtain ⟨L, hL, hmean⟩ := logarithmic_double_cofactor_block_variance hk hβ hθ he he' hA hε
  refine ⟨L, hL, ?_⟩
  filter_upwards [hmean, eventually_ge_atTop 1] with X hmeanX hX
  refine ⟨hmeanX.1, ?_⟩
  intro W Z K N B w hB hw hBw hW hZ P hP ρ₁ ρ₂ hρ₁lo hρ₁hi hρ₂lo hρ₂hi
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  have hE : 0 ≤ ε / (Real.log X) ^ A :=
    div_nonneg hε.le (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hX)) _)
  have hblocks : ∀ i ∈ clippedPrimeIndices W Z K N,
      (∫ y in Real.log (X : ℝ)..Real.log (2 * X : ℝ),
        |logarithmicDoubleCofactorWindow P (clippedPrimeBlock W Z N i) B
            (clippedPrimeLower W N i) ρ₁ y -
          logarithmicDoubleCofactorWindow P (clippedPrimeBlock W Z N i) B
            (clippedPrimeLower W N i) ρ₂ y| ^ 2) ≤ ε / (Real.log X) ^ A := by
    intro i hi
    obtain ⟨H, J, hH, hWH, hHZ, hJ, heq⟩ := clippedPrimeBlock_parameters hi
    have hHlo : (X : ℝ) ^ β ≤ H := hW.trans (by exact_mod_cast (show W - 1 ≤ H by omega))
    have hHhi : (H : ℝ) ≤ (X : ℝ) ^ θ := (by exact_mod_cast hHZ.le : (H : ℝ) ≤ Z).trans hZ
    rw [heq]
    exact hmeanX.2 H J B (clippedPrimeLower W N i) w hH hJ hB hw hBw hHlo hHhi P hP
      ρ₁ ρ₂ hρ₁lo hρ₁hi hρ₂lo hρ₂hi
  have hb := finite_real_window_energy_bound (clippedPrimeIndices W Z K N)
    (fun i ↦ logarithmicDoubleCofactorWindow P (clippedPrimeBlock W Z N i) B
      (clippedPrimeLower W N i) ρ₁)
    (fun i ↦ logarithmicDoubleCofactorWindow P (clippedPrimeBlock W Z N i) B
      (clippedPrimeLower W N i) ρ₂)
    (fun _ _ ↦ logarithmicDoubleCofactorWindow_continuous _ _ _ _ _)
    (fun _ _ ↦ logarithmicDoubleCofactorWindow_continuous _ _ _ _ _)
    (Real.log_le_log hXp (by linarith)) hblocks
  have hcard : ((clippedPrimeIndices W Z K N).card : ℝ) ≤ (K * N : ℕ) := by
    exact_mod_cast clippedPrimeIndices_card_le W Z K N
  exact hb.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) hE)

end Erdos421
