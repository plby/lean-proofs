import ErdosProblems.Erdos421.RealProductWindowEnergy

/-! # Uniform variance bounds for the actual frozen-cutoff prime blocks -/

namespace Erdos421

open MeasureTheory Filter Topology

theorem logarithmic_prime_block_variance {β θ e A ε : ℝ}
    (hβ : 0 < β) (hθ : θ < 1 / 5) (he : 0 < e) (he' : e < 9 / 10)
    (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ L : ℝ, 2 ≤ L ∧ ∀ᶠ X : ℕ in atTop,
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ (Real.log X) ^ (-L) ∧
      ∀ H J B z : ℕ, 0 < H → J ≤ H → 3 * X ≤ B →
      (X : ℝ) ^ β ≤ H → (H : ℝ) ≤ (X : ℝ) ^ θ → ∀ ρ₁ ρ₂ : ℝ,
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ₁ → ρ₁ ≤ (Real.log X) ^ (-L) →
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ₂ → ρ₂ ≤ (Real.log X) ^ (-L) →
      (∫ y in Real.log (X : ℝ)..Real.log (2 * X : ℝ),
        |logarithmicPrimeCofactorWindow (primeBlockSupport H J) B z ρ₁ y -
          logarithmicPrimeCofactorWindow (primeBlockSupport H J) B z ρ₂ y| ^ 2) ≤
            ε / (Real.log X) ^ A := by
  obtain ⟨L, hL, hmean⟩ := prime_cofactor_full_window_variance hβ hθ he he' hA hε
    (by norm_num : (0 : ℝ) < 1)
  refine ⟨L, hL, ?_⟩
  have hloglarge : ∀ᶠ X : ℕ in atTop, 2 ≤ Real.log X :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hmean, hloglarge, eventually_ge_atTop 1] with X hmeanX hlog hX
  refine ⟨hmeanX.1, ?_⟩
  intro H J B z hH hJ hB hHlo hHhi ρ₁ ρ₂ hρ₁lo hρ₁hi hρ₂lo hρ₂hi
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  have hBreal : 3 * (X : ℝ) ≤ B := by exact_mod_cast hB
  have hmin : 0 < 16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) := by positivity
  have hρ₁ : 0 < ρ₁ := hmin.trans_le hρ₁lo
  have hρ₂ : 0 < ρ₂ := hmin.trans_le hρ₂lo
  have hwidth := inverse_log_window_le_support_width hlog hL
  have hpos : ∀ p ∈ primeBlockSupport H J, 0 < p :=
    fun p hp ↦ (Finset.mem_filter.mp hp).2.pos
  have hcoef : ∀ n ∈ Finset.Icc 1 B, ‖(roughIndicator n z : ℂ)‖ ≤ 1 := by
    intro n hn
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (roughIndicator_nonneg n z)]
    exact roughIndicator_le_one n z
  have hbound := hmeanX.2 H J B hH hJ hHlo hHhi (fun n ↦ (roughIndicator n z : ℂ)) hcoef
    ρ₁ ρ₂ hρ₁lo hρ₁hi hρ₂lo hρ₂hi
  apply le_trans _ hbound
  apply real_product_window_interval_energy_le _ _ _ _ 1 hρ₁ hρ₂
    (Real.log_le_log hXp (by linarith))
    (logarithmicPrimeCofactorWindow (primeBlockSupport H J) B z ρ₁)
    (logarithmicPrimeCofactorWindow (primeBlockSupport H J) B z ρ₂)
    (logarithmicPrimeCofactorWindow_continuous _ _ _ _)
    (logarithmicPrimeCofactorWindow_continuous _ _ _ _)
  · intro y hy
    exact logarithmicPrimeCofactorWindow_product _ hpos B z hρ₁
      ((logarithmic_window_endpoint_le hXp (hρ₁hi.trans hwidth) hy.2).trans hBreal)
  · intro y hy
    exact logarithmicPrimeCofactorWindow_product _ hpos B z hρ₂
      ((logarithmic_window_endpoint_le hXp (hρ₂hi.trans hwidth) hy.2).trans hBreal)

theorem logarithmic_double_cofactor_block_variance {k : ℕ} (hk : 0 < k) {β θ e A ε : ℝ}
    (hβ : 0 < β) (hθ : θ < 1 / 5) (he : 0 < e) (he' : e < 9 / 10)
    (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ L : ℝ, 2 ≤ L ∧ ∀ᶠ X : ℕ in atTop,
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ (Real.log X) ^ (-L) ∧
      ∀ H J B z w : ℕ, 0 < H → J ≤ H → 3 * X ≤ B → 0 < w → B < w ^ k →
      (X : ℝ) ^ β ≤ H → (H : ℝ) ≤ (X : ℝ) ^ θ →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ w ≤ p) → ∀ ρ₁ ρ₂ : ℝ,
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ₁ → ρ₁ ≤ (Real.log X) ^ (-L) →
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ₂ → ρ₂ ≤ (Real.log X) ^ (-L) →
      (∫ y in Real.log (X : ℝ)..Real.log (2 * X : ℝ),
        |logarithmicDoubleCofactorWindow P (primeBlockSupport H J) B z ρ₁ y -
          logarithmicDoubleCofactorWindow P (primeBlockSupport H J) B z ρ₂ y| ^ 2) ≤
            ε / (Real.log X) ^ A := by
  obtain ⟨L, hL, hmean⟩ := prime_cofactor_full_window_variance hβ hθ he he' hA hε
    (by exact_mod_cast hk : (0 : ℝ) < k)
  refine ⟨L, hL, ?_⟩
  have hloglarge : ∀ᶠ X : ℕ in atTop, 2 ≤ Real.log X :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hmean, hloglarge, eventually_ge_atTop 1] with X hmeanX hlog hX
  refine ⟨hmeanX.1, ?_⟩
  intro H J B z w hH hJ hB hw hBw hHlo hHhi P hP ρ₁ ρ₂ hρ₁lo hρ₁hi hρ₂lo hρ₂hi
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  have hBreal : 3 * (X : ℝ) ≤ B := by exact_mod_cast hB
  have hmin : 0 < 16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) := by positivity
  have hρ₁ : 0 < ρ₁ := hmin.trans_le hρ₁lo
  have hρ₂ : 0 < ρ₂ := hmin.trans_le hρ₂lo
  have hwidth := inverse_log_window_le_support_width hlog hL
  have hpos : ∀ q ∈ primeBlockSupport H J, 0 < q :=
    fun q hq ↦ (Finset.mem_filter.mp hq).2.pos
  have hPpos : ∀ p ∈ P, 0 < p := fun p hp ↦ (hP p hp).1.pos
  have hcoef := primeCofactorWeight_norm_bound P hw hBw hP z
  have hbound := hmeanX.2 H J B hH hJ hHlo hHhi
    (fun n ↦ (primeCofactorWeight P z n : ℂ)) hcoef ρ₁ ρ₂ hρ₁lo hρ₁hi hρ₂lo hρ₂hi
  apply le_trans _ hbound
  apply real_product_window_interval_energy_le _ _ _ _ 1 hρ₁ hρ₂
    (Real.log_le_log hXp (by linarith))
    (logarithmicDoubleCofactorWindow P (primeBlockSupport H J) B z ρ₁)
    (logarithmicDoubleCofactorWindow P (primeBlockSupport H J) B z ρ₂)
    (logarithmicDoubleCofactorWindow_continuous _ _ _ _ _)
    (logarithmicDoubleCofactorWindow_continuous _ _ _ _ _)
  · intro y hy
    exact logarithmicDoubleCofactorWindow_product _ _ hPpos hpos B z hρ₁
      ((logarithmic_window_endpoint_le hXp (hρ₁hi.trans hwidth) hy.2).trans hBreal)
  · intro y hy
    exact logarithmicDoubleCofactorWindow_product _ _ hPpos hpos B z hρ₂
      ((logarithmic_window_endpoint_le hXp (hρ₂hi.trans hwidth) hy.2).trans hBreal)

end Erdos421
