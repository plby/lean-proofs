import ErdosProblems.Erdos421.FiniteWindowEnergy

/-! # Four active scales suffice for the cofactor-window energy -/

namespace Erdos421

open MeasureTheory

theorem scaledProductWindow_active_energy_le (T : Finset ℕ) (a b : ℕ → ℂ)
    {B K H : ℕ} (hB : B < 2 ^ K) (hH : 0 < H)
    (hT : ∀ n ∈ T, H ≤ n ∧ n ≤ 2 * H) {X δ ρ E : ℝ}
    (hX : 0 < X) (hδ : 0 < δ) (hρ : 0 < ρ) (hδmax : δ ≤ Real.log (3 / 2))
    (hρmax : ρ ≤ Real.log (3 / 2)) (hE : 0 ≤ E)
    (hmean : ∀ j ∈ activeProductScales K H X, (∫ y : ℝ,
      ‖scaledProductWindow (dyadicCofactorSupport B j) T a b 1 oneSidedSchwartzWindow δ y -
        scaledProductWindow (dyadicCofactorSupport B j) T a b 1 oneSidedSchwartzWindow ρ y‖ ^ 2)
        ≤ E) :
    (∫ y in Real.log X..Real.log (2 * X),
      ‖scaledProductWindow (Finset.Icc 1 B) T a b 1 oneSidedSchwartzWindow δ y -
        scaledProductWindow (Finset.Icc 1 B) T a b 1 oneSidedSchwartzWindow ρ y‖ ^ 2)
        ≤ 16 * E := by
  have hlogle : Real.log X ≤ Real.log (2 * X) := Real.log_le_log hX (by linarith)
  have hb := finite_product_window_energy_le (activeProductScales K H X)
    (dyadicCofactorSupport B) T a b 1 hδ hρ hlogle hmean
  have heq : (∫ y in Real.log X..Real.log (2 * X),
      ‖scaledProductWindow (Finset.Icc 1 B) T a b 1 oneSidedSchwartzWindow δ y -
        scaledProductWindow (Finset.Icc 1 B) T a b 1 oneSidedSchwartzWindow ρ y‖ ^ 2) =
        ∫ y in Real.log X..Real.log (2 * X), ‖∑ j ∈ activeProductScales K H X,
          (scaledProductWindow (dyadicCofactorSupport B j) T a b 1 oneSidedSchwartzWindow δ y -
            scaledProductWindow (dyadicCofactorSupport B j) T a b 1
              oneSidedSchwartzWindow ρ y)‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le hlogle] at hy
    dsimp only
    rw [scaledProductWindow_active_dyadic T a b hB hH hT hX hδ hδmax hy.1 hy.2,
      scaledProductWindow_active_dyadic T a b hB hH hT hX hρ hρmax hy.1 hy.2,
      Finset.sum_sub_distrib]
  rw [heq]
  apply hb.trans
  have hcard : ((activeProductScales K H X).card : ℝ) ≤ 4 := by
    exact_mod_cast activeProductScales_card_le_four K H hX
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (activeProductScales K H X).card) hcard 2
  norm_num at hs
  exact mul_le_mul_of_nonneg_right hs hE

end Erdos421
