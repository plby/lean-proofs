import ErdosProblems.Erdos421.FullPrimeCofactorVariance
import ErdosProblems.Erdos421.TruncatedProductWindows
import ErdosProblems.Erdos421.LocalCofactorWindows

/-! # Passing product-window energy to the actual real cofactor counts -/

namespace Erdos421

open MeasureTheory

theorem logarithmic_window_endpoint_le {X δ y : ℝ} (hX : 0 < X)
    (hδ : δ ≤ Real.log (3 / 2)) (hy : y ≤ Real.log (2 * X)) :
    Real.exp (y + δ) ≤ 3 * X := by
  calc
    _ ≤ Real.exp (Real.log (2 * X) + Real.log (3 / 2)) :=
      Real.exp_le_exp.mpr (add_le_add hy hδ)
    _ = _ := by
      rw [Real.exp_add, Real.exp_log (by positivity : 0 < 2 * X),
        Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)]
      ring

theorem real_product_window_interval_energy_le (S T : Finset ℕ) (a b : ℕ → ℂ)
    (σ : ℝ) {δ ρ u v : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (huv : u ≤ v)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfeq : ∀ y ∈ Set.Icc u v, f y =
      (scaledProductWindow S T a b σ oneSidedSchwartzWindow δ y).re)
    (hgeq : ∀ y ∈ Set.Icc u v, g y =
      (scaledProductWindow S T a b σ oneSidedSchwartzWindow ρ y).re) :
    (∫ y in u..v, |f y - g y| ^ 2) ≤
      ∫ y in u..v, ‖scaledProductWindow S T a b σ oneSidedSchwartzWindow δ y -
        scaledProductWindow S T a b σ oneSidedSchwartzWindow ρ y‖ ^ 2 := by
  apply intervalIntegral.integral_mono_on huv (((hf.sub hg).abs.pow 2).intervalIntegrable u v)
    (scaledProductWindow_energy_integrable S T a b σ
      oneSidedSchwartzWindow hδ hρ).intervalIntegrable
  intro y hy
  change |f y - g y| ^ 2 ≤ _
  rw [hfeq y hy, hgeq y hy, ← Complex.sub_re]
  exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2

noncomputable def logarithmicDoubleCofactorWindow (P Q : Finset ℕ) (B z : ℕ) (δ y : ℝ) : ℝ :=
  ∑ q ∈ Q, (q : ℝ)⁻¹ * logarithmicPrimeCofactorWindow P (B / q) z δ (y - Real.log q)

theorem logarithmicDoubleCofactorWindow_continuous (P Q : Finset ℕ) (B z : ℕ) (δ : ℝ) :
    Continuous (logarithmicDoubleCofactorWindow P Q B z δ) := by
  apply continuous_finsetSum
  intro q hq
  exact continuous_const.mul ((logarithmicPrimeCofactorWindow_continuous P (B / q) z δ).comp
    (continuous_id.sub continuous_const))

theorem logarithmicDoubleCofactorWindow_product (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p) (hQ : ∀ q ∈ Q, 0 < q) (B z : ℕ)
    {δ y : ℝ} (hδ : 0 < δ) (hB : Real.exp (y + δ) ≤ B) :
    logarithmicDoubleCofactorWindow P Q B z δ y =
      (scaledProductWindow (Finset.Icc 1 B) Q (fun m ↦ (primeCofactorWeight P z m : ℂ))
        (fun _ ↦ 1) 1 oneSidedSchwartzWindow δ y).re :=
  logarithmic_double_cofactor_product P Q hP hQ B z hδ hB

end Erdos421
