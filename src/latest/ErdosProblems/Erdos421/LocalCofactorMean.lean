import ErdosProblems.Erdos421.LocalCofactorWindows
import ErdosProblems.Erdos421.CofactorWindowLengthMean
import ErdosProblems.Erdos421.LocalLogarithmicMean

/-! # A local mean-square comparison for logarithmic prime-cofactor windows -/

namespace Erdos421

open MeasureTheory Filter Topology

theorem logarithmicPrimeCofactorWindow_log_continuousOn (P : Finset ℕ) (B z : ℕ)
    (δ : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun x ↦ logarithmicPrimeCofactorWindow P B z δ (Real.log x)) (Set.Icc a b) := by
  apply (logarithmicPrimeCofactorWindow_continuous P B z δ).comp_continuousOn
  exact continuousOn_id.log (fun x hx ↦ (ha.trans_le hx.1).ne')

theorem exists_local_logarithmic_cofactor_mean {k : ℕ} (hk : 0 < k) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, ∀ ε τ : ℝ, 0 < ε → ε ≤ 1 → 0 < τ →
      ∀ᶠ X : ℕ in atTop, ∀ Q D z w : ℕ, 0 < Q → 0 < D → 2 ≤ z → 0 < w →
        Q * (z * D ^ 2) < w ^ k →
        ((Q * (z * D ^ 2) : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) →
        16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ Real.log D / Real.log z →
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ w ≤ p ∧ p ≤ Q) →
        ∀ (δ₁ δ₂ ρ a b η : ℝ) (B : ℕ), B < w ^ k →
          0 < δ₁ → 0 < δ₂ → δ₁ ≤ ρ → δ₂ ≤ ρ → ρ ≤ 1 / 2 →
          0 < a → 0 ≤ η → a ≤ b → b ≤ (1 + η) * a → b - a ≤ X →
          (X : ℝ) ^ (1 / 10 : ℝ) ≤ δ₁ * a → (X : ℝ) ^ (1 / 10 : ℝ) ≤ δ₂ * a →
          b + δ₁ * a ≤ B → b + δ₂ * a ≤ B →
          (∫ x in a..b, |logarithmicPrimeCofactorWindow P B z δ₁ (Real.log x) -
            logarithmicPrimeCofactorWindow P B z δ₂ (Real.log x)| ^ 2) ≤
              36 * (b - a) * (ε * (∑ p ∈ P, (p : ℝ)⁻¹) * roughEulerProduct z) ^ 2 +
                τ * X / (Real.log X) ^ A + 6 * (b - a) * (K * (ρ + a⁻¹ + η)) ^ 2 := by
  obtain ⟨K₀, hK₀, hkernel⟩ := exists_local_logarithmic_cofactor_comparison
  let K := K₀ * (k : ℝ)
  have hK : 0 < K := mul_pos hK₀ (by exact_mod_cast hk)
  refine ⟨K, hK, ?_⟩
  intro A ε τ hε hε1 hτ
  filter_upwards [eventually_ge_atTop 1, additivePrimeCofactorWindow_length_comparison hk A
    hε hε1 (by positivity : 0 < τ / 3)] with X hX hmean
  intro Q D z w hQ hD hz hw hcut hMX hlevel P hP δ₁ δ₂ ρ a b η B hBw
    hδ₁ hδ₂ hδ₁ρ hδ₂ρ hρ ha hη hab hba hlen hY₁ hY₂ hB₁ hB₂
  have hPprime : ∀ p ∈ P, p.Prime ∧ w ≤ p := fun p hp ↦ ⟨(hP p hp).1, (hP p hp).2.1⟩
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hlength : 1 ≤ (X : ℝ) ^ (1 / 10 : ℝ) := Real.one_le_rpow hX1 (by norm_num)
  have hbound (δ : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
      (hY : (X : ℝ) ^ (1 / 10 : ℝ) ≤ δ * a) (x : ℝ) (hx : x ∈ Set.Icc a b) :
      |logarithmicPrimeCofactorWindow P B z δ (Real.log x) -
        additivePrimeCofactorWindow P B z (δ * a) x| ≤ K * (ρ + a⁻¹ + η) := by
    apply (hkernel P B z w k hw hBw hPprime δ a η x hδ (hδρ.trans hρ) ha hη hx.1
      (hx.2.trans hba) (hlength.trans hY)).trans
    exact mul_le_mul_of_nonneg_left (by linarith) hK.le
  have hFI : IntervalIntegrable (fun x ↦ |logarithmicPrimeCofactorWindow P B z δ₁ (Real.log x) -
      logarithmicPrimeCofactorWindow P B z δ₂ (Real.log x)| ^ 2) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab
      (((logarithmicPrimeCofactorWindow_log_continuousOn P B z δ₁ ha).sub
        (logarithmicPrimeCofactorWindow_log_continuousOn P B z δ₂ ha)).abs.pow 2)
  have hGI : IntervalIntegrable (fun x ↦ |additivePrimeCofactorWindow P B z (δ₁ * a) x -
      additivePrimeCofactorWindow P B z (δ₂ * a) x| ^ 2) volume a b :=
    (((additivePrimeCofactorWindow_continuous P B z (δ₁ * a)).sub
      (additivePrimeCofactorWindow_continuous P B z (δ₂ * a))).abs.pow 2).intervalIntegrable a b
  have hE : 0 ≤ K * (ρ + a⁻¹ + η) := by have hρpos := hδ₁.trans_le hδ₁ρ; positivity
  have hb := interval_square_comparison_of_error
    (fun x ↦ logarithmicPrimeCofactorWindow P B z δ₁ (Real.log x))
    (fun x ↦ logarithmicPrimeCofactorWindow P B z δ₂ (Real.log x))
    (additivePrimeCofactorWindow P B z (δ₁ * a)) (additivePrimeCofactorWindow P B z (δ₂ * a))
    hab hE hFI hGI (hbound δ₁ hδ₁ hδ₁ρ hY₁) (hbound δ₂ hδ₂ hδ₂ρ hY₂)
  have hm := hmean Q D z w hQ hD hz hw hcut hMX hlevel P hP (δ₁ * a) (δ₂ * a)
    a b B hY₁ hY₂ ha.le hab hlen hB₁ hB₂
  apply hb.trans
  calc
    _ ≤ 3 * (12 * (b - a) * (ε * (∑ p ∈ P, (p : ℝ)⁻¹) * roughEulerProduct z) ^ 2 +
        τ / 3 * X / (Real.log X) ^ A) + 6 * (b - a) * (K * (ρ + a⁻¹ + η)) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hm (by norm_num)) le_rfl
    _ = _ := by ring

end Erdos421
