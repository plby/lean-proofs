import ErdosProblems.Erdos421.CofactorKernelComparison
import ErdosProblems.Erdos421.LocalLogarithmicWindows

/-! # Fixing the additive scale locally for a logarithmic cofactor window -/

namespace Erdos421

theorem exists_local_logarithmic_cofactor_comparison :
    ∃ K : ℝ, 0 < K ∧ ∀ (P : Finset ℕ) (B z w k : ℕ), 0 < w → B < w ^ k →
      (∀ p ∈ P, p.Prime ∧ w ≤ p) → ∀ δ a η x : ℝ,
      0 < δ → δ ≤ 1 / 2 → 0 < a → 0 ≤ η →
      a ≤ x → x ≤ (1 + η) * a → 1 ≤ δ * a →
      |logarithmicPrimeCofactorWindow P B z δ (Real.log x) -
        additivePrimeCofactorWindow P B z (δ * a) x| ≤ K * k * (δ + a⁻¹ + η) := by
  obtain ⟨K₁, hK₁, hlog⟩ := exists_logarithmicCofactorWindow_additive_comparison
  obtain ⟨K₂, hK₂, hscale⟩ := exists_additiveCofactorWindow_scale_bound
  refine ⟨K₁ + K₂, by positivity, ?_⟩
  intro P B z w k hw hB hP δ a η x hδ hδ1 ha hη hax hxa hδa
  have hx : 0 < x := ha.trans_le hax
  have hY : 0 < δ * a := mul_pos hδ ha
  have hYZ : δ * a ≤ δ * x := mul_le_mul_of_nonneg_left hax hδ.le
  have hZη : δ * x ≤ (1 + η) * (δ * a) := by
    have h := mul_le_mul_of_nonneg_left hxa hδ.le
    nlinarith
  have h₁ := hlog P B z w k hw hB hP δ x hδ hδ1 hx
  have h₂ := hscale P B z w k hw hB hP (δ * a) (δ * x) η x hY hYZ hZη hη
    (hδa.trans hYZ) hx.le
  have hinv : x⁻¹ ≤ a⁻¹ := inv_anti₀ ha hax
  have h₁' : |logarithmicPrimeCofactorWindow P B z δ (Real.log x) -
      additivePrimeCofactorWindow P B z (δ * x) x| ≤ K₁ * k * (δ + a⁻¹) :=
    h₁.trans (mul_le_mul_of_nonneg_left (add_le_add_right hinv δ)
      (mul_nonneg hK₁.le (Nat.cast_nonneg k)))
  have htri := abs_sub_le (logarithmicPrimeCofactorWindow P B z δ (Real.log x))
    (additivePrimeCofactorWindow P B z (δ * x) x) (additivePrimeCofactorWindow P B z (δ * a) x)
  rw [abs_sub_comm (additivePrimeCofactorWindow P B z (δ * x) x)] at htri
  calc
    _ ≤ K₁ * k * (δ + a⁻¹) + K₂ * k * η := htri.trans (add_le_add h₁' h₂)
    _ ≤ K₁ * k * (δ + a⁻¹ + η) + K₂ * k * (δ + a⁻¹ + η) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hη)
          (mul_nonneg hK₁.le (Nat.cast_nonneg k))
      · apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK₂.le (Nat.cast_nonneg k))
        have hbase : 0 ≤ δ + a⁻¹ := by positivity
        linarith
    _ = _ := by ring

theorem logarithmicPrimeCofactorWindow_continuous (P : Finset ℕ) (B z : ℕ) (δ : ℝ) :
    Continuous (logarithmicPrimeCofactorWindow P B z δ) := by
  apply continuous_finsetSum
  intro p hp
  exact continuous_const.mul ((logarithmicRoughWindow_continuous (B / p) z δ).comp
    (continuous_id.sub continuous_const))

end Erdos421
