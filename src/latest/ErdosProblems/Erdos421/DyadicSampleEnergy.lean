import ErdosProblems.Erdos421.DyadicAmplitudeCover
import ErdosProblems.Erdos421.DirichletMomentParameters

/-! # Summing all amplitude classes with logarithmically many bins -/

namespace Erdos421

noncomputable def amplitudeLogConstant : ℝ := 2 / Real.log 2 + 1

theorem amplitudeLogConstant_pos : 0 < amplitudeLogConstant := by
  unfold amplitudeLogConstant
  positivity

theorem dyadic_sample_square_sum (F : Finset ℕ) (f g : ℕ → ℝ)
    (hf : ∀ i ∈ F, 0 ≤ f i ∧ f i ≤ 1) (hg : ∀ i ∈ F, 0 ≤ g i ∧ g i ≤ 1)
    {X : ℕ} (hX : 2 ≤ X) (hlog : 1 ≤ Real.log X) (hcard : (F.card : ℝ) ≤ X + 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hlarge : ∀ T : Finset ℕ, T ⊆ F → ∀ V W : ℝ, 0 < V → 0 < W →
      (∀ i ∈ T, V ≤ f i) → (∀ i ∈ T, W ≤ g i) → (T.card : ℝ) * V ^ 2 * W ^ 2 ≤ B) :
    (∑ i ∈ F, (f i) ^ 2 * (g i) ^ 2) ≤
      16 * amplitudeLogConstant ^ 2 * (Real.log X) ^ 2 * B + 2 / X := by
  let J := dirichletDyadicExponent X 1
  have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hL : 0 < Real.log X := by linarith
  have hJ : (J : ℝ) ≤ amplitudeLogConstant * Real.log X := by
    have hb := dirichletDyadicExponent_le_log hX (by omega : 1 ≤ X) le_rfl
      (by omega : X ≤ 2 * X) hlog 1
    simpa only [Nat.cast_one, mul_one, amplitudeLogConstant] using hb
  have hp : (1 / 2 : ℝ) ^ J ≤ (X : ℝ)⁻¹ := by
    have hpow : (X : ℝ) ≤ (2 : ℝ) ^ J := by
      exact_mod_cast (show X ≤ 2 ^ J from by
        simpa only [pow_one] using (dirichletDyadicExponent_support X 1).le)
    rw [one_div, inv_pow]
    exact inv_anti₀ hXp hpow
  have hsmall : (F.card : ℝ) * ((1 / 2 : ℝ) ^ J) ^ 2 ≤ 2 / X := by
    have hb := mul_le_mul hcard (pow_le_pow_left₀ (by positivity) hp 2)
      (sq_nonneg _) (by positivity)
    apply hb.trans
    have hid : ((X : ℝ) + 1) * ((X : ℝ)⁻¹) ^ 2 ≤ 2 / X := by
      apply (le_div_iff₀ hXp).mpr
      have he : (((X : ℝ) + 1) * ((X : ℝ)⁻¹) ^ 2) * X = ((X : ℝ) + 1) / X := by
        field_simp
      rw [he]
      exact (div_le_iff₀ hXp).mpr (by linarith)
    exact hid
  have hbig : 16 * (J : ℝ) ^ 2 * B ≤ 16 * amplitudeLogConstant ^ 2 * (Real.log X) ^ 2 * B := by
    have hb := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg J) hJ 2)
        (by norm_num : (0 : ℝ) ≤ 16)) hB
    simpa only [mul_pow, mul_assoc] using hb
  exact (dyadic_two_function_square_sum F f g hf hg J hlarge).trans (add_le_add hbig hsmall)

end Erdos421
