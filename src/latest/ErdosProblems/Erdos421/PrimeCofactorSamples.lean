import ErdosProblems.Erdos421.TwoFactorCommonConstant
import ErdosProblems.Erdos421.PrimePolynomialSupport

/-! # Simultaneous large values of an actual prime block and its cofactor -/

namespace Erdos421

open Complex

theorem prime_cofactor_sample_numeric_bound {X M H J : ℕ} (hX : 2 ≤ X)
    (hM : 1 ≤ M) (hH : 1 ≤ H) (hMX : M ≤ X) (hHX : H ≤ X) (hJ : J ≤ H)
    (hlog : 1 ≤ Real.log X) (hprod : (M : ℝ) * H = X)
    (S : Finset ℕ) (a : ℕ → ℂ) (hS : ∀ n ∈ S, M ≤ n ∧ n ≤ 2 * M)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ 1) {σ : ℝ} (hσ : 1 ≤ σ)
    {k : ℕ} (hk : 5 ≤ k) {e d η : ℝ} (he : 0 ≤ e) (hd : d ≤ e / 2)
    (hd' : d ≤ 1 / (60 * k)) (hHlo : (X : ℝ) ^ (1 / ((k : ℝ) + 1)) ≤ H)
    (hHhi : (H : ℝ) ≤ (X : ℝ) ^ (1 / (k : ℝ)))
    (hη : (X : ℝ) ^ (-d) ≤ η)
    (F : Finset ℕ) (t : ℕ → ℝ) {A B V W : ℝ} (hAB : A ≤ B)
    (hThi : B - A ≤ (X : ℝ) ^ (9 / 10 - e))
    (ht : ∀ i ∈ F, A ≤ t i ∧ t i ≤ B)
    (hsep : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → 1 ≤ |t i - t j|)
    (hV : 0 < V) (hW : 0 < W) (hV1 : V ≤ 1) (hWη : W ≤ η)
    (hlargeM : ∀ i ∈ F, V ≤ ‖dirichletPolynomial S a (σ + t i * I)‖)
    (hlargeH : ∀ i ∈ F, W ≤ ‖primeDirichletBlock H J (σ + t i * I)‖) :
    (F.card : ℝ) * V ^ 2 * W ^ 2 ≤ 2 * twoFactorSampleWeight k (Real.log X) * η := by
  let C := twoFactorSampleWeight k (Real.log X)
  obtain ⟨hC, hC1, hC2, hC3, hC4⟩ := twoFactorSampleWeight_bounds (by omega : 1 ≤ k) hlog
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hHp : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hXp : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hT : 0 ≤ B - A := sub_nonneg.mpr hAB
  have hmeanM : (F.card : ℝ) * ((M : ℝ) * V ^ 2) ≤ C * ((M : ℝ) + (B - A)) := by
    have hb := dirichletPolynomial_normalized_higher_mean hX hM hMX hlog S a hS ha hσ
      1 F t hAB ht hsep hV.le hlargeM
    simp only [pow_one] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right hC1 (by positivity))
  have hhalaszM : (F.card : ℝ) * ((M : ℝ) * V ^ 2) ^ 3 ≤
      C * ((M : ℝ) * ((M : ℝ) * V ^ 2) ^ 2 + M * (B - A)) := by
    have hb := dirichletPolynomial_normalized_halasz hX hM hMX hlog S a hS ha hσ
      1 F t hAB ht hsep hV hlargeM
    simp only [pow_one] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right hC2 (by positivity))
  have hSP : ∀ n ∈ primeBlockSupport H J, H ≤ n ∧ n ≤ 2 * H := primeBlockSupport_bounds hJ
  have hcoeff : ∀ n ∈ primeBlockSupport H J, ‖(1 : ℂ)‖ ≤ 1 := by simp
  have hlargeP : ∀ i ∈ F,
      W ≤ ‖dirichletPolynomial (primeBlockSupport H J) (fun _ ↦ 1) (σ + t i * I)‖ := by
    intro i hi
    rw [← primeDirichletBlock_eq_polynomial]
    exact hlargeH i hi
  have hmeanH : (F.card : ℝ) * ((H : ℝ) * W ^ 2) ^ k ≤ C * ((H : ℝ) ^ k + (B - A)) := by
    have hb := dirichletPolynomial_normalized_higher_mean hX hH hHX hlog
      (primeBlockSupport H J) (fun _ ↦ 1) hSP hcoeff hσ k F t hAB ht hsep hW.le hlargeP
    exact hb.trans (mul_le_mul_of_nonneg_right hC3 (by positivity))
  have hhalaszH : (F.card : ℝ) * ((H : ℝ) * W ^ 2) ^ (3 * k) ≤
      C * ((H : ℝ) ^ k * ((H : ℝ) * W ^ 2) ^ (2 * k) + (H : ℝ) ^ k * (B - A)) := by
    have hb := dirichletPolynomial_normalized_halasz hX hH hHX hlog
      (primeBlockSupport H J) (fun _ ↦ 1) hSP hcoeff hσ k F t hAB ht hsep hW hlargeP
    exact hb.trans (mul_le_mul_of_nonneg_right hC4 (by positivity))
  have huM : (M : ℝ) * V ^ 2 ≤ M := by
    have hp := pow_le_pow_left₀ hV.le hV1 2
    simpa only [one_pow, mul_one] using mul_le_mul_of_nonneg_left hp hMp.le
  have hwH : (H : ℝ) * W ^ 2 ≤ η ^ 2 * H := by
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW.le hWη 2) hHp.le
    simpa only [mul_comm] using hp
  have hb := twoFactor_scaled_power_range_saving hX1 (by positivity) (by positivity)
    (Nat.cast_nonneg F.card) hMp.le hHp.le hT hC hprod hk he hd hd' hHlo hHhi hThi hη
    huM hwH hmeanM hhalaszM hmeanH hhalaszH
  have hidentity : (F.card : ℝ) * ((M : ℝ) * V ^ 2) * ((H : ℝ) * W ^ 2) =
      ((F.card : ℝ) * V ^ 2 * W ^ 2) * X := by
    calc
      _ = ((F.card : ℝ) * V ^ 2 * W ^ 2) * ((M : ℝ) * H) := by ring
      _ = _ := by rw [hprod]
  rw [hidentity] at hb
  exact (mul_le_mul_iff_left₀ hXp).mp hb

end Erdos421
