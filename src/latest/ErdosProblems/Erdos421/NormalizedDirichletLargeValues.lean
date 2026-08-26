import ErdosProblems.Erdos421.DirichletMeanPrefactor
import ErdosProblems.Erdos421.LargeValueNormalization

/-! # Actual large-value estimates with uniform logarithmic constants -/

namespace Erdos421

open Complex

noncomputable def dirichletNormalizedMeanConstant (k : ℕ) : ℝ :=
  dirichletMeanPrefactorConstant k * dirichletMomentConstant k

noncomputable def dirichletNormalizedHalaszConstant (k : ℕ) : ℝ :=
  dirichletHalaszPrefactorConstant k * dirichletMomentConstant k *
      (dirichletDyadicLogConstant k) ^ 2 +
    1280 ^ 2 * dirichletHalaszPrefactorConstant k * (dirichletMomentConstant k) ^ 3 *
      (dirichletDyadicLogConstant k) ^ 6

theorem dirichletNormalizedMeanConstant_pos (k : ℕ) :
    0 < dirichletNormalizedMeanConstant k :=
  mul_pos (dirichletMeanPrefactorConstant_pos k) (dirichletMomentConstant_pos k)

theorem dirichletNormalizedHalaszConstant_pos (k : ℕ) :
    0 < dirichletNormalizedHalaszConstant k := by
  have := dirichletHalaszPrefactorConstant_pos k
  have := dirichletMomentConstant_pos k
  have := dirichletDyadicLogConstant_pos k
  unfold dirichletNormalizedHalaszConstant
  positivity

theorem dirichletPolynomial_normalized_higher_mean {X M : ℕ} (hX : 2 ≤ X) (hM : 1 ≤ M)
    (hMX : M ≤ X) (hlog : 1 ≤ Real.log X) (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, M ≤ n ∧ n ≤ 2 * M) (ha : ∀ n ∈ S, ‖a n‖ ≤ 1)
    {σ : ℝ} (hσ : 1 ≤ σ) (k : ℕ) (F : Finset ℕ) (t : ℕ → ℝ)
    {u v V : ℝ} (huv : u ≤ v) (ht : ∀ i ∈ F, u ≤ t i ∧ t i ≤ v)
    (hsep : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → 1 ≤ |t i - t j|)
    (hV : 0 ≤ V) (hlarge : ∀ i ∈ F, V ≤ ‖dirichletPolynomial S a (σ + t i * I)‖) :
    F.card * ((M : ℝ) * V ^ 2) ^ k ≤
      (dirichletNormalizedMeanConstant k * (Real.log X) ^ (k ^ 2 + 3)) *
        ((M : ℝ) ^ k + (v - u)) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hL : 0 < Real.log X := by linarith
  have hT : 0 ≤ v - u := sub_nonneg.mpr huv
  have hmean := dirichletPolynomial_higher_large_values S a hM hS ha hσ k F t huv ht hsep hV hlarge
  have hpref := dirichletMean_prefactor_ambient hX hM hMX hlog k hT
  have henergy := dirichletMomentEnergy_ambient_bound hX hM (by omega : 1 ≤ 2 * M)
    hMX le_rfl hlog k
  have hG : 0 ≤ dirichletMomentEnergy M (2 * M) k := by
    unfold dirichletMomentEnergy
    positivity
  have hb : F.card * V ^ (2 * k) ≤
      (dirichletMeanPrefactorConstant k * (Real.log X) ^ 3) * ((v - u) + (M : ℝ) ^ k) *
        ((dirichletMomentConstant k * (Real.log X) ^ (k ^ 2)) / (M : ℝ) ^ k) := by
    apply hmean.trans
    have he : v + 1 - u = (v - u) + 1 := by ring
    rw [he]
    exact mul_le_mul hpref henergy hG (by
      have := dirichletMeanPrefactorConstant_pos k
      positivity)
  have hn := largeValue_normalized_mean hMp k hb
  apply hn.trans_eq
  unfold dirichletNormalizedMeanConstant
  rw [show k ^ 2 + 3 = 3 + k ^ 2 by omega, pow_add]
  ring

theorem dirichletHalasz_log_factor {L : ℝ} (hL : 1 ≤ L) (k : ℕ) :
    (dirichletHalaszPrefactorConstant k * L ^ 2) *
        (dirichletMomentConstant k * L ^ (k ^ 2)) *
        (dirichletDyadicLogConstant k * L) ^ 2 +
      1280 ^ 2 * (dirichletHalaszPrefactorConstant k * L ^ 2) *
        (dirichletMomentConstant k * L ^ (k ^ 2)) ^ 3 *
        (dirichletDyadicLogConstant k * L) ^ 6 ≤
      dirichletNormalizedHalaszConstant k * L ^ (3 * k ^ 2 + 8) := by
  let A := dirichletHalaszPrefactorConstant k * dirichletMomentConstant k *
    (dirichletDyadicLogConstant k) ^ 2
  let B := 1280 ^ 2 * dirichletHalaszPrefactorConstant k * (dirichletMomentConstant k) ^ 3 *
    (dirichletDyadicLogConstant k) ^ 6
  have hA : 0 ≤ A := by
    have := dirichletHalaszPrefactorConstant_pos k
    have := dirichletMomentConstant_pos k
    dsimp only [A]
    positivity
  have he : (dirichletHalaszPrefactorConstant k * L ^ 2) *
        (dirichletMomentConstant k * L ^ (k ^ 2)) *
        (dirichletDyadicLogConstant k * L) ^ 2 +
      1280 ^ 2 * (dirichletHalaszPrefactorConstant k * L ^ 2) *
        (dirichletMomentConstant k * L ^ (k ^ 2)) ^ 3 *
        (dirichletDyadicLogConstant k * L) ^ 6 =
      A * L ^ (k ^ 2 + 4) + B * L ^ (3 * k ^ 2 + 8) := by
    dsimp only [A, B]
    simp only [mul_pow, pow_add, ← pow_mul]
    ring
  rw [he]
  have hp : L ^ (k ^ 2 + 4) ≤ L ^ (3 * k ^ 2 + 8) :=
    pow_le_pow_right₀ hL (by omega)
  have hb := add_le_add (mul_le_mul_of_nonneg_left hp hA) (le_refl (B * L ^ (3 * k ^ 2 + 8)))
  exact hb.trans_eq (by dsimp only [A, B, dirichletNormalizedHalaszConstant]; ring)

theorem dirichletPolynomial_normalized_halasz {X M : ℕ} (hX : 2 ≤ X) (hM : 1 ≤ M)
    (hMX : M ≤ X) (hlog : 1 ≤ Real.log X) (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, M ≤ n ∧ n ≤ 2 * M) (ha : ∀ n ∈ S, ‖a n‖ ≤ 1)
    {σ : ℝ} (hσ : 1 ≤ σ) (k : ℕ) (F : Finset ℕ) (t : ℕ → ℝ)
    {u v V : ℝ} (huv : u ≤ v) (ht : ∀ i ∈ F, u ≤ t i ∧ t i ≤ v)
    (hsep : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → 1 ≤ |t i - t j|)
    (hV : 0 < V) (hlarge : ∀ i ∈ F, V ≤ ‖dirichletPolynomial S a (σ + t i * I)‖) :
    F.card * ((M : ℝ) * V ^ 2) ^ (3 * k) ≤
      (dirichletNormalizedHalaszConstant k * (Real.log X) ^ (3 * k ^ 2 + 8)) *
        ((M : ℝ) ^ k * ((M : ℝ) * V ^ 2) ^ (2 * k) + (M : ℝ) ^ k * (v - u)) := by
  let K := dirichletDyadicExponent (2 * M) k
  let G := dirichletMomentEnergy M (2 * M) k
  let C : ℝ := 10240 * K * (2 ^ K : ℕ) * Real.log ((2 ^ K : ℕ) + 2 : ℝ)
  have hK : 0 < K := dirichletDyadicExponent_pos _ _
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMk : 0 < (M : ℝ) ^ k := pow_pos hMp _
  have hL : 0 < Real.log X := by linarith
  have hT : 0 ≤ v - u := sub_nonneg.mpr huv
  have hG : 0 ≤ G := by dsimp only [G, dirichletMomentEnergy]; positivity
  have hD : 0 ≤ dirichletMomentConstant k * (Real.log X) ^ (k ^ 2) :=
    mul_nonneg (dirichletMomentConstant_pos k).le (pow_nonneg hL.le _)
  have hE : 0 ≤ dirichletHalaszPrefactorConstant k * (Real.log X) ^ 2 :=
    mul_nonneg (dirichletHalaszPrefactorConstant_pos k).le (sq_nonneg _)
  have hKL : (K : ℝ) ≤ dirichletDyadicLogConstant k * Real.log X :=
    dirichletDyadicExponent_le_log hX (by omega) hMX le_rfl hlog k
  have henergy : G * (M : ℝ) ^ k ≤ dirichletMomentConstant k * (Real.log X) ^ (k ^ 2) :=
    (le_div_iff₀ hMk).mp (dirichletMomentEnergy_ambient_bound hX hM (by omega)
      hMX le_rfl hlog k)
  have hprefactor : C ≤ (dirichletHalaszPrefactorConstant k * (Real.log X) ^ 2) * (M : ℝ) ^ k :=
    dirichletHalasz_prefactor_ambient hX (by omega) hMX le_rfl hlog k
  have hbound := dirichletPolynomial_higher_halasz S a hM hS ha hσ k hK
    (dirichletDyadicExponent_support _ _) F t huv ht hsep hV hlarge
  have hb := largeValue_normalized_halasz hMp hV hKr hG hT hD hE hKL k
    henergy hprefactor hbound
  exact hb.trans (mul_le_mul_of_nonneg_right (dirichletHalasz_log_factor hlog k) (by positivity))

end Erdos421
