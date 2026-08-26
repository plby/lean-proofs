import ErdosProblems.Erdos67b.MRSparseIntegerMean
import ErdosProblems.Erdos67b.MRExceptionalParameters

/-!
# Sparse cofactor samples on the exceptional class

The cofactor square mass and rounded rectangle length are substituted
into the proved sparse integer mean value. Small additional prime values
give the finite product bound. These are sampled estimates; passage from
the exceptional integral to samples remains a separate construction.
-/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

def mrSparseCofactorSampleBudget (M : ℝ) (U X : ℕ) (T : ℝ) : ℝ :=
  16 * (1 + 12 * Real.pi * (1 + Real.log (2 * T + 1))) +
    3200 * M * U / X * Real.sqrt (2 * T) * (1 + Real.log (16 * T)) ^ 2

theorem mrSparseCofactorSampleBudget_mono {M M' : ℝ} (hM : M ≤ M') (U X : ℕ) (T : ℝ) :
    mrSparseCofactorSampleBudget M U X T ≤ mrSparseCofactorSampleBudget M' U X T := by
  have hh := mul_le_mul_of_nonneg_right hM
    (show 0 ≤ 3200 * (U : ℝ) / X * Real.sqrt (2 * T) * (1 + Real.log (16 * T)) ^ 2 by positivity)
  unfold mrSparseCofactorSampleBudget
  apply add_le_add le_rfl
  convert hh using 1 <;> ring

theorem mrSparse_cofactor_subset_rectangle_le
    {A : Finset ℕ} {b : ℕ → ℂ} {L U X : ℕ}
    (hL : 0 < L) (hU : 0 < U) (hX : 0 < X) (hUL : U ≤ 2 * L)
    (hA : A ⊆ mrDyadicCofactorRectangle (L, U) X)
    (hb : ∀ m ∈ A, ‖b m‖ ≤ (m : ℝ)⁻¹)
    (S : Finset ℝ) {T : ℝ} (hT : 1 ≤ T)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|) :
    (∑ t ∈ S, ‖logarithmicDirichletPolynomial A b t‖ ^ 2) ≤
      mrSparseCofactorSampleBudget S.card U X T := by
  let M : ℕ := X / U + 1
  let N : ℕ := (2 * X) / L
  have hM : 0 < M := Nat.succ_pos _
  have hSlow (m : ℕ) (hm : m ∈ A) : M ≤ m :=
    Nat.succ_le_iff.mpr (Finset.mem_Ioc.mp (hA hm)).1
  have hSup (m : ℕ) (hm : m ∈ A) : m ≤ N := (Finset.mem_Ioc.mp (hA hm)).2
  have hApos (m : ℕ) (hm : m ∈ A) : 0 < m := hM.trans_le (hSlow m hm)
  have hmass : (∑ m ∈ A, ‖b m‖ ^ 2) ≤ 4 * (U : ℝ) / X := by
    calc
      _ ≤ ∑ _m ∈ A, (M : ℝ)⁻¹ ^ 2 := by
        apply Finset.sum_le_sum
        intro m hm
        have hi : (m : ℝ)⁻¹ ≤ (M : ℝ)⁻¹ :=
          inv_anti₀ (by exact_mod_cast hM) (by exact_mod_cast hSlow m hm)
        exact pow_le_pow_left₀ (norm_nonneg _) ((hb m hm).trans hi) 2
      _ = (A.card : ℝ) * (M : ℝ)⁻¹ ^ 2 := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((mrDyadicCofactorRectangle (L, U) X).card : ℝ) * (M : ℝ)⁻¹ ^ 2 := by gcongr
      _ = ((mrDyadicCofactorRectangle (L, U) X).card : ℝ) / (M : ℝ) ^ 2 := by rw [div_eq_mul_inv, inv_pow]
      _ ≤ _ := mrDyadicCofactorRectangle_cardRatio_cofactor_le hL hU hX hUL
  have hNU : N * U ≤ 4 * X := by
    calc
      _ ≤ N * (2 * L) := Nat.mul_le_mul_left N hUL
      _ = 2 * (L * N) := by ring
      _ ≤ 2 * (2 * X) := Nat.mul_le_mul_left 2 (Nat.mul_div_le _ _)
      _ = _ := by ring
  have hNUr : (N : ℝ) * U / X ≤ 4 := by
    apply (div_le_iff₀ (by exact_mod_cast hX : (0 : ℝ) < X)).mpr
    exact_mod_cast hNU
  have hlog : 0 ≤ Real.log (2 * T + 1) := Real.log_nonneg (by linarith)
  have hmean := mrSparse_integer_meanValue_le_support hApos hSup S hT hST hsep b
  calc
    _ ≤ mrSparseIntegerEnergyBudget N S.card T * ∑ m ∈ A, ‖b m‖ ^ 2 := hmean
    _ ≤ mrSparseIntegerEnergyBudget N S.card T * (4 * U / X) :=
      mul_le_mul_of_nonneg_left hmass (mrSparseIntegerEnergyBudget_nonneg N S.card hT)
    _ = 4 * ((N : ℝ) * U / X) * (1 + 12 * Real.pi * (1 + Real.log (2 * T + 1))) +
        3200 * S.card * U / X * Real.sqrt (2 * T) * (1 + Real.log (16 * T)) ^ 2 := by
      unfold mrSparseIntegerEnergyBudget
      ring
    _ ≤ _ := by
      unfold mrSparseCofactorSampleBudget
      have hh := mul_le_mul_of_nonneg_right hNUr
        (show 0 ≤ 1 + 12 * Real.pi * (1 + Real.log (2 * T + 1)) by positivity)
      nlinarith

theorem mrSparse_smallPrime_product_le
    {A : Finset ℕ} {b : ℕ → ℂ} {L U X : ℕ}
    (hL : 0 < L) (hU : 0 < U) (hX : 0 < X) (hUL : U ≤ 2 * L)
    (hA : A ⊆ mrDyadicCofactorRectangle (L, U) X)
    (hb : ∀ m ∈ A, ‖b m‖ ≤ (m : ℝ)⁻¹)
    (S : Finset ℝ) {T : ℝ} (hT : 1 ≤ T)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    (Q : ℝ → ℂ) {V : ℝ} (hsmall : ∀ t ∈ S, ‖Q t‖ ≤ V) :
    (∑ t ∈ S, ‖Q t * logarithmicDirichletPolynomial A b t‖ ^ 2) ≤
      V ^ 2 * mrSparseCofactorSampleBudget S.card U X T := by
  calc
    _ ≤ ∑ t ∈ S, V ^ 2 * ‖logarithmicDirichletPolynomial A b t‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hsmall t ht) 2) (sq_nonneg _)
    _ = V ^ 2 * ∑ t ∈ S, ‖logarithmicDirichletPolynomial A b t‖ ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mrSparse_cofactor_subset_rectangle_le hL hU hX hUL hA hb S hT hST hsep) (sq_nonneg _)

/-- Actual typical cofactor and prime-line polynomials; all rectangle
and coefficient hypotheses are instantiated. -/
theorem mrSparse_typicalPrimeProduct_sample_le
    (blocks : Finset (ℕ × ℕ)) (I J : ℕ × ℕ) (P : Finset ℕ)
    (hL : 0 < J.1) (hU : 0 < J.2) (hUL : J.2 ≤ 2 * J.1)
    {X : ℕ} (hX : 0 < X) {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S : Finset ℝ) {T : ℝ} (hT : 1 ≤ T)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    {V : ℝ} (hsmall : ∀ t ∈ S,
      ‖logarithmicDirichletPolynomial P (mrFinitePrimeLineCoefficient f) t‖ ≤ V) :
    (∑ t ∈ S, ‖logarithmicDirichletPolynomial P (mrFinitePrimeLineCoefficient f) t *
      logarithmicDirichletPolynomial (mrTypicalCofactorRectangle blocks I J X)
        (mrFiniteCofactorLineCoefficient (primesInBlock I) f) t‖ ^ 2) ≤
      V ^ 2 * mrSparseCofactorSampleBudget S.card J.2 X T := by
  apply mrSparse_smallPrime_product_le hL hU hX hUL
    (mrTypicalCofactorRectangle_subset blocks I J X)
    (fun m hm ↦ norm_mrFiniteCofactorLineCoefficient_le_inv hbound
      (mrTypicalCofactorRectangle_pos hm)) S hT hST hsep
    (logarithmicDirichletPolynomial P (mrFinitePrimeLineCoefficient f)) hsmall

/-- The small-additional-prime sampled branch on the actual exceptional
class, with the optimized sample-count bound substituted explicitly. -/
theorem mrArithmetic_noSmall_smallPrime_product_le
    {eta p₁ q₁ : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p₁) (hq : 1 ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {J j : ℕ} (hj : 1 ≤ j) (hjJ : j ≤ J)
    (blocks : Finset (ℕ × ℕ)) (I Jaux : ℕ × ℕ) (P : Finset ℕ)
    (hL : 0 < Jaux.1) (hU : 0 < Jaux.2) (hUL : Jaux.2 ≤ 2 * Jaux.1)
    {X : ℕ} (hX : 0 < X) {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S : Finset ℝ) {T : ℝ} (hT : 1 ≤ T)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    (hNoSmall : ∀ t ∈ S, t ∈ mrNoSmallFrequencyClass (mrArithmeticSmallFrequencySet eta p₁ q₁ f) J)
    {V : ℝ} (hsmall : ∀ t ∈ S,
      ‖logarithmicDirichletPolynomial P (mrFinitePrimeLineCoefficient f) t‖ ≤ V) :
    (∑ t ∈ S, ‖logarithmicDirichletPolynomial P (mrFinitePrimeLineCoefficient f) t *
      logarithmicDirichletPolynomial (mrTypicalCofactorRectangle blocks I Jaux X)
        (mrFiniteCofactorLineCoefficient (primesInBlock I) f) t‖ ^ 2) ≤
      V ^ 2 * mrSparseCofactorSampleBudget
        (∑ r ∈ mrScheduledSubblocks eta p₁ q₁ j,
          mrOptimizedPrimeSampleBudget T (mrScheduledParameter eta p₁ q₁ j r)
            (mrThresholdExponent eta (j : ℝ))) Jaux.2 X T := by
  have hcount := mrArithmetic_noSmall_sample_card_le_optimized heta0 heta1 hp hq hlogq hbudget
    hj hjJ hbound S hT hST hsep hNoSmall
  exact (mrSparse_typicalPrimeProduct_sample_le blocks I Jaux P hL hU hUL hX hbound
    S hT hST hsep hsmall).trans
    (mul_le_mul_of_nonneg_left (mrSparseCofactorSampleBudget_mono hcount Jaux.2 X T) (sq_nonneg _))

end

end Erdos67b
