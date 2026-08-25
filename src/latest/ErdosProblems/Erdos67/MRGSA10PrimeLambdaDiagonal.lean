import ErdosProblems.Erdos67.MRGSA10PrimeLambdaL2
import ErdosProblems.Erdos67.MRGSA10WeightedChebyshev
import ErdosProblems.Erdos67.MRFiniteHalaszSchurGeometric

/-!
# Scalar diagonal bounds for the prime Lambda window

This module scalarizes only the diagonal sum left by the weighted Schur
mean-square theorem.  The two opposite real shifts are kept paired, as in
GHS Lemma 2.6; no pointwise bound for the Lambda polynomial is introduced.
-/

open scoped BigOperators

namespace Erdos67.MRHalaszBands

noncomputable section

/-- On the prime window the exact Schur weight is bounded by the usual
von-Mangoldt Dirichlet weight. -/
theorem gsA10PrimeLambdaSchurWeight_le_vonMangoldt
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X n : ℕ} {sigma : ℝ} (hn : n ∈ gsA10PrimeWindow y X) :
    gsA10PrimeLambdaSchurWeight hmul y sigma n ≤
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (1 - 2 * sigma) := by
  have hnData := mem_gsA10PrimeWindow.mp hn
  have hp : n.Prime := hnData.2.2
  have hnpos : 0 < n := hp.pos
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hp.one_lt)
  have hhigh := norm_gsPrimePart_highGeneralizedMangoldt_le_vonMangoldt
    hmul hbound y n
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp] at hhigh ⊢
  have hrpow0 : 0 ≤ (n : ℝ) ^ (-sigma) := Real.rpow_nonneg (by positivity) _
  have hcoeff :
      ‖gsA10PrimeLambdaCoefficient hmul y sigma n‖ ≤
        Real.log (n : ℝ) * (n : ℝ) ^ (-sigma) := by
    unfold gsA10PrimeLambdaCoefficient
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hrpow0]
    exact mul_le_mul_of_nonneg_right hhigh hrpow0
  have hcoeff0 : 0 ≤ ‖gsA10PrimeLambdaCoefficient hmul y sigma n‖ :=
    norm_nonneg _
  have hupper0 :
      0 ≤ Real.log (n : ℝ) * (n : ℝ) ^ (-sigma) := by positivity
  have hsq := (sq_le_sq₀ hcoeff0 hupper0).2 hcoeff
  have hden : 0 < Real.log (n : ℝ) / (n : ℝ) :=
    div_pos hlogpos (by exact_mod_cast hnpos)
  unfold gsA10PrimeLambdaSchurWeight
  rw [div_le_iff₀ hden]
  calc
    ‖gsA10PrimeLambdaCoefficient hmul y sigma n‖ ^ 2 ≤
        (Real.log (n : ℝ) * (n : ℝ) ^ (-sigma)) ^ 2 := hsq
    _ = (Real.log (n : ℝ) * (n : ℝ) ^ (1 - 2 * sigma)) *
          (Real.log (n : ℝ) / (n : ℝ)) := by
      have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
      rw [Real.rpow_sub hnreal, Real.rpow_one,
        Real.rpow_mul (by positivity)]
      field_simp
      rw [Real.rpow_pow_comm hnreal.le,
        Real.rpow_neg (by positivity : 0 ≤ (n : ℝ) ^ 2)]
      convert inv_mul_cancel₀
        (show ((n : ℝ) ^ 2) ^ sigma ≠ 0 by positivity) using 1
      norm_num [Real.rpow_natCast]

/-- The elementary harmonic budget used for both opposite shifts. -/
def gsA10PrimeLambdaHarmonicBudget (X : ℕ) : ℝ :=
  2 * (Real.log 4 + 4) * (Nat.log 2 X : ℝ)

theorem sum_vonMangoldt_rpow_neg_one_primeWindow_le
    {y X : ℕ} (hX : 2 ≤ X) :
    (∑ n ∈ gsA10PrimeWindow y X,
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-1 : ℝ)) ≤
      gsA10PrimeLambdaHarmonicBudget X := by
  have hsub : gsA10PrimeWindow y X ⊆ Finset.Icc 1 X := by
    intro n hn
    have hnData := mem_gsA10PrimeWindow.mp hn
    exact Finset.mem_Icc.mpr
      ⟨hnData.2.2.one_le, hnData.2.1.le.trans (Nat.div_le_self X y)⟩
  calc
    (∑ n ∈ gsA10PrimeWindow y X,
        ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-1 : ℝ)) ≤
        ∑ n ∈ Finset.Icc 1 X,
          ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-1 : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ ↦ mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (Real.rpow_nonneg (by positivity) _))
    _ ≤ gsA10PrimeLambdaHarmonicBudget X := by
      simpa only [gsA10PrimeLambdaHarmonicBudget, neg_one_mul,
        sub_self, Real.rpow_zero, mul_one] using
        (sum_vonMangoldt_mul_rpow_neg_le_one
          (K := X) (alpha := (1 : ℝ)) hX zero_le_one le_rfl)

/-- On the left shifted line the only growth is the explicit top-of-window
factor.  The extra Tao-line decay is harmlessly discarded here. -/
theorem sum_gsA10PrimeLambdaSchurWeight_tao_sub_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X) {beta : ℝ} (hbeta : 0 ≤ beta) :
    (∑ n ∈ gsA10PrimeWindow y X,
        gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67.EulerResidue.taoExponent X - beta) n) ≤
      ((X / y : ℕ) : ℝ) ^ (2 * beta) *
        gsA10PrimeLambdaHarmonicBudget X := by
  let c := Erdos67.EulerResidue.taoExponent X
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hpoint : ∀ n ∈ gsA10PrimeWindow y X,
      gsA10PrimeLambdaSchurWeight hmul y (c - beta) n ≤
        ((X / y : ℕ) : ℝ) ^ (2 * beta) *
          (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-1 : ℝ)) := by
    intro n hn
    have hnData := mem_gsA10PrimeWindow.mp hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hnData.2.2.pos
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnData.2.2.one_le
    have hnUpper : (n : ℝ) ≤ ((X / y : ℕ) : ℝ) := by
      exact_mod_cast hnData.2.1.le
    have hexp : 1 - 2 * (c - beta) ≤ -1 + 2 * beta := by
      dsimp only [c, Erdos67.EulerResidue.taoExponent]
      have hinv : 0 < (Real.log (X : ℝ))⁻¹ := inv_pos.mpr hlogX
      linarith
    have hpow :
        (n : ℝ) ^ (1 - 2 * (c - beta)) ≤
          ((X / y : ℕ) : ℝ) ^ (2 * beta) * (n : ℝ) ^ (-1 : ℝ) := by
      calc
        (n : ℝ) ^ (1 - 2 * (c - beta)) ≤
            (n : ℝ) ^ (-1 + 2 * beta) :=
          Real.rpow_le_rpow_of_exponent_le hnOne hexp
        _ = (n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ (2 * beta) := by
          rw [Real.rpow_add hnpos]
        _ ≤ (n : ℝ) ^ (-1 : ℝ) *
              ((X / y : ℕ) : ℝ) ^ (2 * beta) := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hnpos.le hnUpper (by positivity)) (by positivity)
        _ = _ := by ring
    calc
      gsA10PrimeLambdaSchurWeight hmul y (c - beta) n ≤
          ArithmeticFunction.vonMangoldt n *
            (n : ℝ) ^ (1 - 2 * (c - beta)) :=
        gsA10PrimeLambdaSchurWeight_le_vonMangoldt hmul hbound hn
      _ ≤ ArithmeticFunction.vonMangoldt n *
            (((X / y : ℕ) : ℝ) ^ (2 * beta) *
              (n : ℝ) ^ (-1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow ArithmeticFunction.vonMangoldt_nonneg
      _ = _ := by ring
  calc
    (∑ n ∈ gsA10PrimeWindow y X,
        gsA10PrimeLambdaSchurWeight hmul y (c - beta) n) ≤
        ∑ n ∈ gsA10PrimeWindow y X,
          ((X / y : ℕ) : ℝ) ^ (2 * beta) *
            (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-1 : ℝ)) :=
      Finset.sum_le_sum hpoint
    _ = ((X / y : ℕ) : ℝ) ^ (2 * beta) *
          (∑ n ∈ gsA10PrimeWindow y X,
            ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-1 : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ ((X / y : ℕ) : ℝ) ^ (2 * beta) *
          gsA10PrimeLambdaHarmonicBudget X := by
      exact mul_le_mul_of_nonneg_left
        (sum_vonMangoldt_rpow_neg_one_primeWindow_le hX) (by positivity)

/-- The right shifted line is no larger than the harmonic budget. -/
theorem sum_gsA10PrimeLambdaSchurWeight_tao_add_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X) {beta : ℝ} (hbeta : 0 ≤ beta) :
    (∑ n ∈ gsA10PrimeWindow y X,
        gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67.EulerResidue.taoExponent X + beta) n) ≤
      gsA10PrimeLambdaHarmonicBudget X := by
  let c := Erdos67.EulerResidue.taoExponent X
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  calc
    (∑ n ∈ gsA10PrimeWindow y X,
        gsA10PrimeLambdaSchurWeight hmul y (c + beta) n) ≤
        ∑ n ∈ gsA10PrimeWindow y X,
          ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnData := mem_gsA10PrimeWindow.mp hn
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnData.2.2.one_le
      have hexp : 1 - 2 * (c + beta) ≤ -1 := by
        dsimp only [c, Erdos67.EulerResidue.taoExponent]
        have hinv : 0 < (Real.log (X : ℝ))⁻¹ := inv_pos.mpr hlogX
        linarith
      calc
        gsA10PrimeLambdaSchurWeight hmul y (c + beta) n ≤
            ArithmeticFunction.vonMangoldt n *
              (n : ℝ) ^ (1 - 2 * (c + beta)) :=
          gsA10PrimeLambdaSchurWeight_le_vonMangoldt hmul hbound hn
        _ ≤ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-1 : ℝ) := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hnOne hexp)
            ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ _ := sum_vonMangoldt_rpow_neg_one_primeWindow_le hX

theorem gsA10PrimeGaussianRowBound_nonneg
    {Cβ : ℝ} {Q S y X : ℕ} {T : ℝ}
    (hCβ : 1 ≤ Cβ) (hX : 2 ≤ X) (hT : 0 < T) :
    0 ≤ gsA10PrimeGaussianRowBound Cβ Q S y X T := by
  have hdensity : 0 ≤ gsA10PrimeRowBetaDensity Cβ Q S := by
    unfold gsA10PrimeRowBetaDensity
    exact mul_nonneg (by positivity) (primeBlockDensity_nonneg _)
  have hremainder : 0 ≤ gsA10PrimeRowBetaRemainder Q S := by
    unfold gsA10PrimeRowBetaRemainder
    positivity
  have hlogX : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hkernel :
      0 ≤ finiteHalaszGaussianPairKernel (T⁻¹ ^ 2) (Real.log 4) :=
    finiteHalaszGaussianPairKernel_nonneg _ _
  unfold gsA10PrimeGaussianRowBound
  have hfirst :
      0 ≤ 16 * Real.log (X : ℝ) *
        (32 / T * gsA10PrimeRowBetaDensity Cβ Q S) := by positivity
  have hsecond :
      0 ≤ (4 * Real.log (X : ℝ) / (y : ℝ)) *
        (6 * gsA10PrimeRowBetaDensity Cβ Q S +
          2 * gsA10PrimeRowBetaRemainder Q S) := by positivity
  have hthird :
      0 ≤ finiteHalaszGaussianPairKernel (T⁻¹ ^ 2) (Real.log 4) *
        (Real.log (X : ℝ) + polynomialHeightPrimeLogMertensBound) :=
    mul_nonneg hkernel
      (add_nonneg hlogX polynomialHeightPrimeLogMertensBound_nonneg)
  positivity

/-- The two opposite A.10 prime-Lambda windows, with a single beta-sieve
constant and an explicit scalar diagonal.  This is the direct input for
the vertical Cauchy step. -/
theorem exists_two_intervalIntegral_normSq_gsA10PrimeLambda_tao_le_betaSchur :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        (y X Q S : ℕ) (beta T : ℝ),
        2 ≤ X → 3 ≤ Q → Q ≤ y → 101 ≤ S →
        Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 →
        0 ≤ beta → 0 < T →
        (∫ t in -T..T,
            Complex.normSq
              (gsA10PrimeLambdaPolynomial hmul y X
                (Erdos67.EulerResidue.taoExponent X - beta) t)) ≤
          Real.exp 1 *
            (Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
              (gsA10PrimeGaussianRowBound Cβ Q S y X T *
                (((X / y : ℕ) : ℝ) ^ (2 * beta) *
                  gsA10PrimeLambdaHarmonicBudget X))) ∧
        (∫ t in -T..T,
            Complex.normSq
              (gsA10PrimeLambdaPolynomial hmul y X
                (Erdos67.EulerResidue.taoExponent X + beta) t)) ≤
          Real.exp 1 *
            (Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
              (gsA10PrimeGaussianRowBound Cβ Q S y X T *
                gsA10PrimeLambdaHarmonicBudget X)) := by
  obtain ⟨Cβ, hCβ, hL2⟩ :=
    exists_intervalIntegral_normSq_gsA10PrimeLambdaPolynomial_le_betaSchur
  refine ⟨Cβ, hCβ, ?_⟩
  intro f hmul hbound y X Q S beta T hX hQ hQy hS hlog hbeta hT
  have hrow0 := gsA10PrimeGaussianRowBound_nonneg
    (Q := Q) (S := S) (y := y) hCβ hX hT
  constructor
  · calc
      (∫ t in -T..T,
          Complex.normSq
            (gsA10PrimeLambdaPolynomial hmul y X
              (Erdos67.EulerResidue.taoExponent X - beta) t)) ≤
          Real.exp 1 *
            (Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
              (gsA10PrimeGaussianRowBound Cβ Q S y X T *
                ∑ n ∈ gsA10PrimeWindow y X,
                  gsA10PrimeLambdaSchurWeight hmul y
                    (Erdos67.EulerResidue.taoExponent X - beta) n)) :=
        hL2 hmul y X Q S _ T hQ hQy hS hlog hT
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (sum_gsA10PrimeLambdaSchurWeight_tao_sub_le
                hmul hbound hX hbeta) hrow0)
            (Real.sqrt_nonneg _)) (Real.exp_pos _).le
  · calc
      (∫ t in -T..T,
          Complex.normSq
            (gsA10PrimeLambdaPolynomial hmul y X
              (Erdos67.EulerResidue.taoExponent X + beta) t)) ≤
          Real.exp 1 *
            (Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
              (gsA10PrimeGaussianRowBound Cβ Q S y X T *
                ∑ n ∈ gsA10PrimeWindow y X,
                  gsA10PrimeLambdaSchurWeight hmul y
                    (Erdos67.EulerResidue.taoExponent X + beta) n)) :=
        hL2 hmul y X Q S _ T hQ hQy hS hlog hT
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (sum_gsA10PrimeLambdaSchurWeight_tao_add_le
                hmul hbound hX hbeta) hrow0)
            (Real.sqrt_nonneg _)) (Real.exp_pos _).le

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.gsA10PrimeLambdaSchurWeight_le_vonMangoldt
#print axioms Erdos67.MRHalaszBands.exists_two_intervalIntegral_normSq_gsA10PrimeLambda_tao_le_betaSchur
