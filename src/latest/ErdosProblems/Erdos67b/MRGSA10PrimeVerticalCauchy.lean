import ErdosProblems.Erdos67b.MRGSA10PrimeLambdaDiagonal
import ErdosProblems.Erdos67b.MRGSA10VerticalCauchy

/-!
# Vertical Cauchy bound for the prime Lambda pair

This module is the contour-facing composition of the two weighted-Schur
second moments.  It deliberately retains the common finite beta-sieve row
bound, so later parameter choices can be made independently of the
multiplicative coefficient and of the Archimedean threshold.
-/

namespace Erdos67b.MRHalaszBands

noncomputable section

def gsA10PrimeLambdaLeftEnergyBound
    (Cβ : ℝ) (Q S X y : ℕ) (beta T : ℝ) : ℝ :=
  Real.exp 1 *
    (Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
      (gsA10PrimeGaussianRowBound Cβ Q S y X T *
        (((X / y : ℕ) : ℝ) ^ (2 * beta) *
          gsA10PrimeLambdaHarmonicBudget X)))

def gsA10PrimeLambdaRightEnergyBound
    (Cβ : ℝ) (Q S y X : ℕ) (T : ℝ) : ℝ :=
  Real.exp 1 *
    (Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
      (gsA10PrimeGaussianRowBound Cβ Q S y X T *
        gsA10PrimeLambdaHarmonicBudget X))

theorem continuous_gsA10PrimeLambdaPolynomial
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (sigma : ℝ) :
    Continuous (gsA10PrimeLambdaPolynomial hmul y X sigma) := by
  unfold gsA10PrimeLambdaPolynomial logarithmicDirichletPolynomial
  apply continuous_finsetSum
  intro n _hn
  unfold logarithmicPhase
  fun_prop

/-- Prime-part GHS vertical integral after the exact `L∞ × L² × L²`
step.  The two energy factors are numerical and share the same beta-sieve
constant. -/
theorem exists_norm_intervalIntegral_mul_gsA10PrimeLambda_pair_le :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        (y X Q S : ℕ) (beta T M : ℝ) (F : ℝ → ℂ),
        2 ≤ X → 3 ≤ Q → Q ≤ y → 101 ≤ S →
        Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 →
        0 ≤ beta → 0 < T → 0 ≤ M →
        (∀ t, |t| ≤ T → ‖F t‖ ≤ M) →
        ‖∫ t in -T..T,
            F t *
              gsA10PrimeLambdaPolynomial hmul y X
                (Erdos67b.EulerResidue.taoExponent X - beta) t *
              gsA10PrimeLambdaPolynomial hmul y X
                (Erdos67b.EulerResidue.taoExponent X + beta) t‖ ≤
          M *
              (gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y beta T) ^
                ((1 : ℝ) / 2) *
            (gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T) ^
              ((1 : ℝ) / 2) := by
  obtain ⟨Cβ, hCβ, henergy⟩ :=
    exists_two_intervalIntegral_normSq_gsA10PrimeLambda_tao_le_betaSchur
  refine ⟨Cβ, hCβ, ?_⟩
  intro f hmul hbound y X Q S beta T M F hX hQ hQy hS hlog hbeta hT hM hF
  obtain ⟨hleft, hright⟩ :=
    henergy hmul hbound y X Q S beta T hX hQ hQy hS hlog hbeta hT
  apply norm_intervalIntegral_triple_le_Linfty_mul_L2_bounds
    hT.le hM
    (continuous_gsA10PrimeLambdaPolynomial hmul y X _)
    (continuous_gsA10PrimeLambdaPolynomial hmul y X _)
    hF
  · simpa only [Real.rpow_two, Complex.normSq_eq_norm_sq,
      gsA10PrimeLambdaLeftEnergyBound] using hleft
  · simpa only [Real.rpow_two, Complex.normSq_eq_norm_sq,
      gsA10PrimeLambdaRightEnergyBound] using hright

end

end Erdos67b.MRHalaszBands

#print axioms Erdos67b.MRHalaszBands.exists_norm_intervalIntegral_mul_gsA10PrimeLambda_pair_le
