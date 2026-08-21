import ErdosProblems.Erdos239.External.Erdos67.MRGSA10PrimeLambdaSourceCumulative

/-!
# Ordinary vertical prime-pair estimate on the source A.10 lines

The maximum-modulus estimate for `L(g,s) / s^2` absorbs the Perron
denominator.  Consequently the remaining source vertical integral uses the
ordinary (rather than reciprocal-weighted) prime-Lambda second moments.
This file packages their beta-sensitive symmetric square-root product.
-/

open Complex MeasureTheory Set

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Symmetric ordinary vertical energy at the two original source lines.
The common affine-row factor remains outside the beta-sensitive diagonal. -/
theorem rpow_half_mul_intervalIntegral_normSq_gsA10PrimeLambda_tao_le_affineRow_symmetric
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y X : ℕ) (beta R A B : ℝ)
    (hX : 2 ≤ X) (hN : 2 ≤ X / y)
    (hbeta : 0 ≤ beta) (hbetaHalf : beta ≤ 1 / 2)
    (hR : 0 < R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrow : ∀ n ∈ gsA10PrimeWindow y X,
      (∑ m ∈ gsA10PrimeWindow y X,
          (Real.log (m : ℝ) / m) *
            finiteHalaszGaussianPairKernel (R⁻¹ ^ 2)
              (Real.log m - Real.log n)) ≤ A / R + B) :
    (∫ t in -R..R,
        Complex.normSq
          (gsA10PrimeLambdaPolynomial hmul y X
            (Erdos67.EulerResidue.taoExponent X - beta) t)) ^
          ((1 : ℝ) / 2) *
      (∫ t in -R..R,
        Complex.normSq
          (gsA10PrimeLambdaPolynomial hmul y X
            (Erdos67.EulerResidue.taoExponent X + beta) t)) ^
          ((1 : ℝ) / 2) ≤
      (Real.exp 1 * Real.sqrt Real.pi * (A + B * R)) *
        (((X / y : ℕ) : ℝ) ^ beta *
          gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta) := by
  let IL : ℝ := ∫ t in -R..R,
    Complex.normSq
      (gsA10PrimeLambdaPolynomial hmul y X
        (Erdos67.EulerResidue.taoExponent X - beta) t)
  let IR : ℝ := ∫ t in -R..R,
    Complex.normSq
      (gsA10PrimeLambdaPolynomial hmul y X
        (Erdos67.EulerResidue.taoExponent X + beta) t)
  let DL : ℝ := ∑ n ∈ gsA10PrimeWindow y X,
    gsA10PrimeLambdaSchurWeight hmul y
      (Erdos67.EulerResidue.taoExponent X - beta) n
  let DR : ℝ := ∑ n ∈ gsA10PrimeWindow y X,
    gsA10PrimeLambdaSchurWeight hmul y
      (Erdos67.EulerResidue.taoExponent X + beta) n
  let Q : ℝ := Real.exp 1 * Real.sqrt Real.pi * (A + B * R)
  have hIL : 0 ≤ IL := by
    dsimp only [IL]
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun t ht ↦ Complex.normSq_nonneg _)
  have hIR : 0 ≤ IR := by
    dsimp only [IR]
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun t ht ↦ Complex.normSq_nonneg _)
  have hDL : 0 ≤ DL := by
    dsimp only [DL]
    apply Finset.sum_nonneg
    intro n hn
    unfold gsA10PrimeLambdaSchurWeight
    positivity
  have hDR : 0 ≤ DR := by
    dsimp only [DR]
    apply Finset.sum_nonneg
    intro n hn
    unfold gsA10PrimeLambdaSchurWeight
    positivity
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    positivity
  have hILE : IL ≤ Q * DL := by
    have h :=
      intervalIntegral_normSq_gsA10PrimeLambdaPolynomial_le_affineRow
        hmul y X
          (Erdos67.EulerResidue.taoExponent X - beta) R A B hR hrow
    dsimp only [IL, Q, DL]
    convert h using 1 <;> ring
  have hIRE : IR ≤ Q * DR := by
    have h :=
      intervalIntegral_normSq_gsA10PrimeLambdaPolynomial_le_affineRow
        hmul y X
          (Erdos67.EulerResidue.taoExponent X + beta) R A B hR hrow
    dsimp only [IR, Q, DR]
    convert h using 1 <;> ring
  have hILhalf : IL ^ ((1 : ℝ) / 2) ≤
      (Q * DL) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hIL hILE (by norm_num)
  have hIRhalf : IR ^ ((1 : ℝ) / 2) ≤
      (Q * DR) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hIR hIRE (by norm_num)
  have hdiag :=
    rpow_half_sum_gsA10PrimeLambdaSchurWeight_symmetric_le
      hmul hbound hX hN hbeta hbetaHalf
  change IL ^ ((1 : ℝ) / 2) * IR ^ ((1 : ℝ) / 2) ≤ _
  calc
    IL ^ ((1 : ℝ) / 2) * IR ^ ((1 : ℝ) / 2) ≤
        (Q * DL) ^ ((1 : ℝ) / 2) *
          (Q * DR) ^ ((1 : ℝ) / 2) :=
      mul_le_mul hILhalf hIRhalf (Real.rpow_nonneg hIR _)
        (Real.rpow_nonneg (mul_nonneg hQ hDL) _)
    _ = Q * (DL ^ ((1 : ℝ) / 2) * DR ^ ((1 : ℝ) / 2)) := by
      rw [Real.mul_rpow hQ hDL, Real.mul_rpow hQ hDR]
      have hQhalf : Q ^ ((1 : ℝ) / 2) * Q ^ ((1 : ℝ) / 2) = Q := by
        rw [← Real.sqrt_eq_rpow, Real.mul_self_sqrt hQ]
      calc
        (Q ^ ((1 : ℝ) / 2) * DL ^ ((1 : ℝ) / 2)) *
            (Q ^ ((1 : ℝ) / 2) * DR ^ ((1 : ℝ) / 2)) =
          (Q ^ ((1 : ℝ) / 2) * Q ^ ((1 : ℝ) / 2)) *
            (DL ^ ((1 : ℝ) / 2) * DR ^ ((1 : ℝ) / 2)) := by ring
        _ = Q * (DL ^ ((1 : ℝ) / 2) * DR ^ ((1 : ℝ) / 2)) := by
          rw [hQhalf]
    _ ≤ Q * (((X / y : ℕ) : ℝ) ^ beta *
        gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta) :=
      mul_le_mul_of_nonneg_left (by simpa only [DL, DR] using hdiag) hQ
    _ = _ := by rfl

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.rpow_half_mul_intervalIntegral_normSq_gsA10PrimeLambda_tao_le_affineRow_symmetric
