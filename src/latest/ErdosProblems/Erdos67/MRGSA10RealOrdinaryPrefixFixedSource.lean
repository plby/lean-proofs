import ErdosProblems.Erdos67.MRGSA10FixedSourceProjection
import ErdosProblems.Erdos67.MRGSA10GlobalSecondaryShiu
import ErdosProblems.Erdos67.MRGSA10PrefixUnrestriction

/-!
# Ordinary prefixes from the fixed source A.10 contour

The contour input below is the fixed-`taoExponent` source contour used by
the affine-row/maximum-modulus argument.  Joint near mass, the half endpoint,
the coefficient-mass rectangle, the global secondary, and atypical
unrestriction are all discharged separately.
-/

open scoped ComplexConjugate

namespace Erdos67.MRHalaszBands

noncomputable section

theorem norm_positivePrefixMean_twoBlock_le_sourceContour_add_jointSource
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {I₁ I₂ : ℕ × ℕ}
    (hdisj : Disjoint (primesInBlock I₁) (primesInBlock I₂))
    {y N : ℕ} (hy : 23 ≤ y) (hyN : y ≤ N) (hN : 2 ≤ N)
    (hlogN : 1 ≤ Real.log (N : ℝ))
    (hlogy : 6 ≤ Real.log (y : ℝ))
    (hprimeMass : Erdos67.PrimeEstimates.primeReciprocals N ≤
      Real.log (N : ℝ))
    (hySize : (Real.log (N : ℝ)) ^ 4 ≤ (y : ℝ))
    (hQ₂ : ∀ p, (¬ mrTwoBlockOutside I₁ I₂ p ∧
      mrTwoBlockFirst I₁ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ mrTwoBlockOutside I₁ I₂ p ∧
      ¬ mrTwoBlockFirst I₁ p) → p ≤ y)
    {Econtour rho : ℝ}
    (hcontour :
      ‖gsA10TwoBlockSourcePerronIntegrated f hmul
          (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)
          y N (Real.log (y : ℝ))⁻¹ ((Real.log (N : ℝ)) ^ 2)‖ /
          (N : ℝ) ≤ Econtour)
    (hbad : ((atypicalFactorizationSet {I₁, I₂} N).card : ℝ) ≤
      rho * N) :
    ‖positivePrefixMean f N‖ ≤
      Econtour + gsA10JointMovingProjectionSourceBudget y N +
        gsA10GlobalSecondaryShiuConstant *
          Real.log (y : ℝ) / Real.log (N : ℝ) + rho := by
  let P₁ : ℕ → Prop := mrTwoBlockOutside I₁ I₂
  let P₂ : ℕ → Prop := mrTwoBlockFirst I₁
  have hprojection :
      ‖gsA10TwoBlockTailoredIntegratedPrefix f hmul P₁ P₂ y N
            (Real.log (y : ℝ))⁻¹ -
          gsA10TwoBlockSourcePerronIntegrated f hmul P₁ P₂ y N
            (Real.log (y : ℝ))⁻¹ ((Real.log (N : ℝ)) ^ 2)‖ /
          (N : ℝ) ≤ gsA10JointMovingProjectionSourceBudget y N := by
    exact
      norm_gsA10TwoBlockTailoredIntegratedPrefix_sub_sourcePerronIntegrated_div_le_jointSource
        hmul hcomp hbound P₁ P₂ hy hN hlogN hlogy hprimeMass hySize
          (by simpa only [P₁, P₂] using hQ₂)
          (by simpa only [P₁, P₂] using hQ₃)
  let tailored : ℂ := gsA10TwoBlockTailoredIntegratedPrefix
    f hmul P₁ P₂ y N (Real.log (y : ℝ))⁻¹
  let source : ℂ := gsA10TwoBlockSourcePerronIntegrated
    f hmul P₁ P₂ y N (Real.log (y : ℝ))⁻¹
      ((Real.log (N : ℝ)) ^ 2)
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have htailored : ‖tailored‖ / (N : ℝ) ≤
      Econtour + gsA10JointMovingProjectionSourceBudget y N := by
    have htriangle : ‖tailored‖ ≤ ‖source‖ + ‖tailored - source‖ := by
      calc
        ‖tailored‖ = ‖source + (tailored - source)‖ := by ring_nf
        _ ≤ ‖source‖ + ‖tailored - source‖ := norm_add_le _ _
    calc
      ‖tailored‖ / (N : ℝ) ≤
          ‖source‖ / (N : ℝ) + ‖tailored - source‖ / (N : ℝ) := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right htriangle hN0
      _ ≤ Econtour + gsA10JointMovingProjectionSourceBudget y N :=
        add_le_add (by simpa only [source, P₁, P₂] using hcontour)
          (by simpa only [tailored, source] using hprojection)
  have hrecRaw :=
    norm_positivePrefixSum_gsA10TwoBlockReconstructed_le_tailored_add_log
      hmul hcomp hbound P₁ P₂ hy hyN
        (by simpa only [P₁, P₂] using hQ₂)
        (by simpa only [P₁, P₂] using hQ₃)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrec :
      ‖positivePrefixMean
          (gsA10TwoBlockReconstructedCoefficient f P₁ P₂ y) N‖ ≤
        Econtour + gsA10JointMovingProjectionSourceBudget y N +
          gsA10GlobalSecondaryShiuConstant *
            Real.log (y : ℝ) / Real.log (N : ℝ) := by
    unfold positivePrefixMean
    rw [norm_div, Complex.norm_natCast]
    calc
      ‖positivePrefixSum
          (gsA10TwoBlockReconstructedCoefficient f P₁ P₂ y) N‖ /
            (N : ℝ) ≤
          (‖tailored‖ +
              gsA10GlobalSecondaryShiuConstant *
                ((N : ℝ) / Real.log (N : ℝ)) * Real.log (y : ℝ)) /
            (N : ℝ) := by
        exact div_le_div_of_nonneg_right (by
          simpa only [tailored] using hrecRaw) hNpos.le
      _ = ‖tailored‖ / (N : ℝ) +
          gsA10GlobalSecondaryShiuConstant * Real.log (y : ℝ) /
            Real.log (N : ℝ) := by
        field_simp
      _ ≤ Econtour + gsA10JointMovingProjectionSourceBudget y N +
          gsA10GlobalSecondaryShiuConstant * Real.log (y : ℝ) /
            Real.log (N : ℝ) := by
        gcongr
  exact norm_positivePrefixMean_le_reconstructed_add_atypicalDensity
    hmul hbound hdisj (show 0 < N by omega) hQ₂ hQ₃
    (E := Econtour + gsA10JointMovingProjectionSourceBudget y N +
      gsA10GlobalSecondaryShiuConstant *
        Real.log (y : ℝ) / Real.log (N : ℝ))
    (rho := rho) (by simpa only [P₁, P₂] using hrec) hbad

end


end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.norm_positivePrefixMean_twoBlock_le_sourceContour_add_jointSource
