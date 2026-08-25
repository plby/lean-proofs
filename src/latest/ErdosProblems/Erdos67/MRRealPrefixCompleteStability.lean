import ErdosProblems.Erdos67.MRGSA10RealOrdinaryPrefixLargeZeroFixedSource
import ErdosProblems.Erdos67.MRRealPrefixCompleteStabilityAdapter

/-!
# Unconditional common-prefix stability for real complete multiplicative functions

This file combines the source A.10 estimate in the Archimedean-
nonpretentious branch with its retained-large-zero counterpart.  The signed
prefix adapter handles the remaining near-twist branch and produces one
common centre for every prefix in `[X,3X]`.
-/

open Filter
open scoped ComplexConjugate

namespace Erdos67

noncomputable section

/-- Uniform real prefix stability with a common centre.  The exponent is
deliberately weak; it is the fixed power supplied by the source-scale A.10
schedule. -/
theorem exists_eventually_uniform_real_complete_prefix_stable_one_thousandth :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
        IsMultiplicativeOnPositiveNat f →
        IsCompletelyMultiplicativeOnPositive f →
        (∀ n, 0 < n → conj (f n) = f n) →
        (∀ n, ‖f n‖ ≤ 1) →
        ∃ mu : ℂ, ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
          ‖positivePrefixMean f Z - mu‖ ≤
            C * (Real.log (X : ℝ)) ^ (-(1 / 1000 : ℝ)) := by
  obtain ⟨Ch, hCh, hhalasz⟩ :=
    MRHalaszBands.exists_eventually_norm_positivePrefixMean_real_halasz_smallPower_fixedSource
  obtain ⟨Cf, hCf, hlargeZero⟩ :=
    MRHalaszBands.exists_eventually_norm_positivePrefixMean_real_largeZero_smallPower_fixedSource
  let C : ℝ := max Ch (max Cf realGSSignedPrefixStabilityConstant)
  have hC : 0 < C := hCh.trans_le (by
    dsimp only [C]
    exact le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  have hhalasz' : ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      IsMultiplicativeOnPositiveNat f →
      IsCompletelyMultiplicativeOnPositive f →
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      MRArchimedeanNonpretentious f (realPrefixMovingThreshold X) (3 * X) →
      (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) <
        pretentiousDistSq f (archimedeanTwist 0) (3 * X) →
      ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ‖positivePrefixMean f Z‖ ≤
          Ch * (Real.log (X : ℝ)) ^ (-(1 / 1000 : ℝ)) := by
    filter_upwards [hhalasz] with X hX
    intro f hmul hcomp hreal hbound harch _hzero Z hXZ hZX
    exact hX f hmul hcomp hreal hbound harch Z hXZ hZX
  have hfar' : ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      IsMultiplicativeOnPositiveNat f →
      IsCompletelyMultiplicativeOnPositive f →
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      (∃ t₀ : ℝ,
        (Real.log (X : ℝ)) ^ (4 : ℕ) < |t₀| ∧
        |t₀| ≤ 3 * X ∧
        pretentiousDistSq f (archimedeanTwist t₀) (3 * X) <
          realPrefixMovingThreshold X) →
      (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) <
        pretentiousDistSq f (archimedeanTwist 0) (3 * X) →
      ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ‖positivePrefixMean f Z‖ ≤
          Cf * (Real.log (X : ℝ)) ^ (-(1 / 1000 : ℝ)) := by
    filter_upwards [hlargeZero] with X hX
    intro f hmul hcomp hreal hbound _hfar hzero Z hXZ hZX
    exact hX f hmul hcomp hreal hbound hzero Z hXZ hZX
  simpa only [C] using
    (eventually_uniform_real_complete_prefix_stable_one_thousandth_of_branches
      hhalasz' hfar')

end

end Erdos67

#print axioms
  Erdos67.exists_eventually_uniform_real_complete_prefix_stable_one_thousandth
