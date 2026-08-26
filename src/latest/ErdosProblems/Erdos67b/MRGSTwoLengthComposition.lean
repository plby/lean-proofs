import ErdosProblems.Erdos67b.MRGSPointwiseEnergy
import ErdosProblems.Erdos67b.MRLemma14ContinuousMixed

/-!
# Two-length continuous Perron composition for the GS pointwise estimate

This module inserts the source-form Granville--Soundararajan pointwise
estimate into the exact two-length continuous Perron endpoint.  The medium,
common, and discrepancy energies remain separate for the later arithmetic
schedule.
-/

open MeasureTheory

namespace Erdos67b

noncomputable section

/-- A GS pointwise estimate on the central band, together with the three
source-order weighted tail inputs, controls the genuine two-length short
average. -/
theorem dyadicTwoLengthShortMeanSquare_le_gsPointwise_add_mixedBands
    (Sset : Finset ℕ) (f : ℕ → ℂ) (Y : ℕ) (G : ℝ → ℂ)
    (hG : Continuous G)
    {X H₁ H₂ : ℕ} (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T S Emedium Ecommon Ediscrepancy c M A K D : ℝ}
    (hT : 0 < T) (hTS : T ≤ S)
    (hA : 0 ≤ A) (hAM : A ≤ M) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hEmedium : 0 ≤ Emedium) (hEcommon : 0 ≤ Ecommon)
    (hEdiscrepancy : 0 ≤ Ediscrepancy)
    (hpoint : ∀ t ∈ Set.Icc (-T) T,
      ‖dyadicVerticalDirichletPolynomial Sset f Y t‖ ≤
        K * Real.exp (-(1 / 2 : ℝ) * M) * (1 + |t - c|)⁻¹ + D)
    (hmedium :
      (∫ t in -S..-T,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq (dyadicVerticalDirichletPolynomial Sset f Y t)) +
        ∫ t in T..S,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq (dyadicVerticalDirichletPolynomial Sset f Y t) ≤
        Emedium)
    (hcommon : ∀ U : ℝ, S ≤ U →
      (∫ t in -U..-S,
          lemma14SafeReciprocalSqWeight S t * Complex.normSq (G t)) +
        ∫ t in S..U,
          lemma14SafeReciprocalSqWeight S t * Complex.normSq (G t) ≤
        Ecommon)
    (hdiscrepancy : ∀ U : ℝ, S ≤ U →
      (∫ t in -U..-S,
          lemma14SafeReciprocalSqWeight S t *
            Complex.normSq
              (dyadicVerticalDirichletPolynomial Sset f Y t - G t)) +
        ∫ t in S..U,
          lemma14SafeReciprocalSqWeight S t *
            Complex.normSq
              (dyadicVerticalDirichletPolynomial Sset f Y t - G t) ≤
        Ediscrepancy) :
    (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq
        (dyadicRestrictedShortAverage Sset f Y n H₁ -
          dyadicRestrictedShortAverage Sset f Y n H₂)) ≤
      2 * ((X : ℝ) *
        Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
        (2 * T) *
        (T * ((H₁ : ℝ) + H₂) / ((X : ℝ) + 1)) ^ 2 *
        (64 * K ^ 2 * (A + 1) * Real.exp (-(1 / 2 : ℝ) * A) +
          4 * T * D ^ 2)) +
      8 * (lemma14UniversalPerronSegmentSafeWeightedCoefficient
              ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₁ +
            lemma14UniversalPerronSegmentSafeWeightedCoefficient
              ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₂) *
        (Emedium + 2 * (Ecommon + Ediscrepancy)) := by
  have henergy := symmetric_intervalIntegral_normSq_le_gsPointwise_add
    (F := dyadicVerticalDirichletPolynomial Sset f Y)
    (continuous_dyadicVerticalDirichletPolynomial Sset f Y)
    (c := c) (T := T) (M := M) (A := A) (K := K) (D := D)
    hT.le hA hAM hK hD hpoint
  have hbase := dyadicTwoLengthShortMeanSquare_le_verticalEnergy_add_mixedBands
    Sset f Y G hG (X := X) hH₁ hH₂ hT hTS
      hEmedium hEcommon hEdiscrepancy
      hmedium hcommon hdiscrepancy
  have hscale : 0 ≤
      (X : ℝ) *
        Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
        (2 * T) *
        (T * ((H₁ : ℝ) + H₂) / ((X : ℝ) + 1)) ^ 2 := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg X) (Complex.normSq_nonneg _))
        (mul_nonneg (by norm_num) hT.le))
      (sq_nonneg _)
  calc
    (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq
        (dyadicRestrictedShortAverage Sset f Y n H₁ -
          dyadicRestrictedShortAverage Sset f Y n H₂)) ≤
        2 * ((X : ℝ) *
          Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
          (2 * T) *
          (T * ((H₁ : ℝ) + H₂) / ((X : ℝ) + 1)) ^ 2 *
          (∫ t in -T..T,
            Complex.normSq
              (dyadicVerticalDirichletPolynomial Sset f Y t))) +
        8 * (lemma14UniversalPerronSegmentSafeWeightedCoefficient
                ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₁ +
              lemma14UniversalPerronSegmentSafeWeightedCoefficient
                ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₂) *
          (Emedium + 2 * (Ecommon + Ediscrepancy)) := hbase
    _ ≤ 2 * ((X : ℝ) *
          Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
          (2 * T) *
          (T * ((H₁ : ℝ) + H₂) / ((X : ℝ) + 1)) ^ 2 *
          (64 * K ^ 2 * (A + 1) * Real.exp (-(1 / 2 : ℝ) * A) +
            4 * T * D ^ 2)) +
        8 * (lemma14UniversalPerronSegmentSafeWeightedCoefficient
                ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₁ +
              lemma14UniversalPerronSegmentSafeWeightedCoefficient
                ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₂) *
          (Emedium + 2 * (Ecommon + Ediscrepancy)) := by
      gcongr

end

end Erdos67b
