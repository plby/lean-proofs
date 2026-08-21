import ErdosProblems.Erdos239.External.Erdos67.MRLemma14ContinuousAdapter
import ErdosProblems.Erdos239.External.Erdos67.MRLemma14TwoLengthSplitAt
import ErdosProblems.Erdos239.External.Erdos67.MRDyadicCover

/-!
# Centered two-length recovery for the real Matomäki--Radziwiłł theorem

The source real-valued theorem does not estimate the longer normalized
average absolutely.  It compares that average with the reference mean on
`(X,2X]`.  This file records the exact finite algebra needed for that
comparison.  The two-length difference is unchanged by centering, so the
compiled Perron/Fatou estimate applies without modification.
-/

open scoped BigOperators
open Finset

namespace Erdos67

noncomputable section

/-- Square mean of normalized short averages centered at the reference mean
on `(X,2X]`. -/
def centeredNormalizedShortAverageMeanSquare
    (a : ℕ → ℂ) (X H : ℕ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    Complex.normSq
      ((∑ j ∈ Finset.Icc 1 H, a (x + j)) / (H : ℂ) -
        longIntervalMean a X)

/-- The centered unnormalized mean square is exactly `H²` times the
normalized centered mean square. -/
theorem shortIntervalMeanSquare_eq_centeredNormalized
    (a : ℕ → ℂ) (X : ℕ) {H : ℕ} (hH : 0 < H) :
    shortIntervalMeanSquare a X H =
      (H : ℝ) ^ 2 * centeredNormalizedShortAverageMeanSquare a X H := by
  classical
  unfold shortIntervalMeanSquare centeredNormalizedShortAverageMeanSquare
    shortIntervalDeviation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hHC : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  have hHR : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  rw [show
      (∑ j ∈ Finset.Icc 1 H, a (x + j)) -
          (H : ℂ) * longIntervalMean a X =
        (H : ℂ) *
          ((∑ j ∈ Finset.Icc 1 H, a (x + j)) / (H : ℂ) -
            longIntervalMean a X) by
      field_simp]
  rw [Complex.normSq_mul, Complex.normSq_natCast]
  ring

/-- Square mean of the longer dyadically restricted normalized average,
centered at the long mean of that same coefficient. -/
def dyadicRestrictedCenteredShortAverageMeanSquareAt
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X H : ℕ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    Complex.normSq
      (dyadicRestrictedShortAverage S f Y x H -
        longIntervalMean (dyadicRestrictedCoefficient S f Y) X)

/-- The two adjacent dyadic restrictions recover the normalized short
average, provided the short length is at most the spatial scale. -/
theorem normalizedShortAverage_eq_two_dyadicRestricted
    (a : ℕ → ℂ) {X H x : ℕ} (hH : 0 < H) (hHX : H ≤ X)
    (hx : x ∈ Finset.Ioc X (2 * X)) :
    (∑ j ∈ Finset.Icc 1 H, a (x + j)) / (H : ℂ) =
      dyadicRestrictedShortAverage (Finset.Ioc X (2 * X)) a X x H +
        dyadicRestrictedShortAverage
          (Finset.Ioc (2 * X) (4 * X)) a (2 * X) x H := by
  rw [sum_Icc_eq_two_dyadicRestricted a hHX hx]
  unfold dyadicRestrictedShortAverage
  rw [sum_Icc_add_eq_sum_Ioc, sum_Icc_add_eq_sum_Ioc, add_div]

/-- The short-interval deviation of a dyadically restricted coefficient is
`H` times its normalized centered short average. -/
theorem shortIntervalDeviation_dyadicRestricted_eq
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X x : ℕ)
    {H : ℕ} (hH : 0 < H) :
    shortIntervalDeviation (dyadicRestrictedCoefficient S f Y) X x H =
      (H : ℂ) *
        (dyadicRestrictedShortAverage S f Y x H -
          longIntervalMean (dyadicRestrictedCoefficient S f Y) X) := by
  unfold shortIntervalDeviation dyadicRestrictedShortAverage
  rw [sum_Icc_add_eq_sum_Ioc]
  have hHC : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  field_simp

/-- Centered analogue of the source Lemma-14 recovery step.  The first term
is precisely the already compiled two-length Perron/Fatou quantity.  The
only new term is the source long-average stability term at `H₂`. -/
theorem shortIntervalMeanSquare_dyadicRestrictedAt_le_twoLength_add_centeredLong
    (S : Finset ℕ) (f : ℕ → ℂ)
    {Y X H₁ H₂ : ℕ} (hH₁ : 0 < H₁) (_hH₂ : 0 < H₂) :
    shortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f Y) X H₁ ≤
      2 * (H₁ : ℝ) ^ 2 *
        (dyadicTwoLengthShortMeanSquareAt S f Y X H₁ H₂ +
          dyadicRestrictedCenteredShortAverageMeanSquareAt S f Y X H₂) := by
  classical
  unfold shortIntervalMeanSquare dyadicTwoLengthShortMeanSquareAt
    dyadicRestrictedCenteredShortAverageMeanSquareAt
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  rw [shortIntervalDeviation_dyadicRestricted_eq S f Y X x hH₁]
  let A : ℂ := dyadicRestrictedShortAverage S f Y x H₁ -
    dyadicRestrictedShortAverage S f Y x H₂
  let B : ℂ := dyadicRestrictedShortAverage S f Y x H₂ -
    longIntervalMean (dyadicRestrictedCoefficient S f Y) X
  have hdecomp :
      dyadicRestrictedShortAverage S f Y x H₁ -
          longIntervalMean (dyadicRestrictedCoefficient S f Y) X = A + B := by
    dsimp [A, B]
    ring
  rw [hdecomp, Complex.normSq_mul, Complex.normSq_natCast]
  have hsum := normSq_sub_le_two_mul_add A (-B)
  simp only [sub_neg_eq_add, Complex.normSq_neg] at hsum
  calc
    (H₁ : ℝ) * H₁ * Complex.normSq (A + B) =
        (H₁ : ℝ) ^ 2 * Complex.normSq (A + B) := by ring
    _ ≤ (H₁ : ℝ) ^ 2 *
        (2 * (Complex.normSq A + Complex.normSq B)) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = 2 * (H₁ : ℝ) ^ 2 * Complex.normSq
            (dyadicRestrictedShortAverage S f Y x H₁ -
              dyadicRestrictedShortAverage S f Y x H₂) +
          2 * (H₁ : ℝ) ^ 2 * Complex.normSq
            (dyadicRestrictedShortAverage S f Y x H₂ -
              longIntervalMean (dyadicRestrictedCoefficient S f Y) X) := by
      dsimp [A, B]
      ring

/-- Source-exact two-dyadic centered recovery.  The dyadic pieces remain
separate only in their two-length differences, where the compiled Perron
argument applies.  Their longer averages are recombined before centering,
leaving one stability term for the original coefficient `a`. -/
theorem shortIntervalMeanSquare_le_twoDyadicTwoLength_add_centeredLong
    (a : ℕ → ℂ) {X H₁ H₂ : ℕ}
    (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    (hH₁X : H₁ ≤ X) (hH₂X : H₂ ≤ X) :
    shortIntervalMeanSquare a X H₁ ≤
      4 * (H₁ : ℝ) ^ 2 *
        (dyadicTwoLengthShortMeanSquareAt
            (Finset.Ioc X (2 * X)) a X X H₁ H₂ +
          dyadicTwoLengthShortMeanSquareAt
            (Finset.Ioc (2 * X) (4 * X)) a (2 * X) X H₁ H₂) +
      2 * (H₁ : ℝ) ^ 2 *
        centeredNormalizedShortAverageMeanSquare a X H₂ := by
  classical
  unfold shortIntervalMeanSquare dyadicTwoLengthShortMeanSquareAt
    centeredNormalizedShortAverageMeanSquare
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  let A : ℂ :=
    dyadicRestrictedShortAverage (Finset.Ioc X (2 * X)) a X x H₁ -
      dyadicRestrictedShortAverage (Finset.Ioc X (2 * X)) a X x H₂
  let B : ℂ :=
    dyadicRestrictedShortAverage
        (Finset.Ioc (2 * X) (4 * X)) a (2 * X) x H₁ -
      dyadicRestrictedShortAverage
        (Finset.Ioc (2 * X) (4 * X)) a (2 * X) x H₂
  let C : ℂ :=
    (∑ j ∈ Finset.Icc 1 H₂, a (x + j)) / (H₂ : ℂ) -
      longIntervalMean a X
  have havg₁ := normalizedShortAverage_eq_two_dyadicRestricted
    a hH₁ hH₁X hx
  have havg₂ := normalizedShortAverage_eq_two_dyadicRestricted
    a hH₂ hH₂X hx
  have hdev : shortIntervalDeviation a X x H₁ =
      (H₁ : ℂ) * (A + B + C) := by
    unfold shortIntervalDeviation
    have hH₁C : (H₁ : ℂ) ≠ 0 := by exact_mod_cast hH₁.ne'
    rw [show
        (∑ j ∈ Finset.Icc 1 H₁, a (x + j)) -
            (H₁ : ℂ) * longIntervalMean a X =
          (H₁ : ℂ) *
            ((∑ j ∈ Finset.Icc 1 H₁, a (x + j)) / (H₁ : ℂ) -
              longIntervalMean a X) by field_simp]
    congr 1
    rw [havg₁]
    dsimp only [A, B, C]
    rw [havg₂]
    ring
  rw [hdev, Complex.normSq_mul, Complex.normSq_natCast]
  have hab := normSq_sub_le_two_mul_add A (-B)
  simp only [sub_neg_eq_add, Complex.normSq_neg] at hab
  have habc := normSq_sub_le_two_mul_add (A + B) (-C)
  simp only [sub_neg_eq_add, Complex.normSq_neg] at habc
  have hthree : Complex.normSq (A + B + C) ≤
      4 * Complex.normSq A + 4 * Complex.normSq B +
        2 * Complex.normSq C := by linarith
  calc
    (H₁ : ℝ) * H₁ * Complex.normSq (A + B + C) =
        (H₁ : ℝ) ^ 2 * Complex.normSq (A + B + C) := by ring
    _ ≤ (H₁ : ℝ) ^ 2 *
        (4 * Complex.normSq A + 4 * Complex.normSq B +
          2 * Complex.normSq C) :=
      mul_le_mul_of_nonneg_left hthree (sq_nonneg _)
    _ = 4 * (H₁ : ℝ) ^ 2 * Complex.normSq
              (dyadicRestrictedShortAverage (Finset.Ioc X (2 * X))
                  a X x H₁ -
                dyadicRestrictedShortAverage (Finset.Ioc X (2 * X))
                  a X x H₂) +
        4 * (H₁ : ℝ) ^ 2 * Complex.normSq
              (dyadicRestrictedShortAverage
                  (Finset.Ioc (2 * X) (4 * X)) a (2 * X) x H₁ -
                dyadicRestrictedShortAverage
                  (Finset.Ioc (2 * X) (4 * X)) a (2 * X) x H₂) +
        2 * (H₁ : ℝ) ^ 2 * Complex.normSq
          ((∑ j ∈ Finset.Icc 1 H₂, a (x + j)) / (H₂ : ℂ) -
            longIntervalMean a X) := by
      dsimp only [A, B, C]
      ring

/-- Source-form centered Lemma 14 with the central band and the reciprocal-square
far tail displayed separately.  In particular, no estimate of an uncentered
single-length Perron integral is needed in the real branch. -/
theorem shortIntervalMeanSquare_dyadicRestrictedAt_le_centeredLemma14
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hf : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {Y X H₁ H₂ : ℕ} (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T Efar : ℝ} (hT : 0 < T) (hEfar : 0 ≤ Efar)
    (hfar : ∀ U : ℝ, T ≤ U →
      (∫ t in -U..-T,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t)) +
        ∫ t in T..U,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t) ≤ Efar) :
    shortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f Y) X H₁ ≤
      2 * (H₁ : ℝ) ^ 2 *
        (2 * ((X : ℝ) *
          (‖(((2 * Real.pi : ℝ) : ℂ))⁻¹‖ *
            (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / ((X : ℝ) + 1))) ^ 2) +
          8 * (lemma14UniversalPerronSegmentSafeWeightedCoefficient
                ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₁ +
              lemma14UniversalPerronSegmentSafeWeightedCoefficient
                ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₂) * Efar +
          dyadicRestrictedCenteredShortAverageMeanSquareAt S f Y X H₂) := by
  have htwo :=
    dyadicTwoLengthShortMeanSquare_le_central_add_weightedHigh_continuous
      S f Y (X := X) hH₁ hH₂ hT hEfar hfar
  have hcentral := integral_normSq_dyadicTwoLengthPerronCentral_le
    S hf Y (X := X) hH₁ hH₂ hT.le
  have htwo' :
      dyadicTwoLengthShortMeanSquareAt S f Y X H₁ H₂ ≤
        2 * ((X : ℝ) *
          (‖(((2 * Real.pi : ℝ) : ℂ))⁻¹‖ *
            (2 * T ^ 2 * ((H₁ : ℝ) + H₂) / ((X : ℝ) + 1))) ^ 2) +
          8 * (lemma14UniversalPerronSegmentSafeWeightedCoefficient
                ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₁ +
              lemma14UniversalPerronSegmentSafeWeightedCoefficient
                ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₂) * Efar := by
    unfold dyadicTwoLengthShortMeanSquareAt
    calc
      (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq
          (dyadicRestrictedShortAverage S f Y n H₁ -
            dyadicRestrictedShortAverage S f Y n H₂)) ≤
          2 * (∫ x in ((X : ℝ) + 1)..(((2 * X : ℕ) : ℝ) + 1),
            Complex.normSq
              (perronKernelSegmentOn
                  (dyadicVerticalDirichletPolynomial S f Y) x H₁ (-T) T -
                perronKernelSegmentOn
                  (dyadicVerticalDirichletPolynomial S f Y) x H₂ (-T) T)) +
          8 * (lemma14UniversalPerronSegmentSafeWeightedCoefficient
                ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₁ +
              lemma14UniversalPerronSegmentSafeWeightedCoefficient
                ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₂) * Efar := htwo
      _ ≤ _ := by gcongr
  have hbase :=
    shortIntervalMeanSquare_dyadicRestrictedAt_le_twoLength_add_centeredLong
      S f (Y := Y) (X := X) hH₁ hH₂
  calc
    shortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f Y) X H₁ ≤
      2 * (H₁ : ℝ) ^ 2 *
        (dyadicTwoLengthShortMeanSquareAt S f Y X H₁ H₂ +
          dyadicRestrictedCenteredShortAverageMeanSquareAt S f Y X H₂) := hbase
    _ ≤ _ := by gcongr

end

end Erdos67
