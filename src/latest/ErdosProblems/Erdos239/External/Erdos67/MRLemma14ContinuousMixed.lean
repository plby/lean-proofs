import ErdosProblems.Erdos239.External.Erdos67.MRLemma14ContinuousCentralEnergy

/-!
# Mixed central/far input for the continuous Perron reduction

The source argument estimates the central and medium frequencies on the
original typical coefficient, but replaces that polynomial by its finite
Ramaré factorisation only on the far bands.  This file records the exact
analytic glue.  The arithmetic comparison between the two polynomials is
left explicit as a second safe-weighted tail.
-/

open Finset MeasureTheory Set

namespace Erdos67

noncomputable section

/-- Weighted square energy of `F` on one ordered interval is bounded by the
energies of `G` and of the discrepancy `F-G`. -/
theorem intervalIntegral_safeReciprocalSqWeight_normSq_le_two_add
    (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    {T a b : ℝ} (hT : 0 < T) (hab : a ≤ b) :
    (∫ t in a..b,
        lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) ≤
      2 * ((∫ t in a..b,
          lemma14SafeReciprocalSqWeight T t * Complex.normSq (G t)) +
        ∫ t in a..b,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq (F t - G t)) := by
  let w : ℝ → ℝ := lemma14SafeReciprocalSqWeight T
  have hw : Continuous w := continuous_lemma14SafeReciprocalSqWeight hT
  have hleft : ContinuousOn (fun t ↦ w t * Complex.normSq (F t))
      (Set.uIcc a b) :=
    (hw.mul (Complex.continuous_normSq.comp hF)).continuousOn
  have hright : ContinuousOn (fun t ↦
      2 * (w t * Complex.normSq (G t) +
        w t * Complex.normSq (F t - G t))) (Set.uIcc a b) := by
    exact (continuous_const.mul
      ((hw.mul (Complex.continuous_normSq.comp hG)).add
        (hw.mul (Complex.continuous_normSq.comp (hF.sub hG))))).continuousOn
  have hpoint (t : ℝ) :
      w t * Complex.normSq (F t) ≤
        2 * (w t * Complex.normSq (G t) +
          w t * Complex.normSq (F t - G t)) := by
    have hadd := normSq_add_le_two_mul (G t) (F t - G t)
    have heq : G t + (F t - G t) = F t := by ring
    rw [heq] at hadd
    have hw0 : 0 ≤ w t := by
      dsimp only [w, lemma14SafeReciprocalSqWeight]
      exact sq_nonneg _
    nlinarith
  calc
    (∫ t in a..b, w t * Complex.normSq (F t)) ≤
        ∫ t in a..b,
          2 * (w t * Complex.normSq (G t) +
            w t * Complex.normSq (F t - G t)) := by
      exact intervalIntegral.integral_mono_on hab
        hleft.intervalIntegrable hright.intervalIntegrable
        (fun t ht ↦ hpoint t)
    _ = 2 * ((∫ t in a..b, w t * Complex.normSq (G t)) +
        ∫ t in a..b, w t * Complex.normSq (F t - G t)) := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      exact intervalIntegral.integral_add
        ((hw.mul (Complex.continuous_normSq.comp hG)).intervalIntegrable
          (μ := volume) a b)
        ((hw.mul (Complex.continuous_normSq.comp (hF.sub hG))).intervalIntegrable
          (μ := volume) a b)

/-- Two-sided safe-weighted form of the preceding comparison. -/
theorem safeReciprocalSqWeight_twoSided_le_two_add
    (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    {T U : ℝ} (hT : 0 < T) (hTU : T ≤ U) :
    (∫ t in -U..-T,
        lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) +
      (∫ t in T..U,
        lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) ≤
      2 * (((∫ t in -U..-T,
          lemma14SafeReciprocalSqWeight T t * Complex.normSq (G t)) +
        ∫ t in T..U,
          lemma14SafeReciprocalSqWeight T t * Complex.normSq (G t)) +
        ((∫ t in -U..-T,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq (F t - G t)) +
        ∫ t in T..U,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq (F t - G t))) := by
  have hneg := intervalIntegral_safeReciprocalSqWeight_normSq_le_two_add
    F G hF hG hT (show -U ≤ -T by linarith)
  have hpos := intervalIntegral_safeReciprocalSqWeight_normSq_le_two_add
    F G hF hG hT hTU
  linarith

theorem lemma14SafeReciprocalSqWeight_eq_of_threshold_le_abs
    {T S t : ℝ} (hTS : T ≤ S) (hSt : S ≤ |t|) :
    lemma14SafeReciprocalSqWeight T t =
      lemma14SafeReciprocalSqWeight S t := by
  unfold lemma14SafeReciprocalSqWeight
  rw [max_eq_left (hTS.trans hSt), max_eq_left hSt]

/-- A two-sided nonnegative weighted tail is monotone in its outer
endpoint. -/
theorem safeReciprocalSqWeight_twoSided_mono_outer
    (F : ℝ → ℂ) (hF : Continuous F) {T U V : ℝ}
    (hT : 0 < T) (hTU : T ≤ U) (hUV : U ≤ V) :
    (∫ t in -U..-T,
        lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) +
      (∫ t in T..U,
        lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) ≤
    (∫ t in -V..-T,
        lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) +
      (∫ t in T..V,
        lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) := by
  let e : ℝ → ℝ := fun t ↦
    lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)
  have he : Continuous e :=
    (continuous_lemma14SafeReciprocalSqWeight hT).mul
      (Complex.continuous_normSq.comp hF)
  have hneg : (∫ t in -U..-T, e t) ≤ ∫ t in -V..-T, e t := by
    exact intervalIntegral.integral_mono_interval (by linarith) (by linarith)
      (le_refl _) (Filter.Eventually.of_forall fun t ↦
        mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
      (he.intervalIntegrable _ _)
  have hpos : (∫ t in T..U, e t) ≤ ∫ t in T..V, e t := by
    exact intervalIntegral.integral_mono_interval (le_refl _) hTU hUV
      (Filter.Eventually.of_forall fun t ↦
        mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
      (he.intervalIntegrable _ _)
  exact add_le_add hneg hpos

/-- Source three-band glue.  Frequencies from `T` to `S` are estimated on
`F`; beyond `S`, `F` is replaced by `G` plus the discrepancy.  The far
inputs use their natural safe cutoff `S`; the weights agree pointwise on
those bands. -/
theorem safeReciprocalSqWeight_twoSided_le_medium_add_two_far
    (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    {T S Emedium Ecommon Ediscrepancy : ℝ}
    (hT : 0 < T) (hTS : T ≤ S)
    (hmedium :
      (∫ t in -S..-T,
          lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) +
        ∫ t in T..S,
          lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t) ≤
        Emedium)
    (hcommon : ∀ U : ℝ, S ≤ U →
      (∫ t in -U..-S,
          lemma14SafeReciprocalSqWeight S t * Complex.normSq (G t)) +
        ∫ t in S..U,
          lemma14SafeReciprocalSqWeight S t * Complex.normSq (G t) ≤
        Ecommon)
    (hdiscrepancy : ∀ U : ℝ, S ≤ U →
      (∫ t in -U..-S,
          lemma14SafeReciprocalSqWeight S t * Complex.normSq (F t - G t)) +
        ∫ t in S..U,
          lemma14SafeReciprocalSqWeight S t * Complex.normSq (F t - G t) ≤
        Ediscrepancy) :
    ∀ U : ℝ, T ≤ U →
      (∫ t in -U..-T,
          lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) +
        ∫ t in T..U,
          lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t) ≤
        Emedium + 2 * (Ecommon + Ediscrepancy) := by
  intro U hTU
  by_cases hUS : U ≤ S
  · have hmono := safeReciprocalSqWeight_twoSided_mono_outer
      F hF hT hTU hUS
    have hc0 : 0 ≤ Ecommon := by
      simpa only [intervalIntegral.integral_same, zero_add] using
        hcommon S le_rfl
    have hd0 : 0 ≤ Ediscrepancy := by
      simpa only [intervalIntegral.integral_same, zero_add] using
        hdiscrepancy S le_rfl
    exact hmono.trans (hmedium.trans
      (le_add_of_nonneg_right (mul_nonneg (by norm_num)
        (add_nonneg hc0 hd0))))
  · have hSU : S ≤ U := le_of_not_ge hUS
    let eT : ℝ → ℝ := fun t ↦
      lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)
    have heT : Continuous eT :=
      (continuous_lemma14SafeReciprocalSqWeight hT).mul
        (Complex.continuous_normSq.comp hF)
    have hSpos : 0 < S := hT.trans_le hTS
    have hsplitNeg : (∫ t in -U..-T, eT t) =
        (∫ t in -U..-S, eT t) + ∫ t in -S..-T, eT t := by
      exact (intervalIntegral.integral_add_adjacent_intervals
        (heT.intervalIntegrable (-U) (-S))
        (heT.intervalIntegrable (-S) (-T))).symm
    have hsplitPos : (∫ t in T..U, eT t) =
        (∫ t in T..S, eT t) + ∫ t in S..U, eT t := by
      exact (intervalIntegral.integral_add_adjacent_intervals
        (heT.intervalIntegrable T S) (heT.intervalIntegrable S U)).symm
    have hnegWeight : (∫ t in -U..-S,
        lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) =
      ∫ t in -U..-S,
        lemma14SafeReciprocalSqWeight S t * Complex.normSq (F t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by linarith)] at ht
      have hSt : S ≤ |t| := by
        rw [abs_of_nonpos (by linarith [ht.2])]
        linarith [ht.2]
      change lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t) =
        lemma14SafeReciprocalSqWeight S t * Complex.normSq (F t)
      rw [lemma14SafeReciprocalSqWeight_eq_of_threshold_le_abs hTS hSt]
    have hposWeight : (∫ t in S..U,
        lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) =
      ∫ t in S..U,
        lemma14SafeReciprocalSqWeight S t * Complex.normSq (F t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hSU] at ht
      have hSt : S ≤ |t| := ht.1.trans (le_abs_self t)
      change lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t) =
        lemma14SafeReciprocalSqWeight S t * Complex.normSq (F t)
      rw [lemma14SafeReciprocalSqWeight_eq_of_threshold_le_abs hTS hSt]
    have hfarCompare := safeReciprocalSqWeight_twoSided_le_two_add
      F G hF hG hSpos hSU
    have hc := hcommon U hSU
    have hd := hdiscrepancy U hSU
    have hfar :
        (∫ t in -U..-S,
            lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) +
          ∫ t in S..U,
            lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t) ≤
          2 * (Ecommon + Ediscrepancy) := by
      rw [hnegWeight, hposWeight]
      exact hfarCompare.trans (by linarith)
    dsimp only [eT] at hsplitNeg hsplitPos
    rw [hsplitNeg, hsplitPos]
    linarith

/-- Genuine two-length Lemma-14 endpoint with the source frequency split:
central cancellation on `F`, a medium safe-weighted energy of `F`, and a
far replacement by `G` plus its discrepancy. -/
theorem dyadicTwoLengthShortMeanSquare_le_verticalEnergy_add_mixedBands
    (Sset : Finset ℕ) (f : ℕ → ℂ) (Y : ℕ) (G : ℝ → ℂ)
    (hG : Continuous G)
    {X H₁ H₂ : ℕ} (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T S Emedium Ecommon Ediscrepancy : ℝ}
    (hT : 0 < T) (hTS : T ≤ S)
    (hEmedium : 0 ≤ Emedium) (hEcommon : 0 ≤ Ecommon)
    (hEdiscrepancy : 0 ≤ Ediscrepancy)
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
        (∫ t in -T..T,
          Complex.normSq (dyadicVerticalDirichletPolynomial Sset f Y t))) +
      8 * (lemma14UniversalPerronSegmentSafeWeightedCoefficient
              ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₁ +
            lemma14UniversalPerronSegmentSafeWeightedCoefficient
              ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₂) *
        (Emedium + 2 * (Ecommon + Ediscrepancy)) := by
  let F : ℝ → ℂ := dyadicVerticalDirichletPolynomial Sset f Y
  have hF : Continuous F :=
    continuous_dyadicVerticalDirichletPolynomial Sset f Y
  have htotal : 0 ≤ Emedium + 2 * (Ecommon + Ediscrepancy) := by
    positivity
  have hfar : ∀ U : ℝ, T ≤ U →
      (∫ t in -U..-T,
          lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) +
        ∫ t in T..U,
          lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t) ≤
        Emedium + 2 * (Ecommon + Ediscrepancy) :=
    safeReciprocalSqWeight_twoSided_le_medium_add_two_far
      F G hF hG hT hTS hmedium hcommon (by
        intro U hSU
        simpa only [F] using hdiscrepancy U hSU)
  have hbase :=
    dyadicTwoLengthShortMeanSquare_le_central_add_weightedHigh_continuous
      Sset f Y (X := X) hH₁ hH₂ hT htotal hfar
  have hcentral :=
    integral_normSq_dyadicTwoLengthPerronCentral_le_verticalEnergy
      Sset f Y (X := X) hH₁ hH₂ hT.le
  exact hbase.trans (by
    have hscaled :=
      mul_le_mul_of_nonneg_left hcentral (show (0 : ℝ) ≤ 2 by norm_num)
    linarith)

/-- Source-correct continuous Perron endpoint with separate central,
finite-Ramaré far, and arithmetic-discrepancy inputs. -/
theorem normalized_uncenteredShortIntervalMeanSquare_le_verticalEnergy_add_mixedHigh
    (S : Finset ℕ) (f : ℕ → ℂ) (Y : ℕ) (G : ℝ → ℂ)
    (hG : Continuous G)
    {X H : ℕ} (hH : 0 < H) {T Ecommon Ediscrepancy : ℝ}
    (hT : 0 < T) (hEcommon : 0 ≤ Ecommon)
    (hEdiscrepancy : 0 ≤ Ediscrepancy)
    (hcommon : ∀ U : ℝ, T ≤ U →
      (∫ t in -U..-T,
          lemma14SafeReciprocalSqWeight T t * Complex.normSq (G t)) +
        ∫ t in T..U,
          lemma14SafeReciprocalSqWeight T t * Complex.normSq (G t) ≤
        Ecommon)
    (hdiscrepancy : ∀ U : ℝ, T ≤ U →
      (∫ t in -U..-T,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq
              (dyadicVerticalDirichletPolynomial S f Y t - G t)) +
        ∫ t in T..U,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq
              (dyadicVerticalDirichletPolynomial S f Y t - G t) ≤
        Ediscrepancy) :
    uncenteredShortIntervalMeanSquare
        (dyadicRestrictedCoefficient S f Y) X H / (H : ℝ) ^ 2 ≤
      2 * (X : ℝ) *
        (Complex.normSq (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
          (2 * T) *
            (∫ t in -T..T,
              Complex.normSq (dyadicVerticalDirichletPolynomial S f Y t))) +
      8 * lemma14UniversalPerronSegmentSafeWeightedCoefficient
          ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H *
            (Ecommon + Ediscrepancy) := by
  let F : ℝ → ℂ := dyadicVerticalDirichletPolynomial S f Y
  have hF : Continuous F :=
    continuous_dyadicVerticalDirichletPolynomial S f Y
  have hsum0 : 0 ≤ 2 * (Ecommon + Ediscrepancy) := by positivity
  have hfar : ∀ U : ℝ, T ≤ U →
      (∫ t in -U..-T,
          lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) +
        ∫ t in T..U,
          lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t) ≤
        2 * (Ecommon + Ediscrepancy) := by
    intro U hTU
    have hcompare := safeReciprocalSqWeight_twoSided_le_two_add
      F G hF hG hT hTU
    have hc := hcommon U hTU
    have hd := hdiscrepancy U hTU
    dsimp only [F] at hcompare
    linarith
  have hbase :=
    normalized_uncenteredShortIntervalMeanSquare_le_verticalEnergy_add_weightedHigh
      S f Y (X := X) hH hT hsum0 hfar
  exact hbase.trans_eq (by ring)

end

end Erdos67
