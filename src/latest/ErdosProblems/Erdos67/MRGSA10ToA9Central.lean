import ErdosProblems.Erdos67.MRGSA10Reconstruction
import ErdosProblems.Erdos67.MRGSTwoBlockA9Energy

/-!
# From the whole A.10 reconstruction to the A.9 central input

The A.10 contour argument acts on one convolution of the alternating low
coefficient with the common high coefficient.  The coefficientwise
reconstruction theorem identifies that convolution with the actual
two-block typical coefficient away from zero.  This file records the exact
prefix-mean transfer required by `MRGSTwoBlockA9Energy`.
-/

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The single whole coefficient on which the A.10 contour argument acts. -/
def gsA10TwoBlockReconstructedCoefficient
    (f : ℕ → ℂ) (P₁ P₂ : ℕ → Prop)
    [DecidablePred P₁] [DecidablePred P₂] (y : ℕ) : ℕ → ℂ :=
  fun n ↦
    (gsA10TwoBlockAlternatingLow f P₁ P₂ y *
      gsA9HighArithmetic f y) n

/-- Coefficientwise reconstruction on the positive integers. -/
theorem gsA10TwoBlockReconstructedCoefficient_eq_typical
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {n : ℕ} (hn : 0 < n) :
    gsA10TwoBlockReconstructedCoefficient f P₁ P₂ y n =
      finiteHalaszTypicalCoefficient f P₁ P₂ n := by
  have hrec := congrFun (congrArg DFunLike.coe
    (gsA10TwoBlockAlternatingLow_mul_high_eq_typical
      hmul P₁ P₂ y hQ₂ hQ₃)) n
  simpa [gsA10TwoBlockReconstructedCoefficient,
    toArithmeticFunction, hn.ne'] using hrec

/-- The whole A.10 coefficient and the actual typical coefficient have
identical untwisted positive prefix means.  The possible value at zero is
irrelevant because `positivePrefixSum` removes it exactly. -/
theorem positivePrefixMean_archimedeanUntwist_gsA10TwoBlock_eq_typical
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    (t : ℝ) (N : ℕ) :
    positivePrefixMean
        (archimedeanUntwist
          (gsA10TwoBlockReconstructedCoefficient f P₁ P₂ y) t) N =
      positivePrefixMean
        (archimedeanUntwist
          (finiteHalaszTypicalCoefficient f P₁ P₂) t) N := by
  have hsum (a : ℕ → ℂ) :
      positivePrefixSum a N = ∑ n ∈ Finset.Ioc 0 N, a n := by
    have h := sum_Ioc_eq_positivePrefixSum_sub a (Nat.zero_le N)
    simpa [positivePrefixSum] using h.symm
  unfold positivePrefixMean
  rw [hsum, hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := (Finset.mem_Ioc.mp hn).1
  unfold archimedeanUntwist
  rw [gsA10TwoBlockReconstructedCoefficient_eq_typical
    hmul P₁ P₂ y hQ₂ hQ₃ hnpos]

/-- Applying A.10 after first removing the minimizing Archimedean twist
produces exactly the centered prefix mean required by A.9.  This is the
natural interface for the GS contour argument: there is no second twist on
the reconstructed convolution. -/
theorem positivePrefixMean_gsA10TwoBlock_archimedeanUntwist_eq_typical
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y : ℕ)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    (t : ℝ) (N : ℕ) :
    positivePrefixMean
        (gsA10TwoBlockReconstructedCoefficient
          (archimedeanUntwist f t) P₁ P₂ y) N =
      positivePrefixMean
        (archimedeanUntwist
          (finiteHalaszTypicalCoefficient f P₁ P₂) t) N := by
  have hsum (a : ℕ → ℂ) :
      positivePrefixSum a N = ∑ n ∈ Finset.Ioc 0 N, a n := by
    have h := sum_Ioc_eq_positivePrefixSum_sub a (Nat.zero_le N)
    simpa [positivePrefixSum] using h.symm
  unfold positivePrefixMean
  rw [hsum, hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := (Finset.mem_Ioc.mp hn).1
  rw [gsA10TwoBlockReconstructedCoefficient_eq_typical
    (archimedeanUntwist_isMultiplicative hmul t)
    P₁ P₂ y hQ₂ hQ₃ hnpos]
  exact congrFun
    (finiteHalaszTypicalCoefficient_archimedeanUntwist f P₁ P₂ t) n

end

end Erdos67.MRHalaszBands

namespace Erdos67

noncomputable section

/-- For the actual two selected prime blocks, endpoint containment supplies
the two low-prime hypotheses needed by A.10. -/
theorem twoBlockA9Central_of_gsA10ReconstructedCentral
    {I₁ I₂ : ℕ × ℕ} {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    {y : ℕ} (hI₁y : I₁.2 ≤ y) (hI₂y : I₂.2 ≤ y)
    (t₁ : ℝ) {Y : ℕ} {E : ℝ}
    (hcentral : ∀ N ∈ Finset.Icc Y (2 * Y),
      ‖positivePrefixMean
          (archimedeanUntwist
            (MRHalaszBands.gsA10TwoBlockReconstructedCoefficient f
              (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁) y) t₁) N‖ ≤ E) :
    ∀ N ∈ Finset.Icc Y (2 * Y),
      ‖positivePrefixMean
          (archimedeanUntwist
            (MRHalaszBands.finiteHalaszTypicalCoefficient f
              (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)) t₁) N‖ ≤ E := by
  have hQ₂ : ∀ p,
      (¬ mrTwoBlockOutside I₁ I₂ p ∧ mrTwoBlockFirst I₁ p) → p ≤ y := by
    intro p hp
    exact (mem_primesInBlock.mp hp.2).2.2.trans hI₁y
  have hQ₃ : ∀ p,
      (¬ mrTwoBlockOutside I₁ I₂ p ∧ ¬ mrTwoBlockFirst I₁ p) → p ≤ y := by
    intro p hp
    have hpI₂ : p ∈ primesInBlock I₂ := by
      by_contra hpI₂
      apply hp.1
      exact ⟨hp.2, hpI₂⟩
    exact (mem_primesInBlock.mp hpI₂).2.2.trans hI₂y
  intro N hN
  rw [← MRHalaszBands.positivePrefixMean_archimedeanUntwist_gsA10TwoBlock_eq_typical
    hmul (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁) y hQ₂ hQ₃ t₁ N]
  exact hcentral N hN

/-- Natural A.10-to-A.9 transfer: A.10 is run on the coefficient after the
minimizing Archimedean twist has already been removed. -/
theorem twoBlockA9Central_of_gsA10UntwistedCentral
    {I₁ I₂ : ℕ × ℕ} {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    {y : ℕ} (hI₁y : I₁.2 ≤ y) (hI₂y : I₂.2 ≤ y)
    (t₁ : ℝ) {Y : ℕ} {E : ℝ}
    (hcentral : ∀ N ∈ Finset.Icc Y (2 * Y),
      ‖positivePrefixMean
          (MRHalaszBands.gsA10TwoBlockReconstructedCoefficient
            (archimedeanUntwist f t₁)
            (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁) y) N‖ ≤ E) :
    ∀ N ∈ Finset.Icc Y (2 * Y),
      ‖positivePrefixMean
          (archimedeanUntwist
            (MRHalaszBands.finiteHalaszTypicalCoefficient f
              (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)) t₁) N‖ ≤ E := by
  have hQ₂ : ∀ p,
      (¬ mrTwoBlockOutside I₁ I₂ p ∧ mrTwoBlockFirst I₁ p) → p ≤ y := by
    intro p hp
    exact (mem_primesInBlock.mp hp.2).2.2.trans hI₁y
  have hQ₃ : ∀ p,
      (¬ mrTwoBlockOutside I₁ I₂ p ∧ ¬ mrTwoBlockFirst I₁ p) → p ≤ y := by
    intro p hp
    have hpI₂ : p ∈ primesInBlock I₂ := by
      by_contra hpI₂
      apply hp.1
      exact ⟨hp.2, hpI₂⟩
    exact (mem_primesInBlock.mp hpI₂).2.2.trans hI₂y
  intro N hN
  rw [← MRHalaszBands.positivePrefixMean_gsA10TwoBlock_archimedeanUntwist_eq_typical
    hmul (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁) y hQ₂ hQ₃ t₁ N]
  exact hcentral N hN

/-- Direct A.10-to-two-length endpoint.  Its central analytic input is a
bound for the one reconstructed convolution of the already untwisted
coefficient, not a bound which already mentions the typical dyadic
polynomial or the short-interval conclusion. -/
theorem dyadicTwoLengthShortMeanSquare_le_twoBlockA10Central_add_mixedBands
    {I₁ I₂ : ℕ × ℕ}
    (hdisj : Disjoint (primesInBlock I₁) (primesInBlock I₂))
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    {y Y Z : ℕ} (hI₁y : I₁.2 ≤ y) (hI₂y : I₂.2 ≤ y)
    (hY : 2 ≤ Y) (hYZ : 2 * Y ≤ Z)
    (t₁ : ℝ) {C R M A : ℝ}
    (hlogOne : 1 ≤ Real.log (Y : ℝ))
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (G : ℝ → ℂ) (hG : Continuous G)
    {X H₁ H₂ : ℕ} (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T S Emedium Ecommon Ediscrepancy : ℝ}
    (hT : 0 < T) (hTS : T ≤ S)
    (hA : 0 ≤ A) (hAM : A ≤ M)
    (hEmedium : 0 ≤ Emedium) (hEcommon : 0 ≤ Ecommon)
    (hEdiscrepancy : 0 ≤ Ediscrepancy)
    (hwindow : ∀ t ∈ Set.Icc (-T) T,
      |t - t₁| ≤ (Real.log (Y : ℝ)) ^ (1 / 16 : ℝ))
    (hdist : ∀ N ∈ Finset.Icc Y (2 * Y),
      pretentiousDistSq f (archimedeanTwist t₁) N ≤
        PrimeEstimates.primeReciprocals N / 8)
    (hmass₂ : ∀ N ∈ Finset.Icc Y (2 * Y),
      MRHalaszBands.primeBandReciprocalMass
          (fun p ↦ ¬ mrTwoBlockOutside I₁ I₂ p ∧ mrTwoBlockFirst I₁ p) N ≤
        PrimeEstimates.primeReciprocals N / 2)
    (hmass₃ : ∀ N ∈ Finset.Icc Y (2 * Y),
      MRHalaszBands.primeBandReciprocalMass
          (fun p ↦ ¬ mrTwoBlockOutside I₁ I₂ p ∧ ¬ mrTwoBlockFirst I₁ p) N ≤
        PrimeEstimates.primeReciprocals N / 2)
    (hmass₂₃ : ∀ N ∈ Finset.Icc Y (2 * Y),
      MRHalaszBands.primeBandReciprocalMass
          (fun p ↦
            (¬ mrTwoBlockOutside I₁ I₂ p ∧ mrTwoBlockFirst I₁ p) ∨
            (¬ mrTwoBlockOutside I₁ I₂ p ∧ ¬ mrTwoBlockFirst I₁ p)) N ≤
        PrimeEstimates.primeReciprocals N / 2)
    (hcentralA10 : ∀ N ∈ Finset.Icc Y (2 * Y),
      ‖positivePrefixMean
          (MRHalaszBands.gsA10TwoBlockReconstructedCoefficient
            (archimedeanUntwist f t₁)
            (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁) y) N‖ ≤
        C * Real.exp (-(1 / 2 : ℝ) * M) + R)
    (hmedium :
      (∫ t in -S..-T,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq (dyadicVerticalDirichletPolynomial
              (typicalFactorizationSet {I₁, I₂} Z) f Y t)) +
        ∫ t in T..S,
          lemma14SafeReciprocalSqWeight T t *
            Complex.normSq (dyadicVerticalDirichletPolynomial
              (typicalFactorizationSet {I₁, I₂} Z) f Y t) ≤
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
              (dyadicVerticalDirichletPolynomial
                (typicalFactorizationSet {I₁, I₂} Z) f Y t - G t)) +
        ∫ t in S..U,
          lemma14SafeReciprocalSqWeight S t *
            Complex.normSq
              (dyadicVerticalDirichletPolynomial
                (typicalFactorizationSet {I₁, I₂} Z) f Y t - G t) ≤
        Ediscrepancy) :
    (∑ n ∈ Finset.Ioc X (2 * X), Complex.normSq
        (dyadicRestrictedShortAverage
            (typicalFactorizationSet {I₁, I₂} Z) f Y n H₁ -
          dyadicRestrictedShortAverage
            (typicalFactorizationSet {I₁, I₂} Z) f Y n H₂)) ≤
      2 * ((X : ℝ) *
        Complex.normSq ((((2 * Real.pi : ℝ) : ℂ))⁻¹) *
        (2 * T) *
        (T * ((H₁ : ℝ) + H₂) / ((X : ℝ) + 1)) ^ 2 *
        (64 * (6 * C) ^ 2 * (A + 1) * Real.exp (-(1 / 2 : ℝ) * A) +
          4 * T *
            (6 * R + 3 * MRHalaszBands.gsA8TwoBlockErrorConstant *
              (Real.log (Y : ℝ)) ^ (-1 / 16 : ℝ)) ^ 2)) +
      8 * (lemma14UniversalPerronSegmentSafeWeightedCoefficient
              ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₁ +
            lemma14UniversalPerronSegmentSafeWeightedCoefficient
              ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) H₂) *
        (Emedium + 2 * (Ecommon + Ediscrepancy)) := by
  have hcentral := twoBlockA9Central_of_gsA10UntwistedCentral
    hmul hI₁y hI₂y t₁ hcentralA10
  exact dyadicTwoLengthShortMeanSquare_le_twoBlockA9Central_add_mixedBands
    hdisj hmul hbound hY hYZ t₁ hlogOne hC hR G hG hH₁ hH₂
    hT hTS hA hAM hEmedium hEcommon hEdiscrepancy hwindow
    hdist hmass₂ hmass₃ hmass₂₃ hcentral hmedium hcommon hdiscrepancy

end

end Erdos67
