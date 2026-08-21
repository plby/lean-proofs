import ErdosProblems.Erdos239.External.Erdos67.MRGSTwoBlockA8Pointwise
import ErdosProblems.Erdos239.External.Erdos67.MRGSPrefixToDyadic
import ErdosProblems.Erdos239.External.Erdos67.MRGSPointwiseEnergy
import ErdosProblems.Erdos239.External.Erdos67.MRGSTwoLengthComposition

/-!
# Lossless two-block A.9 to dyadic energy

This file inserts one central A.9 estimate for the entire two-deleted-block
coefficient into A.8, the prefix-to-dyadic bridge, and the GS reciprocal
energy estimate.  In particular, there is no decomposition into a finite
family of gaps and no Cauchy--Schwarz loss depending on its cardinality.
-/

open MeasureTheory

namespace Erdos67

noncomputable section

/-- A central A.9 estimate for the whole two-block coefficient gives the
reciprocal pointwise estimate for the actual MRT two-block dyadic
polynomial.  The logarithmic part of A.9 and the A.8 error are kept as one
flat remainder; only that remainder can pay for the length of a later
frequency window. -/
theorem norm_twoBlockTypical_dyadicVerticalDirichletPolynomial_le_of_a9Central
    {I₁ I₂ : ℕ × ℕ}
    (hdisj : Disjoint (primesInBlock I₁) (primesInBlock I₂))
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    {Y Z : ℕ} (hY : 2 ≤ Y) (hYZ : 2 * Y ≤ Z)
    (t₁ u : ℝ) {C R M : ℝ}
    (hlogOne : 1 ≤ Real.log (Y : ℝ))
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hu : |u| ≤ (Real.log (Y : ℝ)) ^ (1 / 16 : ℝ))
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
    (hcentral : ∀ N ∈ Finset.Icc Y (2 * Y),
      ‖positivePrefixMean
          (archimedeanUntwist
            (MRHalaszBands.finiteHalaszTypicalCoefficient f
              (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)) t₁) N‖ ≤
        C * Real.exp (-(1 / 2 : ℝ) * M) + R) :
    ‖dyadicVerticalDirichletPolynomial
        (typicalFactorizationSet {I₁, I₂} Z) f Y (t₁ + u)‖ ≤
      6 * C * Real.exp (-(1 / 2 : ℝ) * M) * (1 + |u|)⁻¹ +
        (6 * R + 3 * MRHalaszBands.gsA8TwoBlockErrorConstant *
          (Real.log (Y : ℝ)) ^ (-1 / 16 : ℝ)) := by
  let B : ℝ :=
    2 * C * Real.exp (-(1 / 2 : ℝ) * M) * (1 + |u|)⁻¹ +
      (2 * R + MRHalaszBands.gsA8TwoBlockErrorConstant *
        (Real.log (Y : ℝ)) ^ (-1 / 16 : ℝ))
  have hlogY : 0 < Real.log (Y : ℝ) := zero_lt_one.trans_le hlogOne
  have hinv : 0 ≤ (1 + |u|)⁻¹ := by positivity
  have hinvOne : (1 + |u|)⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ (by linarith [abs_nonneg u])
  have hB : 0 ≤ B := by
    dsimp only [B]
    have hp : 0 ≤ (Real.log (Y : ℝ)) ^ (-1 / 16 : ℝ) :=
      Real.rpow_nonneg hlogY.le _
    have hc := MRHalaszBands.gsA8TwoBlockErrorConstant_nonneg
    positivity
  have hprefix : ∀ N ∈ Finset.Icc Y (2 * Y),
      ‖gsTwistedPositivePrefixSum
          (MRHalaszBands.finiteHalaszTypicalCoefficient f
            (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)) (t₁ + u) N /
          (N : ℂ)‖ ≤ B := by
    intro N hNmem
    have hYN := (Finset.mem_Icc.mp hNmem).1
    have hN : 2 ≤ N := hY.trans hYN
    have hlogMono : Real.log (Y : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < Y by omega))
        (by exact_mod_cast hYN)
    have hlogN : 1 ≤ Real.log (N : ℝ) := hlogOne.trans hlogMono
    have hwindow : |u| ≤ (Real.log (N : ℝ)) ^ (1 / 16 : ℝ) := by
      exact hu.trans (Real.rpow_le_rpow hlogY.le hlogMono (by norm_num))
    have hnegPow :
        (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ) ≤
          (Real.log (Y : ℝ)) ^ (-1 / 16 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hlogY hlogMono (by norm_num)
    have hE : 0 ≤ C * Real.exp (-(1 / 2 : ℝ) * M) + R := by
      positivity
    have hpoint :=
      MRHalaszBands.norm_twoBlock_normalized_prefix_le_reciprocal_add_window
        hmul hbound (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)
        t₁ u hN hlogN hwindow (hdist N hNmem)
        (hmass₂ N hNmem) (hmass₃ N hNmem) (hmass₂₃ N hNmem)
        hE (hcentral N hNmem)
    have herr := MRHalaszBands.gsA8TwoBlockErrorConstant_nonneg
    calc
      ‖gsTwistedPositivePrefixSum
          (MRHalaszBands.finiteHalaszTypicalCoefficient f
            (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)) (t₁ + u) N /
          (N : ℂ)‖ ≤
        2 * (C * Real.exp (-(1 / 2 : ℝ) * M) + R) * (1 + |u|)⁻¹ +
          MRHalaszBands.gsA8TwoBlockErrorConstant *
            (Real.log (N : ℝ)) ^ (-1 / 16 : ℝ) := hpoint
      _ ≤ 2 * (C * Real.exp (-(1 / 2 : ℝ) * M) + R) * (1 + |u|)⁻¹ +
          MRHalaszBands.gsA8TwoBlockErrorConstant *
            (Real.log (Y : ℝ)) ^ (-1 / 16 : ℝ) := by
        gcongr
      _ ≤ B := by
        dsimp only [B]
        have hRinv : R * (1 + |u|)⁻¹ ≤ R := by
          nlinarith
        nlinarith
  have hdyadic :=
    norm_twoBlockTypical_dyadicVerticalDirichletPolynomial_le_of_normalized_gsPrefixes
      hdisj f (show 0 < Y by omega) hYZ (t₁ + u) hB hprefix
  calc
    ‖dyadicVerticalDirichletPolynomial
        (typicalFactorizationSet {I₁, I₂} Z) f Y (t₁ + u)‖ ≤ 3 * B := hdyadic
    _ = 6 * C * Real.exp (-(1 / 2 : ℝ) * M) * (1 + |u|)⁻¹ +
        (6 * R + 3 * MRHalaszBands.gsA8TwoBlockErrorConstant *
          (Real.log (Y : ℝ)) ^ (-1 / 16 : ℝ)) := by
      dsimp only [B]
      ring

/-- The lossless central-energy consequence.  A whole-coefficient A.9
bound of the form `C exp (-M/2) + R` produces one exponentially decaying
energy term and one flat-remainder term; no schedule cardinality occurs. -/
theorem twoBlockTypical_symmetric_intervalIntegral_normSq_le_of_a9Central
    {I₁ I₂ : ℕ × ℕ}
    (hdisj : Disjoint (primesInBlock I₁) (primesInBlock I₂))
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    {Y Z : ℕ} (hY : 2 ≤ Y) (hYZ : 2 * Y ≤ Z)
    (t₁ : ℝ) {T C R M A : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hAM : A ≤ M)
    (hlogOne : 1 ≤ Real.log (Y : ℝ))
    (hC : 0 ≤ C) (hR : 0 ≤ R)
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
    (hcentral : ∀ N ∈ Finset.Icc Y (2 * Y),
      ‖positivePrefixMean
          (archimedeanUntwist
            (MRHalaszBands.finiteHalaszTypicalCoefficient f
              (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)) t₁) N‖ ≤
        C * Real.exp (-(1 / 2 : ℝ) * M) + R) :
    (∫ t in -T..T, Complex.normSq
        (dyadicVerticalDirichletPolynomial
          (typicalFactorizationSet {I₁, I₂} Z) f Y t)) ≤
      64 * (6 * C) ^ 2 * (A + 1) * Real.exp (-(1 / 2 : ℝ) * A) +
        4 * T *
          (6 * R + 3 * MRHalaszBands.gsA8TwoBlockErrorConstant *
            (Real.log (Y : ℝ)) ^ (-1 / 16 : ℝ)) ^ 2 := by
  let D : ℝ := 6 * R + 3 * MRHalaszBands.gsA8TwoBlockErrorConstant *
    (Real.log (Y : ℝ)) ^ (-1 / 16 : ℝ)
  have hD : 0 ≤ D := by
    dsimp only [D]
    have hlogY : 0 < Real.log (Y : ℝ) := zero_lt_one.trans_le hlogOne
    have hp : 0 ≤ (Real.log (Y : ℝ)) ^ (-1 / 16 : ℝ) :=
      Real.rpow_nonneg hlogY.le _
    have hc := MRHalaszBands.gsA8TwoBlockErrorConstant_nonneg
    positivity
  have hpoint : ∀ t ∈ Set.Icc (-T) T,
      ‖dyadicVerticalDirichletPolynomial
          (typicalFactorizationSet {I₁, I₂} Z) f Y t‖ ≤
        (6 * C) * Real.exp (-(1 / 2 : ℝ) * M) * (1 + |t - t₁|)⁻¹ + D := by
    intro t ht
    have hp :=
      norm_twoBlockTypical_dyadicVerticalDirichletPolynomial_le_of_a9Central
        hdisj hmul hbound hY hYZ t₁ (t - t₁) hlogOne hC hR
        (hwindow t ht) hdist hmass₂ hmass₃ hmass₂₃ hcentral
    rw [show t₁ + (t - t₁) = t by ring] at hp
    simpa only [D] using hp
  simpa only [D] using
    symmetric_intervalIntegral_normSq_le_gsPointwise_add
      (F := dyadicVerticalDirichletPolynomial
        (typicalFactorizationSet {I₁, I₂} Z) f Y)
      (continuous_dyadicVerticalDirichletPolynomial
        (typicalFactorizationSet {I₁, I₂} Z) f Y)
      (c := t₁) (T := T) (M := M) (A := A) (K := 6 * C) (D := D)
      hT hA hAM (by positivity) hD hpoint

/-- Direct insertion of one whole-coefficient A.9 estimate into the exact
two-length continuous Perron endpoint.  The three noncentral source-order
energies remain explicit, while the central contribution has no finite
schedule or cardinality loss. -/
theorem dyadicTwoLengthShortMeanSquare_le_twoBlockA9Central_add_mixedBands
    {I₁ I₂ : ℕ × ℕ}
    (hdisj : Disjoint (primesInBlock I₁) (primesInBlock I₂))
    {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    {Y Z : ℕ} (hY : 2 ≤ Y) (hYZ : 2 * Y ≤ Z)
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
    (hcentral : ∀ N ∈ Finset.Icc Y (2 * Y),
      ‖positivePrefixMean
          (archimedeanUntwist
            (MRHalaszBands.finiteHalaszTypicalCoefficient f
              (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)) t₁) N‖ ≤
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
  let D : ℝ := 6 * R + 3 * MRHalaszBands.gsA8TwoBlockErrorConstant *
    (Real.log (Y : ℝ)) ^ (-1 / 16 : ℝ)
  have hD : 0 ≤ D := by
    dsimp only [D]
    have hlogY : 0 < Real.log (Y : ℝ) := zero_lt_one.trans_le hlogOne
    have hp : 0 ≤ (Real.log (Y : ℝ)) ^ (-1 / 16 : ℝ) :=
      Real.rpow_nonneg hlogY.le _
    have hc := MRHalaszBands.gsA8TwoBlockErrorConstant_nonneg
    positivity
  have hpoint : ∀ t ∈ Set.Icc (-T) T,
      ‖dyadicVerticalDirichletPolynomial
          (typicalFactorizationSet {I₁, I₂} Z) f Y t‖ ≤
        (6 * C) * Real.exp (-(1 / 2 : ℝ) * M) * (1 + |t - t₁|)⁻¹ + D := by
    intro t ht
    have hp :=
      norm_twoBlockTypical_dyadicVerticalDirichletPolynomial_le_of_a9Central
        hdisj hmul hbound hY hYZ t₁ (t - t₁) hlogOne hC hR
        (hwindow t ht) hdist hmass₂ hmass₃ hmass₂₃ hcentral
    rw [show t₁ + (t - t₁) = t by ring] at hp
    simpa only [D] using hp
  simpa only [D] using
    dyadicTwoLengthShortMeanSquare_le_gsPointwise_add_mixedBands
      (typicalFactorizationSet {I₁, I₂} Z) f Y G hG hH₁ hH₂
      hT hTS hA hAM (by positivity : 0 ≤ 6 * C) hD
      hEmedium hEcommon hEdiscrepancy hpoint hmedium hcommon hdiscrepancy

end

end Erdos67
