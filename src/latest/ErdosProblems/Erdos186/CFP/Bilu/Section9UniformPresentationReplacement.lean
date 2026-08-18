/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section9PresentationReplacement

/-!
# A uniform-constant form of the Section 9 source replacement

The affine-slice constant supplied by the exponential Freiman theorem only
depends on the distortion rank.  The original source-facing theorem hid that
constant inside an existential depending on the current presentation.  This
module retains a fixed choice as an input, making the intermediate product
rank uniformly bounded.
-/

namespace Erdos186.CFP.Bilu.Section9UniformPresentationReplacement

open scoped Pointwise ENNReal RealInnerProductSpace
open Set MeasureTheory
open CFP.BiluFreiman Mahler MinkowskiSecond MinkowskiUpper SubspaceLattice
open DistortingMeasure BadlyApproximable PolarSeparation
open Proposition75Data Proposition74Construction Proposition75Construction
open Section4PresentationLiftSet Section5RpowAffineSlice
open Section94RankThresholdBoundary
open Section6BiasedResidueCell Section7FreimanMap Section7AffineSlice
open Section7BiasedAffineSlice Section7BiasedNumerics
open Section8PolarVolumeProduct Section8PresentationNormalization
open Section8Synthesis Section9BiasedReplacement
open Section9Replacement Section9NormalizedReplacement
  Section9PresentationReplacement
open Section92PresentationDescent

noncomputable section

set_option autoImplicit false

variable {A : Finset ℤ}

/-- Fixed-constant version of the corrected biased affine-slice step. -/
theorem exists_sourceAffineSlice_of_distortingSystem_fixed
    {m r proportionConstant : ℕ} (hr : 0 < r)
    (hslice : RpowAffineSliceStatement (r - 1) proportionConstant 1)
    (K : Finset (IntegralPoint m)) (hK : K.Nonempty)
    (a : Fin r → EuclideanSpace ℝ (Fin m))
    (delta sigma : ℝ)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hsigma : 0 < sigma)
    (ha : ∀ i, WithLp.ofLp (a i) ∈ cubeDistortingSet delta K)
    (hsum : ((sumset K).card : ℝ) ≤ sigma * K.card)
    (hrank : sigma * (2 / biasGamma delta) ^ r ≤
      Real.rpow 2 (((r - 1 : ℕ) : ℝ) + 1 - 1)) :
    ∃ b : Fin r → ℝ, ∃ alpha : Fin r → Fin 2,
      (biasGamma delta / 2) ^ r * K.card <
          (residueCell a b alpha K).card ∧
        K.card ≤ 2 ^ r * (residueCell a b alpha K).card ∧
        Nonempty (SourceAffineSlice a b proportionConstant
          (residueCell a b alpha K)) := by
  obtain ⟨b, alpha, hlarge, hcover, hcell, hdouble⟩ :=
    exists_biased_rpow_residueCell hr K hK a delta sigma 1
      hdelta hdeltaOne hsigma ha hsum hrank
  exact ⟨b, alpha, hlarge, hcover,
    exists_sourceAffineSlice_of_rpow hr hslice a b alpha K hcell hdouble⟩

/-- Proposition 8.3 followed by the fixed-constant biased slice. -/
theorem exists_biased_sourceAffineSlice_of_proposition83_fixed
    {m proportionConstant : ℕ}
    (sigma epsilon : ℝ)
    (hslice : RpowAffineSliceStatement
      (distortionRank sigma - 1) proportionConstant 1)
    (K : Finset (IntegralPoint m)) (hK : K.Nonempty)
    (hsigma : 1 ≤ sigma)
    (hsum : ((sumset K).card : ℝ) ≤ sigma * K.card)
    (Bpolar : Set (Fin m → ℝ))
    (hpolarMeasurable : MeasurableSet Bpolar)
    (hpolarVolume :
      volume Bpolar ≤
        ENNReal.ofReal ((4 : ℝ) ^ m / (epsilon * K.card)))
    (hepsilon : proposition83Threshold m (distortionRank sigma) sigma <
      epsilon) :
    ∃ a : Fin (distortionRank sigma) → EuclideanSpace ℝ (Fin m),
      ∃ b : Fin (distortionRank sigma) → ℝ,
        ∃ alpha : Fin (distortionRank sigma) → Fin 2,
          (∀ i, WithLp.ofLp (a i) ∈
            cubeDistortingSet (distortionDelta sigma) K) ∧
          IsBadlyApproximable Bpolar
            (epsilon ^ proposition83Exponent m (distortionRank sigma))
            (epsilon ^ proposition83Exponent m (distortionRank sigma))
            (fun i ↦ WithLp.ofLp (a i)) ∧
          (biasGamma (distortionDelta sigma) / 2) ^
              distortionRank sigma * K.card <
            (residueCell a b alpha K).card ∧
          K.card ≤ 2 ^ distortionRank sigma *
            (residueCell a b alpha K).card ∧
          Nonempty (SourceAffineSlice a b proportionConstant
            (residueCell a b alpha K)) := by
  let r : ℕ := distortionRank sigma
  have hr : 0 < r := by
    dsimp only [r]
    exact distortionRank_pos hsigma
  have hdim : 0 < 2 * m + r := by omega
  obtain ⟨aSeq, haCube, haBad⟩ := bilu_proposition_8_3
    K Bpolar sigma epsilon hK hsigma hdim hsum hpolarMeasurable
      hpolarVolume hepsilon
  let a : Fin r → EuclideanSpace ℝ (Fin m) :=
    euclideanSystem (r := r) aSeq
  have ha : ∀ i, WithLp.ofLp (a i) ∈
      cubeDistortingSet (distortionDelta sigma) K := by
    intro i
    simpa only [a, ofLp_euclideanSystem, distortionDelta] using
      haCube i i.isLt
  obtain ⟨b, alpha, hlarge, hcover, W⟩ :=
    exists_sourceAffineSlice_of_distortingSystem_fixed hr
      (by simpa only [r] using hslice) K hK a
      (distortionDelta sigma) sigma
      (distortionDelta_pos hsigma) (distortionDelta_lt_one hsigma)
      (zero_lt_one.trans_le hsigma) ha hsum
      (corrected_rank_inequality hsigma)
  refine ⟨a, b, alpha, ha, ?_, hlarge, hcover, W⟩
  simpa only [r, a, BadlyApproximable.IsBadlyApproximableUpTo,
    ofLp_euclideanSystem] using haBad

/-- Fixed-constant version of the corrected Lemma 4.5 seed. -/
theorem exists_lemma45SectionSeed_of_proposition83_biased_fixed
    {m proportionConstant : ℕ}
    (sigma epsilon : ℝ)
    (hslice : RpowAffineSliceStatement
      (distortionRank sigma - 1) proportionConstant 1)
    (K : Finset (IntegralPoint m)) (hK : K.Nonempty)
    (hsigma : 1 ≤ sigma)
    (hsum : ((sumset K).card : ℝ) ≤ sigma * K.card)
    (B : Set (EuclideanSpace ℝ (Fin m)))
    (hbalanced : Balanced ℝ B) (hconvex : Convex ℝ B)
    (hKB : ∀ x ∈ K, integralReal x ∈ B)
    (p : Seminorm ℝ (Fin m → ℝ))
    (hindependent : AdmitsIndependent p m 1)
    (hunit : ∀ x : IntegralPoint m,
      p (integralEmbed x) ≤ 1 → integralReal x ∈ (2 : ℝ) • B)
    (hpolarMeasurable :
      MeasurableSet (euclideanPolar (WithLp.ofLp '' B)))
    (hpolarVolume :
      volume (euclideanPolar (WithLp.ofLp '' B)) ≤
        ENNReal.ofReal ((4 : ℝ) ^ m / (epsilon * K.card)))
    (hepsilon : proposition83Threshold m (distortionRank sigma) sigma <
      epsilon) :
    ∃ a : Fin (distortionRank sigma) → EuclideanSpace ℝ (Fin m),
      ∃ b : Fin (distortionRank sigma) → ℝ,
        ∃ D : GeometricData B a,
          (∀ i, WithLp.ofLp (a i) ∈
            cubeDistortingSet (distortionDelta sigma) K) ∧
          IsBadlyApproximable
            (euclideanPolar (WithLp.ofLp '' B))
            (epsilon ^ proposition83Exponent m (distortionRank sigma))
            (epsilon ^ proposition83Exponent m (distortionRank sigma))
            (fun i ↦ WithLp.ofLp (a i)) ∧
          Nonempty (Lemma45SectionSeed D K
            (2 ^ distortionRank sigma * proportionConstant)) := by
  obtain ⟨a, b, alpha, haCube, haBad, _hbiased, hcover, W⟩ :=
    exists_biased_sourceAffineSlice_of_proposition83_fixed sigma epsilon
      hslice K hK hsigma hsum
      (euclideanPolar (WithLp.ofLp '' B)) hpolarMeasurable
      hpolarVolume hepsilon
  obtain ⟨W⟩ := W
  have hcell : (residueCell a b alpha K).Nonempty := by
    rw [← Finset.card_pos]
    by_contra hzero
    have hzero' : (residueCell a b alpha K).card = 0 :=
      Nat.eq_zero_of_not_pos hzero
    have hcover' := hcover
    rw [hzero', mul_zero] at hcover'
    exact (not_le_of_gt hK.card_pos) hcover'
  obtain ⟨D, x0, hx0, hdiff⟩ :=
    exists_geometricData_of_sourceAffineSlice W hcell B hbalanced hconvex
      hKB p hindependent hunit
  have hlarge : K.card ≤
      (2 ^ distortionRank sigma * proportionConstant) *
        W.sourceSlice.card := by
    calc
      K.card ≤ 2 ^ distortionRank sigma *
          (residueCell a b alpha K).card := hcover
      _ ≤ 2 ^ distortionRank sigma *
          (proportionConstant * W.sourceSlice.card) :=
        Nat.mul_le_mul_left _ W.card_le
      _ = (2 ^ distortionRank sigma * proportionConstant) *
          W.sourceSlice.card := by simp only [mul_assoc]
  let S : Lemma45SectionSeed D K
      (2 ^ distortionRank sigma * proportionConstant) :=
    lemma45SectionSeedOfBiasedAffineSlice hbalanced hconvex W hcell D hKB
      hlarge x0 hx0 hdiff
  exact ⟨a, b, D, haCube, haBad, ⟨S⟩⟩

/-- The source-facing replacement retaining the globally selected affine
slice constant. -/
theorem exists_coveredNormalizedReplacement_of_presentation_fixed
    {proportionConstant : ℕ}
    (sigma epsilon : ℝ)
    (hslice : RpowAffineSliceStatement
      (distortionRank sigma - 1) proportionConstant 1)
    (s : ℕ) (hs : 0 < s) (X : RankedBodyPresentation A)
    (hX : EnlargedInjective s X) (hA : A.Nonempty)
    (hsigma : 1 ≤ sigma)
    (hepsilonPos : 0 < epsilon)
    (hsum : ((twoA A).card : ℝ) ≤ sigma * A.card)
    (hpolarLarge : (((16 : ℝ) * X.1) ^ X.1) * epsilon * A.card ≤
      (4 : ℝ) ^ X.1 *
        volume.real (unitBall (normalizedMahlerSeminorm X)))
    (hepsilon : proposition83Threshold X.1 (distortionRank sigma) sigma <
      epsilon) :
    ∃ a : Fin (distortionRank sigma) → EuclideanSpace ℝ (Fin X.1),
      ∃ D : GeometricData (normalizedEuclideanBody X) a,
        Nonempty (CoveredNormalizedReplacement
          (D := D) (K := normalizedLiftSet X)
          (coverConstant := 2 ^ distortionRank sigma * proportionConstant)
          (proposition75SourceConstant X.1 (distortionRank sigma))
          (ENNReal.ofReal
            (epsilon ^ proposition83Exponent X.1
              (distortionRank sigma)))⁻¹
          (Nat.ceil sigma)) := by
  have hK : (normalizedLiftSet X).Nonempty := by
    rw [← Finset.card_pos, card_normalizedLiftSet]
    exact hA.card_pos
  have hKcard : (0 : ℝ) < (normalizedLiftSet X).card := by
    rw [card_normalizedLiftSet]
    exact_mod_cast hA.card_pos
  have hsumK : (((normalizedLiftSet X + normalizedLiftSet X).card : ℕ) : ℝ) ≤
      sigma * (normalizedLiftSet X).card := by
    rw [card_pairSumset_normalizedLiftSet_eq_twoA s hs X hX,
      card_normalizedLiftSet]
    exact hsum
  have hpolar := polar_volume_normalizedEuclideanBody_le X hepsilonPos
    hKcard (by simpa [card_normalizedLiftSet] using hpolarLarge)
  obtain ⟨a, b, D, haCube, haBad, S⟩ :=
    exists_lemma45SectionSeed_of_proposition83_biased_fixed sigma epsilon
      hslice (normalizedLiftSet X) hK hsigma hsumK
      (normalizedEuclideanBody X)
      (balanced_normalizedEuclideanBody X)
      (convex_normalizedEuclideanBody X)
      (fun z hz ↦ integralReal_mem_normalizedEuclideanBody X hz)
      (normalizedMahlerSeminorm X)
      (by
        refine ⟨standardIntegralPoint,
          linearIndependent_integralEmbed_standard, ?_⟩
        exact normalizedMahlerSeminorm_standard_le_one X)
      (integralReal_mem_two_smul_normalizedEuclideanBody X)
      (by
        rw [ofLp_image_normalizedEuclideanBody]
        exact measurableSet_euclideanPolar _)
      hpolar hepsilon
  obtain ⟨S⟩ := S
  have haUnit : ∀ i, WithLp.ofLp (a i) ∈ unitCubeIoc X.1 := by
    intro i
    exact (haCube i).1
  have h75 : Proposition75Conclusion D
      (proposition75SourceConstant X.1 (distortionRank sigma))
      (ENNReal.ofReal
        (epsilon ^ proposition83Exponent X.1
          (distortionRank sigma)))⁻¹ := by
    apply proposition75Conclusion_of_badlyApproximable X.2.rank_pos
      (balanced_normalizedEuclideanBody X)
      (measurableSet_normalizedEuclideanBody X)
      (convex_normalizedEuclideanBody X) haUnit
      (closedBall_subset_two_smul_normalizedEuclideanBody X)
      (isCompact_normalizedEuclideanBody X) D haBad
    positivity
  have hsigmaCeil : sigma ≤ (Nat.ceil sigma : ℝ) := Nat.le_ceil sigma
  have hdoubleReal :
      (((normalizedLiftSet X + normalizedLiftSet X).card : ℕ) : ℝ) ≤
        (Nat.ceil sigma : ℝ) * (normalizedLiftSet X).card :=
    hsumK.trans (mul_le_mul_of_nonneg_right hsigmaCeil (by positivity))
  have hdouble :
      (normalizedLiftSet X + normalizedLiftSet X).card ≤
        Nat.ceil sigma * (normalizedLiftSet X).card := by
    exact_mod_cast hdoubleReal
  exact ⟨a, D, exists_coveredNormalizedReplacement S h75 hdouble⟩

/-- Uniform ceiling for the sharp product rank after fixing the affine-slice
constant and bounding the current rank. -/
def uniformSharpProductRankBound
    (rankBound proportionConstant : ℕ) (sigma : ℝ) : ℕ :=
  (rankBound + distortionRank sigma - 1) +
    Nat.ceil sigma * (2 ^ distortionRank sigma * proportionConstant)

theorem initialRank_le_uniformSharpProductRankBound
    {proportionConstant : ℕ}
    {s : ℕ} {sigma : ℝ} {constant scale : ENNReal}
    (X : RankedBodyPresentation A)
    {a : Fin (distortionRank sigma) → EuclideanSpace ℝ (Fin X.1)}
    {D : GeometricData (normalizedEuclideanBody X) a}
    (N : CoveredNormalizedReplacement
      (D := D) (K := normalizedLiftSet X)
      (coverConstant := 2 ^ distortionRank sigma * proportionConstant)
      constant scale (Nat.ceil sigma))
    {rankBound : ℕ} (hXrank : X.1 ≤ rankBound) :
    Section91InitialPresentation.InitialPresentation.initialRank N ≤
      uniformSharpProductRankBound rankBound proportionConstant sigma := by
  refine (Section91InitialPresentation.InitialPresentation.initialRank_le N).trans ?_
  unfold uniformSharpProductRankBound
  gcongr

end

end Erdos186.CFP.Bilu.Section9UniformPresentationReplacement

#print axioms
  Erdos186.CFP.Bilu.Section9UniformPresentationReplacement.exists_coveredNormalizedReplacement_of_presentation_fixed
#print axioms
  Erdos186.CFP.Bilu.Section9UniformPresentationReplacement.initialRank_le_uniformSharpProductRankBound
