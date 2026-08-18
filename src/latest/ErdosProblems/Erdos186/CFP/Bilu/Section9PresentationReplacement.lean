/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section8PresentationNormalization
import ErdosProblems.Erdos186.CFP.Bilu.Section9BiasedReplacement
import ErdosProblems.Erdos186.CFP.Bilu.Section9NormalizedReplacement
import ErdosProblems.Erdos186.CFP.Bilu.Proposition75Construction

/-!
# Proposition 7.5 and Section 9 for a current body presentation

This is the source-facing join.  Mahler normalization supplies the fixed
Euclidean inball, the selected lift set preserves the source doubling
cardinality, the corrected biased affine slice supplies the Lemma 4.5 seed,
and Proposition 7.5 supplies the normalized section-volume estimate.
-/

namespace Erdos186.CFP.Bilu.Section9PresentationReplacement

open scoped Pointwise ENNReal
open Set MeasureTheory
open CFP.BiluFreiman Mahler MinkowskiSecond MinkowskiUpper SubspaceLattice
open Section4PresentationLiftSet Section8PolarVolumeProduct
open Section8PresentationNormalization Section8Synthesis
open Section7BiasedNumerics
open Section9BiasedReplacement Section9NormalizedReplacement
open Section92PresentationDescent Proposition75Data
open Proposition75Construction DistortingMeasure BadlyApproximable
open PolarSeparation

noncomputable section

set_option autoImplicit false

variable {A : Finset ℤ}

theorem integralReal_mem_two_smul_normalizedEuclideanBody
    (X : RankedBodyPresentation A) (z : IntegralPoint X.1)
    (hz : normalizedMahlerSeminorm X (integralEmbed z) ≤ 1) :
    integralReal z ∈ (2 : ℝ) • normalizedEuclideanBody X := by
  apply (balanced_normalizedEuclideanBody X).subset_smul (by norm_num)
  rw [normalizedEuclideanBody_preimage]
  exact hz

theorem polar_volume_normalizedEuclideanBody_le
    (X : RankedBodyPresentation A) {epsilon card : ℝ}
    (hepsilon : 0 < epsilon) (hcard : 0 < card)
    (hlarge : (((16 : ℝ) * X.1) ^ X.1) * epsilon * card ≤
      (4 : ℝ) ^ X.1 *
        volume.real (unitBall (normalizedMahlerSeminorm X))) :
    volume (euclideanPolar
        (WithLp.ofLp '' normalizedEuclideanBody X)) ≤
      ENNReal.ofReal ((4 : ℝ) ^ X.1 / (epsilon * card)) := by
  rw [ofLp_image_normalizedEuclideanBody]
  exact polar_volume_le_four_pow_div (normalizedMahlerSeminorm X)
    (normalizedMahlerSeminorm_definite X) hepsilon hcard
    (by
      change 0 < (volume (unitBall (normalizedMahlerSeminorm X))).toReal
      rw [volume_normalizedMahlerUnitBall, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (pow_nonneg (by positivity) _)]
      exact mul_pos (pow_pos (by exact_mod_cast X.2.rank_pos) _)
        X.2.bodyVolume_pos
    ) hlarge

/-- The corrected Sections 6--9 replacement generated from an arbitrary
enlarged-injective current presentation.  The only remaining hypotheses are
the explicit source numerical inequalities, which are discharged uniformly
in the Section 4 specialization. -/
theorem exists_coveredNormalizedReplacement_of_presentation
    (s : ℕ) (hs : 0 < s) (X : RankedBodyPresentation A)
    (hX : EnlargedInjective s X) (hA : A.Nonempty)
    (sigma epsilon : ℝ) (hsigma : 1 ≤ sigma) (hepsilonPos : 0 < epsilon)
    (hsum : ((twoA A).card : ℝ) ≤ sigma * A.card)
    (hpolarLarge : (((16 : ℝ) * X.1) ^ X.1) * epsilon * A.card ≤
      (4 : ℝ) ^ X.1 *
        volume.real (unitBall (normalizedMahlerSeminorm X)))
    (hepsilon : proposition83Threshold X.1 (distortionRank sigma) sigma <
      epsilon) :
    ∃ proportionConstant : ℕ,
      ∃ a : Fin (distortionRank sigma) → EuclideanSpace ℝ (Fin X.1),
        ∃ D : GeometricData (normalizedEuclideanBody X) a,
          Nonempty (CoveredNormalizedReplacement
            (D := D) (K := normalizedLiftSet X)
            (coverConstant := 2 ^ distortionRank sigma * proportionConstant)
            (proposition75SourceConstant X.1 (distortionRank sigma))
            (ENNReal.ofReal
              (epsilon ^ proposition83Exponent X.1 (distortionRank sigma)))⁻¹
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
  obtain ⟨proportionConstant, a, b, D, haCube, haBad, S⟩ :=
    exists_lemma45SectionSeed_of_proposition83_biased
      (normalizedLiftSet X) hK sigma epsilon hsigma hsumK
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
        (epsilon ^ proposition83Exponent X.1 (distortionRank sigma)))⁻¹ := by
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
  refine ⟨proportionConstant, a, D, ?_⟩
  exact exists_coveredNormalizedReplacement S h75 hdouble

end

end Erdos186.CFP.Bilu.Section9PresentationReplacement

#print axioms
  Erdos186.CFP.Bilu.Section9PresentationReplacement.exists_coveredNormalizedReplacement_of_presentation
