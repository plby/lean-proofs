/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierSourceResidueMass
import ErdosProblems.Erdos4b.SourceDyadicCommonNormalization
import ErdosProblems.Erdos4b.GeneralFourierJointSourceCutoff

/-!
# Uniform positive normalization of the actual dyadic residue measure

For fixed profiles with positive variational denominator, the actual
finite normalization is positive and has the factor-two upper bound.
All cofactors, auxiliary primes and enlarged joint cutoffs are uniform.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

def dyadicSourceResidueNormalization {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (a D r m q N : ℕ) : ℝ :=
  sourceResidueNormalization S F G
    (selectedFourierPrimeCutoff (fun p ↦ decide (sourcePreSieveCutoff r < p))
      (boundedFourierPrimes N)) (dyadicAmbientScale a r) (dyadicCompanionScale r)
    (D * intervalLength a r) (sourcePreSieveCutoff r) m q

def dyadicSourceResidueMass {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (a D r m q N : ℕ) (b : Fin q) : ℝ :=
  sourceResidueMass S F G
    (selectedFourierPrimeCutoff (fun p ↦ decide (sourcePreSieveCutoff r < p))
      (boundedFourierPrimes N)) (dyadicAmbientScale a r) (dyadicCompanionScale r)
    (D * intervalLength a r) (sourcePreSieveCutoff r) m q b

theorem dyadicSourceResidueMass_nonneg {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (a D r m q N : ℕ) (b : Fin q) :
    0 ≤ dyadicSourceResidueMass S F G a D r m q N b :=
  sourceResidueMass_nonneg S F G _ _ _ _ _ m q b

theorem sum_dyadicSourceResidueMass_eq_one {K q : ℕ} {J : Type*} (hq : 0 < q)
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (a D r m N : ℕ) (hpos : 0 < dyadicSourceResidueNormalization S F G a D r m q N) :
    ∑ b : Fin q, dyadicSourceResidueMass S F G a D r m q N b = 1 :=
  sum_sourceResidueMass_eq_one hq S F G _ _ _ _ _ m hpos

theorem uniform_dyadicSourceResidueNormalization_pos_and_upper
    {J : Type*} {K : ℕ} (hK : 0 < K) (S : Finset J)
    (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFsmooth : ∀ j i, ContDiff ℝ ∞ (F j i))
    (hGcompact : HasCompactSupport G) (hGsmooth : ContDiff ℝ ∞ G)
    (hFsimplex : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hFceiling : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (a D : ℕ)
    (hmain : 0 < sourceFirstVariationalIntegral S F * sourceCompanionVariationalIntegral K G) :
    ∀ᶠ r in atTop, ∀ m q N : ℕ, dyadicSourceRange a D r m q →
      jointSourceCommonPrimeBound S F G (dyadicAmbientScale a r) (dyadicCompanionScale r) ≤ N →
      0 < dyadicSourceResidueNormalization S F G a D r m q N ∧
        dyadicSourceResidueNormalization S F G a D r m q N ≤
          2 * (sourceFirstVariationalIntegral S F * sourceCompanionVariationalIntegral K G) *
            (D * intervalLength a r / m : ℕ) *
              largeGapSingularSeries (preSievedShifts K (sourcePreSieveCutoff r)) m q
                (smoothFrontier r) /
            (dyadicAmbientScale a r ^ K * dyadicCompanionScale r ^ K) := by
  have hclose := uniform_dyadicSourceCommonNormalizedWeight_limit hK S F G hFcompact hFsmooth
    hGcompact hGsmooth hFsimplex hFceiling hGsupport a D (half_pos hmain)
  filter_upwards [hclose, eventually_sourceNormalizationConditions_dyadic K a D,
    tendsto_sourcePreSieveCutoff_atTop.eventually (eventually_ge_atTop (2 * K))]
    with r hnear hconditions hw
  intro m q N hdata hN
  have hc := hconditions m q hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2.1
    hdata.2.2.2.2.1 hdata.2.2.2.2.2
  have hV : 0 < dyadicAmbientScale a r := lt_of_lt_of_le (by norm_num)
    (one_le_dyadicAmbientScale a r)
  have hT : (0 : ℝ) < (D * intervalLength a r / m : ℕ) :=
    (Real.exp_pos _).trans_le hc.interval_large
  have hSS := largeGapSingularSeries_preSievedShifts_pos
    (q := q) (y := smoothFrontier r) hw hdata.2.1
  have hnear' := hnear m q N hdata ((sourceAnalyticCommonPrimeBound_le_joint S F G _ _).trans hN)
  have hresult := normalization_pos_and_upper_of_abs_sub_lt
    (mul_pos (pow_pos hV K) (pow_pos hc.companion_scale_pos K)) (mul_pos hT hSS) hmain hnear'
  simpa only [dyadicSourceCommonNormalizedWeight, dyadicSourceResidueNormalization,
    sourceResidueNormalization, mul_assoc] using hresult

end

end Erdos4b.SmoothParameters
