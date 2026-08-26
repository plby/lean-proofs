/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierCommonSourceNormalization
import ErdosProblems.Erdos4b.GeneralFourierSourceAsymptotic

/-!
# Real finite-singular normalization at a common source cutoff

The full singular product is replaced by the literal finite product
using its proved tail ratio, for any enlarged coordinate-capturing
cutoff. No cutoff-dependent analytic estimate is assumed.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

theorem tendsto_sourceAnalyticPreSievedWeightSum_real_normalized_of_common_bound
    {α J : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (K : ℕ) (hK : 0 < K) (S : Finset J)
    (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFsmooth : ∀ j i, ContDiff ℝ ∞ (F j i))
    (hGcompact : HasCompactSupport G) (hGsmooth : ContDiff ℝ ∞ G)
    (hFsimplex : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hFceiling : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (w m q T Y B : α → ℕ) (V : α → ℝ)
    (hw : Tendsto w l atTop) (hV : Tendsto V l atTop)
    (hdata : ∀ᶠ a in l,
      SourceNormalizationConditions K (w a) (m a) (q a) (T a) (V a) (Real.log (Y a)))
    (hB : ∀ᶠ a in l, sourceAnalyticCommonPrimeBound S F G (V a) (Real.log (Y a)) ≤ B a) :
    Tendsto (fun a ↦
      V a ^ K * Real.log (Y a) ^ K *
        sourceAnalyticPreSievedWeightSum (preSievedShifts K (w a))
          (selectedFourierPrimeCutoff (fun p ↦ decide (w a < p)) (boundedFourierPrimes (B a))) S
          (fun j h ↦ F j ((preSievedShiftEquiv K (w a)).symm h)) G
          (V a) (Real.log (Y a)) (w a) (m a) (q a) (T a) /
        ((T a : ℝ) * largeGapSingularSeries (preSievedShifts K (w a)) (m a) (q a) (Y a))) l
      (𝓝 (sourceFirstVariationalIntegral S F * sourceCompanionVariationalIntegral K G)) := by
  have hmain := tendsto_sourceAnalyticPreSievedWeightSum_normalized_of_common_bound
    K hK S F G hFcompact hFsmooth hGcompact hGsmooth hFsimplex hFceiling hGsupport
    w m q T B V (fun a ↦ Real.log (Y a)) hw hV hdata hB
  obtain ⟨hY, hVY⟩ := tendsto_sourceCutoff_atTop_and_ambient_div_zero Y V hV
    (hdata.mono fun a ha ↦ ha.companion_scale_lower)
  have hcompare : ∀ᶠ a in l, w a ≤ Y a ∧ Y a < q a := by
    filter_upwards [hdata, hV.eventually_ge_atTop 1] with a ha hVa
    exact sourceNormalizationConditions_cutoff_comparison hK hVa ha
  have hmass := tendsto_log_fullAffineExceptionalInteger_div_zero K w m q Y V hw hV
    (hdata.mono fun a ha ↦ ha.cofactor_pos) (hdata.mono fun a ha ↦ ha.auxiliary_prime)
    (hdata.mono fun a ha ↦ ha.cutoff_small) (hdata.mono fun a ha ↦ ha.log_cofactor_le)
    (hdata.mono fun a ha ↦ ha.log_auxiliary_le) hVY
  have hratio := tendsto_fullActualAffineSingularProduct_div_truncated_one K w m q Y hw hY
    (hdata.mono fun a ha ↦ ha.cofactor_pos) (hdata.mono fun a ha ↦ ha.cofactor_even)
    (hdata.mono fun a ha ↦ ha.auxiliary_prime)
    (hcompare.mono fun a ha ↦ ha.1) (hcompare.mono fun a ha ↦ ha.2) hmass
  have hne : ∀ᶠ a in l, fullActualAffineSingularProduct K (w a) (m a) (q a) ≠ 0 := by
    filter_upwards [hratio.eventually (eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0))]
      with a ha
    exact (div_ne_zero_iff.mp ha).1
  have hlim := hmain.mul hratio
  simp only [mul_one] at hlim
  rw [selbergTensorSquareMainConstant_twoFamily S F G
    (fun j hj ↦ hFcompact j) (fun j hj ↦ hFsmooth j) hGsmooth, Fintype.card_fin] at hlim
  apply tendsto_ofReal_iff.mp
  apply hlim.congr'
  filter_upwards [hne] with a ha
  rw [fullAffineNormalizedQuantity_mul_truncation_ratio
    (Y := Y a) (V a) (Real.log (Y a)) _ _ ha]
  push_cast
  ring

end

end Erdos4b
