/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierSourceFiniteNormalization
import ErdosProblems.Erdos4b.GeneralFourierSourceMainConstant
import ErdosProblems.Erdos4b.GeneralFourierSourceCutoffGrowth

/-!
# The real, finite-singular-series normalization asymptotic

This is the literal real weight sum and the source's separated real
variational constant. Only explicit numerical conditions on the source
parameters remain; the full-to-finite singular comparison and all
analytic limits are proved.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

theorem tendsto_sourceAnalyticPreSievedWeightSum_real_normalized
    {α J : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (K : ℕ) (hK : 0 < K) (S : Finset J)
    (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFsmooth : ∀ j i, ContDiff ℝ ∞ (F j i))
    (hGcompact : HasCompactSupport G) (hGsmooth : ContDiff ℝ ∞ G)
    (hFsimplex : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hFceiling : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (w m q T Y : α → ℕ) (V : α → ℝ)
    (hw : Tendsto w l atTop) (hV : Tendsto V l atTop)
    (hdata : ∀ᶠ a in l,
      SourceNormalizationConditions K (w a) (m a) (q a) (T a) (V a) (Real.log (Y a))) :
    Tendsto (fun a ↦
      V a ^ K * Real.log (Y a) ^ K *
        sourceAnalyticPreSievedWeightSum (preSievedShifts K (w a))
          (sourceAnalyticPrimeCutoff S F G (w a) (V a) (Real.log (Y a))) S
          (fun j h ↦ F j ((preSievedShiftEquiv K (w a)).symm h)) G
          (V a) (Real.log (Y a)) (w a) (m a) (q a) (T a) /
        ((T a : ℝ) * largeGapSingularSeries (preSievedShifts K (w a)) (m a) (q a) (Y a))) l
      (𝓝 (sourceFirstVariationalIntegral S F * sourceCompanionVariationalIntegral K G)) := by
  have hscale := hdata.mono fun a ha ↦ ha.companion_scale_lower
  obtain ⟨hY, hVY⟩ := tendsto_sourceCutoff_atTop_and_ambient_div_zero Y V hV hscale
  have hcompare : ∀ᶠ a in l, w a ≤ Y a ∧ Y a < q a := by
    filter_upwards [hdata, hV.eventually_ge_atTop 1] with a ha hVa
    exact sourceNormalizationConditions_cutoff_comparison hK hVa ha
  have hmain := tendsto_sourceAnalyticPreSievedWeightSum_finite_normalized K hK S F G
    hFcompact hFsmooth hGcompact hGsmooth hFsimplex hFceiling hGsupport
    w m q T Y V (fun a ↦ Real.log (Y a)) hw hV hY hdata
    (hcompare.mono fun a ha ↦ ha.1) (hcompare.mono fun a ha ↦ ha.2) hVY
  rw [selbergTensorSquareMainConstant_twoFamily S F G
    (fun j hj ↦ hFcompact j) (fun j hj ↦ hFsmooth j) hGsmooth, Fintype.card_fin] at hmain
  apply tendsto_ofReal_iff.mp
  convert! hmain using 1
  ext a
  push_cast
  ring

end

end Erdos4b
