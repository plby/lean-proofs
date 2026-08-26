/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierSourceNormalization
import ErdosProblems.Erdos4b.GeneralFourierActualTailLimit

/-!
# Physical normalization with the source's finite singular product

The proved full-product normalization is transferred to the literal
finite product. The exceptional-prime tail is controlled uniformly by
the ambient logarithm divided by the truncation cutoff.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

theorem twoFamilySelbergScales_prod (K : ℕ) (LD LE : ℝ) :
    (∏ i : Fin K ⊕ Fin K, (twoFamilySelbergScales LD LE i : ℂ)) =
      (LD : ℂ) ^ K * (LE : ℂ) ^ K := by
  simp only [twoFamilySelbergScales, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem fullAffineNormalizedQuantity_mul_truncation_ratio
    {K w m q Y : ℕ} (LD LE : ℝ) (Z T : ℂ)
    (hfull : fullActualAffineSingularProduct K w m q ≠ 0) :
    (fullAffineFourierNormalization K w m q (twoFamilySelbergScales LD LE) * Z / T) *
      (fullActualAffineSingularProduct K w m q /
        (largeGapSingularSeries (preSievedShifts K w) m q Y : ℂ)) =
      ((LD : ℂ) ^ K * (LE : ℂ) ^ K /
        (largeGapSingularSeries (preSievedShifts K w) m q Y : ℂ)) * Z / T := by
  unfold fullAffineFourierNormalization
  rw [twoFamilySelbergScales_prod]
  calc
    _ = (((LD : ℂ) ^ K * (LE : ℂ) ^ K / fullActualAffineSingularProduct K w m q) *
        (fullActualAffineSingularProduct K w m q /
          (largeGapSingularSeries (preSievedShifts K w) m q Y : ℂ))) * (Z / T) := by ring
    _ = _ := by rw [div_mul_div_cancel₀ hfull]; ring

theorem tendsto_sourceAnalyticPreSievedWeightSum_finite_normalized
    {α J : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (K : ℕ) (hK : 0 < K) (S : Finset J)
    (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFsmooth : ∀ j i, ContDiff ℝ ∞ (F j i))
    (hGcompact : HasCompactSupport G) (hGsmooth : ContDiff ℝ ∞ G)
    (hFsimplex : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hFceiling : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (w m q T Y : α → ℕ) (V LE : α → ℝ)
    (hw : Tendsto w l atTop) (hV : Tendsto V l atTop) (hY : Tendsto Y l atTop)
    (hdata : ∀ᶠ a in l, SourceNormalizationConditions K (w a) (m a) (q a) (T a) (V a) (LE a))
    (hwY : ∀ᶠ a in l, w a ≤ Y a) (hYq : ∀ᶠ a in l, Y a < q a)
    (hVY : Tendsto (fun a ↦ V a / Y a) l (𝓝 0)) :
    Tendsto (fun a ↦
      ((V a : ℂ) ^ K * (LE a : ℂ) ^ K /
        (largeGapSingularSeries (preSievedShifts K (w a)) (m a) (q a) (Y a) : ℂ)) *
        (sourceAnalyticPreSievedWeightSum (preSievedShifts K (w a))
          (sourceAnalyticPrimeCutoff S F G (w a) (V a) (LE a)) S
          (fun j h ↦ F j ((preSievedShiftEquiv K (w a)).symm h)) G
          (V a) (LE a) (w a) (m a) (q a) (T a) : ℂ) / (T a : ℂ)) l
      (𝓝 (selbergTensorSquareMainConstant S (fun j ↦ twoFamilySelbergProfiles (F j) G))) := by
  have hmain := tendsto_sourceAnalyticPreSievedWeightSum_normalized K hK S F G
    hFcompact hFsmooth hGcompact hGsmooth hFsimplex hFceiling hGsupport
    w m q T V LE hw hV hdata
  have hmass := tendsto_log_fullAffineExceptionalInteger_div_zero K w m q Y V hw hV
    (hdata.mono fun a ha ↦ ha.cofactor_pos) (hdata.mono fun a ha ↦ ha.auxiliary_prime)
    (hdata.mono fun a ha ↦ ha.cutoff_small) (hdata.mono fun a ha ↦ ha.log_cofactor_le)
    (hdata.mono fun a ha ↦ ha.log_auxiliary_le) hVY
  have hratio := tendsto_fullActualAffineSingularProduct_div_truncated_one K w m q Y hw hY
    (hdata.mono fun a ha ↦ ha.cofactor_pos) (hdata.mono fun a ha ↦ ha.cofactor_even)
    (hdata.mono fun a ha ↦ ha.auxiliary_prime) hwY hYq hmass
  have hne : ∀ᶠ a in l, fullActualAffineSingularProduct K (w a) (m a) (q a) ≠ 0 := by
    filter_upwards [hratio.eventually (eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0))]
      with a ha
    exact (div_ne_zero_iff.mp ha).1
  have hlim := hmain.mul hratio
  simp only [mul_one] at hlim
  apply hlim.congr'
  filter_upwards [hne] with a ha
  exact fullAffineNormalizedQuantity_mul_truncation_ratio (Y := Y a) (V a) (LE a) _ _ ha

end

end Erdos4b
