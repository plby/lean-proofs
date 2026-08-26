/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedPrimeErrorTransfer
import ErdosProblems.Erdos4b.GeneralFourierSourceCutoffGrowth

/-!
# The pinned source prime-weight asymptotic without auxiliary collision factors

The graph kernel limit is transferred to the literal squared divisor
weight summed over the auxiliary primes. The normalization uses the
actual prime count and the literal finite pinned singular series.
Auxiliary collision variables are not part of this theorem.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

theorem tendsto_sourcePinnedPrimeNormalizedWeightSum
    {α I : Type*} {l : Filter α} [l.IsCountablyGenerated] {K : ℕ}
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFsmooth : ∀ j i, ContDiff ℝ ∞ (F j i))
    (hGcompact : HasCompactSupport G) (hGsmooth : ContDiff ℝ ∞ G)
    (hFsimplex : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hFceiling : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) (h : Fin K)
    (J : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (w m p₀ Y X A B N : α → ℕ) (hw : Tendsto w l atTop) (hX : Tendsto X l atTop)
    (hdata : ∀ᶠ a in l, SourcePinnedNormalizationConditions K
      (w a) (m a) (p₀ a) (Y a) (X a) (A a) (B a) J δ)
    (hN : ∀ᶠ a in l,
      jointSourceCommonPrimeBound S F G (Real.log (X a)) (Real.log (Y a)) ≤ N a) :
    Tendsto (fun a ↦ sourcePinnedPrimeNormalizedWeightSum S F G h
      (w a) (m a) (p₀ a) (Y a) (N a) (A a) (B a) (Real.log (X a)) (Real.log (Y a))) l
      (𝓝 ((sourcePinnedFirstVariationalIntegral S F h *
        sourcePinnedCompanionVariationalIntegral K G : ℝ) : ℂ)) := by
  have hV : Tendsto (fun a ↦ Real.log (X a)) l atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hX)
  have hY := (tendsto_sourceCutoff_atTop_and_ambient_div_zero Y (fun a ↦ Real.log (X a)) hV
    (hdata.mono fun a ha ↦ ha.companion_scale_lower)).1
  have hmain := tendsto_pinnedSourceTotientGraphKernel_normalized S F G h
    (fun j hj ↦ hFcompact j) (fun j hj ↦ hFsmooth j) hGcompact hGsmooth
    w m p₀ Y N (fun a ↦ Real.log (X a)) hw hV hY
    (hdata.mono fun a ha ↦ ha.cofactor_pos) (hdata.mono fun a ha ↦ ha.pinned_prime)
    (hdata.mono fun a ha ↦ ha.cutoff_le_companion)
    (hdata.mono fun a ha ↦ ha.companion_lt_pinned)
    (hdata.mono fun a ha ↦ ha.residual_coprime) (hdata.mono fun a ha ↦ ha.cutoff_small)
    (hdata.mono fun a ha ↦ ha.log_cofactor_le) (hdata.mono fun a ha ↦ ha.log_pinned_le)
    (hdata.mono fun a ha ↦ ha.companion_scale_lower)
    (hdata.mono fun a ha ↦ ha.companion_scale_le) hN
  have herr := tendsto_sourcePinnedPrimeWeight_sub_graph_zero S F G
    hFcompact (fun j i ↦ (hFsmooth j i).continuous) hGcompact hGsmooth.continuous
    hFsimplex hFceiling hGsupport h J hδ w m p₀ Y X A B N hw hX hdata
  simp only [Complex.ofReal_div] at herr
  have hlim := herr.add hmain
  simp only [zero_add] at hlim
  apply hlim.congr'
  exact Eventually.of_forall fun a ↦ sub_add_cancel _ _

end

end Erdos4b
