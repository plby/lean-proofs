/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierSourceNormalizationIdentity

/-!
# The physical source normalization asymptotic

The exact original weight sum is normalized by its literal affine
singular product. Fixed compact smooth source profiles, their support
conditions, and explicit numerical parameter inequalities suffice for
the limit. No analytic sieve asymptotic is assumed in the data below.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

structure SourceNormalizationConditions (K w m q T : ℕ) (V LE : ℝ) : Prop where
  cofactor_pos : 0 < m
  cofactor_even : Even m
  auxiliary_prime : q.Prime
  cutoff_lt_auxiliary : w < q
  log_cofactor_le : Real.log m ≤ V
  log_auxiliary_le : Real.log q ≤ V
  half_ambient_le_log_auxiliary : V / 2 ≤ Real.log q
  companion_scale_pos : 0 < LE
  companion_scale_le : LE ≤ V
  companion_scale_small : (K : ℝ) * LE ≤ V / 40
  primorial_small : (primorial w : ℝ) ≤ Real.exp (V / 8)
  interval_large : Real.exp (V / 2) ≤ T
  cutoff_small : (w : ℝ) ≤ Real.log (V + 1)
  companion_scale_lower : 2 * (V + 1) ^ (3 / 4 : ℝ) ≤ LE

theorem tendsto_sourceAnalyticPreSievedWeightSum_normalized
    {α J : Type*} {l : Filter α} [l.IsCountablyGenerated]
    (K : ℕ) (hK : 0 < K) (S : Finset J)
    (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFsmooth : ∀ j i, ContDiff ℝ ∞ (F j i))
    (hGcompact : HasCompactSupport G) (hGsmooth : ContDiff ℝ ∞ G)
    (hFsimplex : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hFceiling : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (w m q T : α → ℕ) (V LE : α → ℝ)
    (hw : Tendsto w l atTop) (hV : Tendsto V l atTop)
    (hdata : ∀ᶠ a in l, SourceNormalizationConditions K (w a) (m a) (q a) (T a) (V a) (LE a)) :
    Tendsto (fun a ↦
      fullAffineFourierNormalization K (w a) (m a) (q a) (twoFamilySelbergScales (V a) (LE a)) *
        (sourceAnalyticPreSievedWeightSum (preSievedShifts K (w a))
          (sourceAnalyticPrimeCutoff S F G (w a) (V a) (LE a)) S
          (fun j h ↦ F j ((preSievedShiftEquiv K (w a)).symm h)) G
          (V a) (LE a) (w a) (m a) (q a) (T a) : ℂ) / (T a : ℂ)) l
      (𝓝 (selbergTensorSquareMainConstant S (fun j ↦ twoFamilySelbergProfiles (F j) G))) := by
  let L (a : α) : (Fin K ⊕ Fin K) → ℝ := twoFamilySelbergScales (V a) (LE a)
  let P (a : α) := sourceAnalyticPrimeCutoff S F G (w a) (V a) (LE a)
  let Fw (a : α) (j : J) (h : preSievedShifts K (w a)) :=
    F j ((preSievedShiftEquiv K (w a)).symm h)
  have hLlower : ∀ᶠ a in l, ∀ i, 2 * (V a + 1) ^ (3 / 4 : ℝ) ≤ L a i := by
    filter_upwards [hdata] with a ha
    intro i
    cases i
    · exact ha.companion_scale_lower.trans ha.companion_scale_le
    · exact ha.companion_scale_lower
  have hLupper : ∀ᶠ a in l, ∀ i, L a i ≤ V a := by
    filter_upwards [hdata] with a ha
    intro i
    cases i
    · exact le_rfl
    · exact ha.companion_scale_le
  have hmain := tendsto_compactAffineTensorSquareSum_actual_normalized K w m q V L hw hV
    (hdata.mono fun a ha ↦ ha.cofactor_pos) (hdata.mono fun a ha ↦ ha.auxiliary_prime)
    (hdata.mono fun a ha ↦ ha.cutoff_lt_auxiliary) (hdata.mono fun a ha ↦ ha.cutoff_small)
    (hdata.mono fun a ha ↦ ha.log_cofactor_le) (hdata.mono fun a ha ↦ ha.log_auxiliary_le)
    hLlower hLupper S (fun j ↦ twoFamilySelbergProfiles (F j) G)
    (fun j hj ↦ hasCompactSupport_twoFamilySelbergProfiles (F j) G (hFcompact j) hGcompact)
    (fun j hj ↦ contDiff_twoFamilySelbergProfiles (F j) G (hFsmooth j) hGsmooth)
  obtain ⟨C, hC, hcoef⟩ := exists_uniform_sourceAnalyticSelbergCoefficient_bound S F G
    hFcompact (fun j i ↦ (hFsmooth j i).continuous) hGcompact hGsmooth.continuous
  have hbound : ∀ᶠ a in l, ∀ (d e : preSievedShifts K (w a) → ℕ),
      |sourceAnalyticSelbergCoefficient S (Fw a) G (V a) (LE a) d e| ≤ C := by
    apply Eventually.of_forall
    intro a d e
    rw [sourceAnalyticSelbergCoefficient_equiv (preSievedShiftEquiv K (w a)) S F G]
    exact hcoef (V a) (LE a) _ _
  have hsimplex : ∀ᶠ a in l, ∀ j ∈ S, ∀ u : preSievedShifts K (w a) → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, Fw a j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10 :=
    Eventually.of_forall fun a ↦
      sourceSimplexSupport_equiv (preSievedShiftEquiv K (w a)) S F hFsimplex
  have herror := tendsto_sourceAnalyticSelbergNormalizedEndpoint_zero
    K hK S w m q T P V LE Fw G hw hV
    (fun a ↦ selectedFourierPrimeCutoff_prime _ _)
    (hdata.mono fun a ha ↦ ha.cofactor_pos) (hdata.mono fun a ha ↦ ha.cofactor_even)
    (hdata.mono fun a ha ↦ ha.auxiliary_prime) (hdata.mono fun a ha ↦ ha.cutoff_lt_auxiliary)
    hC hbound hsimplex hGsupport
    (hdata.mono fun a ha ↦ ⟨ha.companion_scale_pos, ha.companion_scale_le,
      ha.companion_scale_small, ha.primorial_small, ha.interval_large⟩)
  have hlim := hmain.add herror
  simp only [add_zero] at hlim
  apply hlim.congr'
  filter_upwards [hdata, hw.eventually_ge_atTop (max K 2), hV.eventually_ge_atTop 1]
    with a ha hwa hVa
  have hVa0 : 0 < V a := by linarith
  have hTa : 0 < T a := by
    exact_mod_cast (Real.exp_pos (V a / 2)).trans_le ha.interval_large
  have hDq : V a / 10 < Real.log (q a) := by linarith [ha.half_ambient_le_log_auxiliary]
  have hEq : LE a < Real.log (q a) := by
    have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hLE := mul_le_mul_of_nonneg_right hKreal ha.companion_scale_pos.le
    linarith [ha.companion_scale_small, ha.half_ambient_le_log_auxiliary]
  exact (sourceAnalyticPreSievedWeightSum_normalized_identity hK ((le_max_right _ _).trans hwa)
    ((le_max_left _ _).trans hwa) ha.cofactor_pos ha.cofactor_even ha.auxiliary_prime hTa
    S F G (V a) (LE a) hVa0 ha.companion_scale_pos hFceiling hGsupport hDq hEq).symm

end

end Erdos4b
