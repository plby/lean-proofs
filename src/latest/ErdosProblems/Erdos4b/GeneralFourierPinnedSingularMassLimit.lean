/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedSingularMassLower

/-!
# Eventual singular-weighted prime-mass lower bound under source conditions

The cofactor is automatically even by residual coprimality. The positive
pinned variational constant gives a uniform lower bound for the literal
weighted prime sum, with the residual cofactor correction intact.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology ContDiff

theorem even_cofactor_of_pinnedResidual_coprime
    {m p₀ Y : ℕ} (hp₀ : p₀.Prime) (hY : 2 ≤ Y) (hYp₀ : Y < p₀)
    (hcop : (m * p₀ - 1).Coprime (primorial Y)) : Even m := by
  have hcop2 := hcop.of_dvd_right (Nat.prime_two.dvd_primorial_iff.mpr hY)
  have hnot : ¬2 ∣ m * p₀ - 1 := (Nat.prime_two.coprime_iff_not_dvd).mp hcop2.symm
  by_contra hn
  have hmOdd : Odd m := Nat.not_even_iff_odd.mp hn
  have hpOdd : Odd p₀ := hp₀.odd_of_ne_two (by omega)
  have hprod : Odd (m * p₀) := hmOdd.mul hpOdd
  have heven : Even (m * p₀ - 1) := Nat.Odd.sub_odd hprod (by norm_num : Odd (1 : ℕ))
  exact hnot heven.two_dvd

theorem eventually_pinnedSingularWeightedPrimeMass_lower
    {α I : Type*} {l : Filter α} [l.IsCountablyGenerated] {K : ℕ}
    (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i))
    (hFsmooth : ∀ j i, ContDiff ℝ ∞ (F j i))
    (hGcompact : HasCompactSupport G) (hGsmooth : ContDiff ℝ ∞ G)
    (hFsimplex : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hFceiling : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) (h : Fin K)
    (hmain : 0 < sourcePinnedFirstVariationalIntegral S F h *
      sourcePinnedCompanionVariationalIntegral K G)
    (J : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (w m p₀ Y X A B N : α → ℕ) (hw : Tendsto w l atTop) (hX : Tendsto X l atTop)
    (hdata : ∀ᶠ a in l, SourcePinnedNormalizationConditions K
      (w a) (m a) (p₀ a) (Y a) (X a) (A a) (B a) J δ)
    (hN : ∀ᶠ a in l,
      jointSourceCommonPrimeBound S F G (Real.log (X a)) (Real.log (Y a)) ≤ N a)
    (hYN : ∀ᶠ a in l, Y a ≤ N a) :
    ∀ᶠ a in l,
      (sourcePinnedFirstVariationalIntegral S F h * sourcePinnedCompanionVariationalIntegral K G) *
        residualCofactorLocalProduct (Y a) (m a) * (auxiliaryPrimeInterval (A a) (B a)).card /
          (4 * (Real.log (X a) ^ (K - 1) * Real.log (Y a) ^ (K - 1))) ≤
        ∑ q ∈ auxiliaryPrimeInterval (A a) (B a),
          pinnedSourceRealIntegerWeight S F G h
            (selectedFourierPrimeCutoff (fun p ↦ decide (w a < p)) (boundedFourierPrimes (N a)))
            (w a) (m a) (p₀ a) q (Real.log (X a)) (Real.log (Y a)) /
              largeGapSingularSeries (preSievedShifts K (w a)) (m a) q (Y a) := by
  let M := sourcePinnedFirstVariationalIntegral S F h * sourcePinnedCompanionVariationalIntegral K G
  have hM : 0 < M := hmain
  have hweight := eventually_sourcePinnedInverseSingularNormalizedWeight_lower S F G
    hFcompact hFsmooth hGcompact hGsmooth hFsimplex hFceiling hGsupport h J hδ
    (by positivity : 0 < M / 2) w m p₀ Y X A B N hw hX hdata hN hYN
  have hV : Tendsto (fun a ↦ Real.log (X a)) l atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hX)
  have hY := (tendsto_sourceCutoff_atTop_and_ambient_div_zero Y (fun a ↦ Real.log (X a)) hV
    (hdata.mono fun a ha ↦ ha.companion_scale_lower)).1
  have hcount := eventually_sourcePinned_primeCount_pos hδ w m p₀ Y X A B hX hdata
  filter_upwards [hweight, hdata, hcount, hw.eventually_ge_atTop (4 * K),
    hX.eventually_gt_atTop 1, hY.eventually_gt_atTop 1] with a hwa ha hca hfour hXa hYa
  have hmeven := even_cofactor_of_pinnedResidual_coprime ha.pinned_prime hYa
    ha.companion_lt_pinned ha.residual_coprime
  have hc : M / 2 ≤ sourcePinnedInverseSingularNormalizedWeight S F G h
      (w a) (m a) (p₀ a) (Y a) (X a) (A a) (B a) (N a) := by
    change M - M / 2 < _ at hwa
    linarith
  have hb := pinnedSingularWeightedPrimeMass_lower S F G h hfour ha.cofactor_pos hmeven
    ha.pinned_prime ha.cutoff_le_companion ha.companion_lt_pinned ha.residual_coprime
    hXa hYa hca (by positivity : 0 ≤ M / 2) hc
  calc
    _ = (M / 2) * residualCofactorLocalProduct (Y a) (m a) *
        (auxiliaryPrimeInterval (A a) (B a)).card /
          (2 * (Real.log (X a) ^ (K - 1) * Real.log (Y a) ^ (K - 1))) := by
      dsimp only [M]
      ring
    _ ≤ _ := hb

end

end Erdos4b
