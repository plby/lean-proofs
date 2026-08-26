/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedNormalizedError

/-!
# Uniform normalized error for every source prime interval

The prime count is its actual finite cardinality. Its lower bound and
the singular-series lower bound are both proved, and all choices of
the pin, cutoff and residual parameters share one error envelope.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology

theorem threeQuarter_log_le_log_of_four_mul_ge {X x : ℕ} (hX : 0 < X)
    (hfour : X ≤ 4 * x) (hlog : 4 * Real.log 4 ≤ Real.log X) :
    3 * Real.log X / 4 ≤ Real.log x := by
  have hx : 0 < x := by omega
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hXlog : Real.log X ≤ Real.log (4 * (x : ℝ)) :=
    Real.log_le_log (by exact_mod_cast hX) (by exact_mod_cast hfour)
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hxR.ne'] at hXlog
  linarith

theorem pinnedSourceProgressionErrorBound_nonneg
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (A B : ℕ) (LD LE : ℝ) :
    0 ≤ pinnedSourceProgressionErrorBound S F G h P A B LD LE := by
  unfold pinnedSourceProgressionErrorBound
  apply Finset.sum_nonneg
  intro d hd
  exact mul_nonneg (norm_nonneg _)
    (add_nonneg (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _)
      (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _))

theorem exists_uniform_normalized_pinnedSource_error_bound
    {K : ℕ} {I : Type*} (S : Finset I) (F : I → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFcont : ∀ j i, Continuous (F j i))
    (hGcompact : HasCompactSupport G) (hGcont : Continuous G)
    (hFsupport : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (J : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C ≥ 0, ∃ W : ℕ, ∀ᶠ X : ℕ in atTop,
      ∀ (h : Fin K) (P : Finset ℕ) (w m p₀ Y A B : ℕ),
        (∀ p ∈ P, p.Prime) → W ≤ w → 0 < m → p₀.Prime → Y < p₀ →
        (m * p₀ - 1).Coprime (primorial Y) → 0 < Real.log Y → Real.log Y ≤ Real.log X →
        (K : ℝ) * Real.log Y ≤ Real.log X / 40 → X ≤ 2 * A → A ≤ B → B ≤ X →
        δ * (X : ℝ) / Real.log X ^ J ≤ (B : ℝ) - A →
        (Real.log X ^ (K - 1) * Real.log Y ^ (K - 1)) /
            (pinnedSingularSeries h w m p₀ Y * (auxiliaryPrimeInterval A B).card) *
          pinnedSourceProgressionErrorBound S F G h P A B (Real.log X) (Real.log Y) ≤
            C / Real.log X := by
  let L : ℕ := 2 * K + J + 2
  obtain ⟨C₀, hC₀, X₀, hX₀, hsource⟩ := exists_uniform_pinnedSourceEndpoint_logSaving
    S F G hFcompact hFcont hGcompact hGcont hFsupport hGsupport L
  obtain ⟨W, hW⟩ := exists_uniform_half_le_pinnedSingularSeries K
  refine ⟨8 * C₀ * 2 ^ L / δ, by positivity, W, ?_⟩
  have hlogTop : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_primeInterval_card_lower J hδ,
    eventually_ge_atTop (max 8 (4 * X₀)), hlogTop.eventually_ge_atTop 80,
    hlogTop.eventually_ge_atTop (4 * Real.log 4)] with X hprimeCount hX hlog80 hlog4
  intro h P w m p₀ Y A B hP hw hm hp₀ hYp₀ hcop hLE hLEV hsmall hhalf hAB hBX hlength
  have hXpos : 0 < X := by omega
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hVpos : 0 < Real.log X := by linarith
  have hXA : X₀ ≤ A - 1 := by omega
  have hXB : X₀ ≤ B - 1 := by omega
  have hfourA : X ≤ 4 * (A - 1) := by omega
  have hfourB : X ≤ 4 * (B - 1) := by omega
  have hlogA := threeQuarter_log_le_log_of_four_mul_ge hXpos hfourA hlog4
  have hlogB := threeQuarter_log_le_log_of_four_mul_ge hXpos hfourB hlog4
  have hEA : pinnedSourceEndpointErrorBound S F G h P (A - 1) (Real.log X) (Real.log Y) ≤
      C₀ * 2 ^ L * (X : ℝ) / Real.log X ^ L := by
    apply (hsource h P (Real.log X) (Real.log Y) (A - 1) hP hlog80 hLE hsmall hlogA hXA).trans
    exact logSaving_term_le_ambient L hC₀ (Nat.cast_nonneg _)
      (by exact_mod_cast (Nat.sub_le A 1).trans (hAB.trans hBX)) hVpos (by linarith)
  have hEB : pinnedSourceEndpointErrorBound S F G h P (B - 1) (Real.log X) (Real.log Y) ≤
      C₀ * 2 ^ L * (X : ℝ) / Real.log X ^ L := by
    apply (hsource h P (Real.log X) (Real.log Y) (B - 1) hP hlog80 hLE hsmall hlogB hXB).trans
    exact logSaving_term_le_ambient L hC₀ (Nat.cast_nonneg _)
      (by exact_mod_cast (Nat.sub_le B 1).trans hBX) hVpos (by linarith)
  have herr : pinnedSourceProgressionErrorBound S F G h P A B (Real.log X) (Real.log Y) ≤
      2 * C₀ * 2 ^ L * (X : ℝ) / Real.log X ^ L := by
    rw [pinnedSourceProgressionErrorBound_eq_endpoints]
    exact (add_le_add hEB hEA).trans_eq (by ring)
  have hseries := hW w hw h m p₀ Y hm hp₀ hYp₀ hcop
  have hcount := hprimeCount A B hhalf hAB hBX hlength
  have hnorm := normalized_pinned_error_le_inverse_ambient (2 * K) J hδ hC₀ hXreal hVpos
    (pinnedScaleProduct_le_ambient_power K (by linarith) hLE.le hLEV) hseries hcount
    (pinnedSourceProgressionErrorBound_nonneg S F G h P A B (Real.log X) (Real.log Y)) herr
  exact hnorm.trans_eq (by dsimp only [L]; ring)

end

end Erdos4b
