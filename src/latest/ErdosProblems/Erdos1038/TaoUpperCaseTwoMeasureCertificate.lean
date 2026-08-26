import ErdosProblems.Erdos1038.TaoUpperCaseTwoCertificate
import ErdosProblems.Erdos1038.TaoUpperIntervalTrialMeasures

/-!
# Measure-theoretic package for Tao's Case 2

This file combines the checked scalar certificate with the genuine
interval-density measure and records the support and atomlessness facts
needed by the expansive-quantile argument.
-/

open MeasureTheory Set

namespace Erdos1038

noncomputable section

/-- The genuine Case 2 measure has strictly negative potential throughout
every root interval in Tao's second parameter range. -/
theorem taoCaseTwoTrialMeasure_potential_neg
    {t0 : ℝ} (ht0 : taoCaseTwoCenterFloor ≤ t0) :
    ∀ t ∈ Icc (t0 - 1) (t0 + 1),
      taoTrialMeasurePotential taoCaseTwoTrialMeasure t < 0 := by
  intro t ht
  have hfloor := tao_case_two_center_interval_mem_floor ht0 ht
  have htPos : 0 < t := by
    unfold taoCaseTwoFloor at hfloor
    norm_num at hfloor ⊢
    linarith
  rw [taoCaseTwoTrialMeasure_potential htPos]
  exact taoCaseTwoPotential_neg_of_floor_le t hfloor

/-- The Case 2 measure is supported either at zero or inside the half-open
quantile source interval `(t₀-1,M]`. -/
theorem ae_taoCaseTwoTrialMeasure_source_support
    {t0 : ℝ} (ht0Upper : t0 ≤ taoUpperEdge) :
    ∀ᵐ s ∂taoCaseTwoTrialMeasure,
      s = 0 ∨ s ∈ Ioc (t0 - 1) taoUpperEdge := by
  filter_upwards [ae_taoCaseTwoTrialMeasure_mem] with s hs
  rcases hs with rfl | hs
  · exact Or.inl rfl
  · refine Or.inr ⟨?_, hs.2⟩
    have hgap : taoUpperEdge < taoCaseTwoLeftEndpoint + 1 := by
      linarith [tao_case_two_upperEdge_sub_leftEndpoint_lt_one]
    linarith [hs.1, ht0Upper, hgap]

/-- In particular, after marking zero as an already-good fixed point, the
Case 2 source support has the exact disjunction required by the closed
quantile contradiction theorem. -/
theorem ae_taoCaseTwoTrialMeasure_good_zero_or_source
    {E : Set ℝ} {t0 : ℝ} (hzero : 0 ∈ E)
    (ht0Lower : taoCaseTwoCenterFloor ≤ t0)
    (ht0Upper : t0 ≤ taoUpperEdge) :
    ∀ᵐ s ∂taoCaseTwoTrialMeasure,
      (s < t0 - 1 ∧ s ∈ E) ∨
        s ∈ Ioc (t0 - 1) taoUpperEdge := by
  filter_upwards [ae_taoCaseTwoTrialMeasure_source_support
    ht0Upper] with s hs
  rcases hs with rfl | hs
  · left
    constructor
    · unfold taoCaseTwoCenterFloor at ht0Lower
      norm_num at ht0Lower ⊢
      linarith
    · exact hzero
  · exact Or.inr hs

/-- The Case 2 measure has no atoms in the half-open quantile source
interval. -/
theorem taoCaseTwoTrialMeasure_singleton_of_mem_source
    {t0 s : ℝ} (ht0 : taoCaseTwoCenterFloor ≤ t0)
    (hs : s ∈ Ico (t0 - 1) taoUpperEdge) :
    taoCaseTwoTrialMeasure {s} = 0 := by
  apply taoCaseTwoTrialMeasure_singleton
  have hleftPos : 0 < t0 - 1 := by
    unfold taoCaseTwoCenterFloor at ht0
    norm_num at ht0 ⊢
    linarith
  exact ne_of_gt (hleftPos.trans_le hs.1)

end

end Erdos1038
