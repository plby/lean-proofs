import ErdosProblems.Erdos1038.TaoUpperCaseThreeCertificate
import ErdosProblems.Erdos1038.TaoUpperIntervalTrialMeasures

/-!
# Measure-theoretic package for Tao's Case 3
-/

open MeasureTheory Set

namespace Erdos1038

noncomputable section

theorem taoCaseThreeTrialMeasure_potential_neg
    {t0 : ℝ}
    (ht0Lower : taoCaseThreeCenterFloor ≤ t0)
    (ht0Upper : t0 ≤ taoCaseThreeCenterCeiling) :
    ∀ t ∈ Icc (t0 - 1) (t0 + 1),
      taoTrialMeasurePotential taoCaseThreeTrialMeasure t < 0 := by
  intro t ht
  have hinput := tao_case_three_center_interval_mem_input
    ht0Lower ht0Upper ht
  have htPos : 0 < t :=
    tao_case_three_inputFloor_pos.trans_le hinput.1
  rw [taoCaseThreeTrialMeasure_potential htPos]
  exact taoCaseThreePotential_neg_on_input t hinput

theorem ae_taoCaseThreeTrialMeasure_source_support
    {t0 : ℝ} (ht0Upper : t0 ≤ taoCaseThreeCenterCeiling) :
    ∀ᵐ s ∂taoCaseThreeTrialMeasure,
      s = 0 ∨ s ∈ Ioc (t0 - 1) taoUpperEdge := by
  filter_upwards [ae_taoCaseThreeTrialMeasure_mem] with s hs
  rcases hs with rfl | hs
  · exact Or.inl rfl
  · refine Or.inr ⟨?_, hs.2⟩
    have hleft : t0 - 1 < taoCaseThreeLeftA := by
      unfold taoCaseThreeCenterCeiling taoCaseThreeLeftA at *
      linarith
    exact hleft.trans_le hs.1

theorem taoCaseThreeTrialMeasure_singleton_on_rootInterval
    {t0 s : ℝ}
    (ht0Lower : taoCaseThreeCenterFloor ≤ t0)
    (ht0Upper : t0 ≤ taoCaseThreeCenterCeiling)
    (hs : s ∈ Icc (t0 - 1) (t0 + 1)) :
    taoCaseThreeTrialMeasure {s} = 0 := by
  apply taoCaseThreeTrialMeasure_singleton
  · have hleftPos : 0 < t0 - 1 := by
      unfold taoCaseThreeCenterFloor at ht0Lower
      norm_num at ht0Lower ⊢
      linarith
    exact ne_of_gt (hleftPos.trans_le hs.1)
  · have hsUpper : s < taoUpperEdge := by
      have hceiling : taoCaseThreeInputCeiling < taoUpperEdge :=
        tao_case_three_inputCeiling_lt_upperEdge
      unfold taoCaseThreeCenterCeiling taoCaseThreeInputCeiling at *
      linarith [hs.2]
    exact ne_of_lt hsUpper

end

end Erdos1038
