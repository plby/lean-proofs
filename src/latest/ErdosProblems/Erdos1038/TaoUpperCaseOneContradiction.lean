import ErdosProblems.Erdos1038.TaoUpperCenteredTarget
import ErdosProblems.Erdos1038.TaoUpperCaseOneMeasure

/-!
# End-to-end quantile contradiction in Tao's first range

This module plugs the checked two-atom certificate into the centered closed
target bridge.  The only inputs left are the quantile data supplied by the
target-volume construction and membership of the center in Case 1.
-/

open MeasureTheory Set Polynomial

namespace Erdos1038

noncomputable section

/-- A far-left target whose normalized center lies in Case 1 is impossible
once its normalized right target supplies the required quantile. -/
theorem false_of_tao_case_one_quantile
    (Q : QuantileData) (f : Polynomial ℝ) (hf : IsAdmissible f)
    (hfar : closedUnitSublevelLeft f hf < -Real.sqrt 2)
    (hcenterUpper : taoNormalizedCenter f hf < taoCaseOneCeiling)
    (hQleft : Q.left = taoNormalizedSourceLeft f hf)
    (hQupper : Q.upper = taoUpperEdge)
    (hF : Q.F = volumeCumulative (taoNormalizedRightTarget f hf) Q.left) :
    False := by
  let t0 := taoNormalizedCenter f hf
  have ht0Lower : Real.sqrt 2 < t0 := by
    exact taoNormalizedCenter_gt_sqrt_two hf hfar
  have ht0Upper : t0 < taoCaseOneCeiling := hcenterUpper
  obtain ⟨C, hC, htrialScalar⟩ :=
    exists_tao_case_one_twoAtomTrial_checked ht0Lower ht0Upper
  have hQleftCenter : Q.left = t0 - 1 := by
    simpa [t0, taoNormalizedSourceLeft] using! hQleft
  have hzeroLeft : 0 < Q.left := by
    rw [hQleft]
    exact taoNormalizedSourceLeft_pos hf hfar
  have hcenteredZero :
      Q.centeredRearrangement t0 0 =
        closedUnitSublevelLeft f hf := by
    rw [QuantileData.centeredRearrangement,
      Q.rearrangement_of_lt_left hzeroLeft]
    dsimp [t0, taoNormalizedCenter]
    ring
  have hsupport : ∀ᵐ s ∂taoCaseOneTrialMeasure C,
      (s < Q.left ∧
          Q.centeredRearrangement t0 s ∈ closedUnitSublevelSet f) ∨
        s ∈ Ioc Q.left Q.upper := by
    filter_upwards [ae_taoCaseOneTrialMeasure_mem C] with s hs
    rcases hs with rfl | rfl
    · left
      refine ⟨hzeroLeft, ?_⟩
      rw [hcenteredZero]
      exact (closedUnitSublevelLeft_isLeast hf).1
    · right
      rw [hQleft, hQupper]
      exact ⟨taoNormalizedSourceLeft_lt_upperEdge hf, le_rfl⟩
  have hbasicSupport : ∀ᵐ s ∂taoCaseOneTrialMeasure C,
      s < Q.left ∨ s ∈ Icc Q.left Q.upper := by
    filter_upwards [hsupport] with s hs
    rcases hs with hsFixed | hsInterval
    · exact Or.inl hsFixed.1
    · exact Or.inr ⟨hsInterval.1.le, hsInterval.2⟩
  have hsingleton : ∀ s ∈ Icc (t0 - 1) (t0 + 1),
      taoCaseOneTrialMeasure C {s} = 0 := by
    intro s hs
    exact taoCaseOneTrialMeasure_singleton_on_rootInterval
      ht0Lower ht0Upper hs
  have htargetMem : ∀ᵐ s ∂taoCaseOneTrialMeasure C,
      Q.centeredRearrangement t0 s ∈ closedUnitSublevelSet f := by
    filter_upwards [hsupport] with s hs
    rcases hs with hsFixed | hsInterval
    · exact hsFixed.2
    · have hnormalized :=
        Q.rearrangement_mem_of_volumeCumulative_of_isClosed
          (taoNormalizedRightTarget f hf) hF
          (isClosed_taoNormalizedRightTarget hf) hsInterval
      have htarget := hnormalized.1
      change Q.rearrangement s + closedUnitSublevelLeft f hf ∈
        closedUnitSublevelSet f at htarget
      change Q.rearrangement s - t0 ∈ closedUnitSublevelSet f
      simpa [t0, taoNormalizedCenter, sub_eq_add_neg] using! htarget
  have hsource : ∀ t ∈ Icc (-1 : ℝ) 1,
      Integrable (fun s ↦ Real.log
        |Q.extendedInverseCoordinate (t + t0) - s|)
        (taoCaseOneTrialMeasure C) := by
    intro t _
    exact integrable_taoCaseOneTrialMeasure C _
  have htarget : ∀ t ∈ Icc (-1 : ℝ) 1,
      Integrable (fun s ↦ Real.log
        |t - Q.centeredRearrangement t0 s|)
        (taoCaseOneTrialMeasure C) := by
    intro t ht
    have htLeft : Q.left ≤ t + t0 := by
      rw [hQleftCenter]
      linarith [ht.1]
    have hs0Mem :=
      Q.extendedInverseCoordinate_mem_centeredRootInterval
        t0 hQleftCenter ht
    exact Q.integrable_log_sub_centeredRearrangement
      (taoCaseOneTrialMeasure C) f hf t0 ht htLeft hbasicSupport
      (hsingleton _ hs0Mem) (hsource t ht) htargetMem
  have htrial : ∀ s ∈ Icc (t0 - 1) (t0 + 1),
      taoTrialMeasurePotential (taoCaseOneTrialMeasure C) s < 0 := by
    intro s hs
    have hs' : s ∈ Icc (t0 - 1) (t0 + 1) := by
      exact hs
    rcases tao_case_one_interval_geometry ht0Lower ht0Upper with
      ⟨hleftPos, _, hrightM, _, _, _⟩
    rw [taoCaseOneTrialMeasure_potential hC
      (hleftPos.trans_le hs'.1) (hs'.2.trans_lt hrightM)]
    exact htrialScalar s hs'
  apply Q.false_of_normalizedCenteredQuantile_pushforward
    f hf (taoCaseOneTrialMeasure C) hQleft hF
  · simpa [t0] using! hsupport
  · simpa [t0] using! hsingleton
  · simpa [t0] using! hsource
  · simpa [t0] using! htarget
  · simpa [t0] using! htrial

/-- End-to-end Case 1 exclusion under the non-strict sharp-volume
threshold. -/
theorem false_of_taoCaseOne_normalizedCenter
    {f : Polynomial ℝ} (hf : IsAdmissible f)
    (hfarLeft : closedUnitSublevelLeft f hf < -Real.sqrt 2)
    (hvolume : ENNReal.ofReal taoUpperEdge ≤ sublevelVolume f)
    (hcaseOne : taoNormalizedCenter f hf < taoCaseOneCeiling) :
    False := by
  obtain ⟨Q, hQleft, hQupper, hQF, _⟩ :=
    exists_closedTarget_quantileData_of_le hf hfarLeft hvolume
  have hQF' : Q.F =
      volumeCumulative (taoNormalizedRightTarget f hf) Q.left := by
    rw [hQleft]
    exact hQF
  exact false_of_tao_case_one_quantile Q f hf hfarLeft hcaseOne
    hQleft hQupper hQF'

end

end Erdos1038
