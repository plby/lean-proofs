import ErdosProblems.Erdos1038.TaoUpperCenteredTarget
import ErdosProblems.Erdos1038.TaoUpperCaseTwoMeasureCertificate

/-!
# Closing Tao's second parameter range

This module plugs the genuine Case 2 interval-density measure into the
centered affine quantile contradiction.
-/

open scoped ENNReal
open MeasureTheory Set Polynomial

namespace Erdos1038

noncomputable section

/-- A counterexample at or above the sharp volume threshold cannot have
its normalized center in Tao's second parameter range. -/
theorem false_of_taoCaseTwo_normalizedCenter
    {f : Polynomial ℝ} (hf : IsAdmissible f)
    (hfarLeft : closedUnitSublevelLeft f hf < -Real.sqrt 2)
    (hvolume : ENNReal.ofReal taoUpperEdge ≤ sublevelVolume f)
    (hcaseTwo : taoCaseTwoCenterFloor ≤ taoNormalizedCenter f hf) :
    False := by
  let t0 := taoNormalizedCenter f hf
  obtain ⟨Q, hQleft, hQupper, hQF, _⟩ :=
    exists_closedTarget_quantileData_of_le hf hfarLeft hvolume
  have hQleftCenter : Q.left = t0 - 1 := by
    simpa [t0, taoNormalizedSourceLeft] using! hQleft
  have hQF' : Q.F =
      volumeCumulative (taoNormalizedRightTarget f hf) Q.left := by
    rw [hQleft]
    exact hQF
  have ht0Upper : t0 ≤ taoUpperEdge := by
    have hleftMem := (closedUnitSublevelLeft_isLeast hf).1
    have hleftLower :=
      (closedUnitSublevelSet_subset_Icc hf hleftMem).1
    have ht0Two : t0 ≤ 2 := by
      dsimp [t0, taoNormalizedCenter]
      linarith
    have htwoUpper : (2 : ℝ) < taoUpperEdge := by
      unfold taoUpperEdge
      nlinarith [one_lt_sqrt_two]
    exact ht0Two.trans htwoUpper.le
  have hleftPositive : 0 < t0 - 1 := by
    simpa [t0, taoNormalizedSourceLeft] using!
      taoNormalizedSourceLeft_pos hf hfarLeft
  have hzeroQleft : 0 < Q.left := by
    rw [hQleftCenter]
    exact hleftPositive
  have hcenteredZero :
      Q.centeredRearrangement t0 0 =
        closedUnitSublevelLeft f hf := by
    rw [QuantileData.centeredRearrangement,
      Q.rearrangement_of_lt_left hzeroQleft]
    dsimp [t0, taoNormalizedCenter]
    ring
  have hsupport : ∀ᵐ s ∂taoCaseTwoTrialMeasure,
      (s < Q.left ∧
          Q.centeredRearrangement t0 s ∈ closedUnitSublevelSet f) ∨
        s ∈ Ioc Q.left Q.upper := by
    filter_upwards [ae_taoCaseTwoTrialMeasure_source_support
      ht0Upper] with s hs
    rcases hs with rfl | hsInterval
    · left
      refine ⟨hzeroQleft, ?_⟩
      rw [hcenteredZero]
      exact (closedUnitSublevelLeft_isLeast hf).1
    · right
      rw [hQleftCenter, hQupper]
      exact hsInterval
  have hbasicSupport : ∀ᵐ s ∂taoCaseTwoTrialMeasure,
      s < Q.left ∨ s ∈ Icc Q.left Q.upper := by
    filter_upwards [hsupport] with s hs
    rcases hs with hsFixed | hsInterval
    · exact Or.inl hsFixed.1
    · exact Or.inr ⟨hsInterval.1.le, hsInterval.2⟩
  have hsingleton : ∀ s ∈ Icc (t0 - 1) (t0 + 1),
      taoCaseTwoTrialMeasure {s} = 0 := by
    intro s hs
    apply taoCaseTwoTrialMeasure_singleton
    exact ne_of_gt (hleftPositive.trans_le hs.1)
  have htargetMem : ∀ᵐ s ∂taoCaseTwoTrialMeasure,
      Q.centeredRearrangement t0 s ∈ closedUnitSublevelSet f := by
    filter_upwards [hsupport] with s hs
    rcases hs with hsFixed | hsInterval
    · exact hsFixed.2
    · have hnormalized :=
        Q.rearrangement_mem_of_volumeCumulative_of_isClosed
          (taoNormalizedRightTarget f hf) hQF'
          (isClosed_taoNormalizedRightTarget hf) hsInterval
      have htarget := hnormalized.1
      change Q.rearrangement s + closedUnitSublevelLeft f hf ∈
        closedUnitSublevelSet f at htarget
      change Q.rearrangement s - t0 ∈ closedUnitSublevelSet f
      simpa [t0, taoNormalizedCenter, sub_eq_add_neg] using! htarget
  have hsource : ∀ t ∈ Icc (-1 : ℝ) 1,
      Integrable (fun s ↦ Real.log
        |Q.extendedInverseCoordinate (t + t0) - s|)
        taoCaseTwoTrialMeasure := by
    intro t _
    exact integrable_log_t_sub_taoCaseTwoTrialMeasure
      (Q.extendedInverseCoordinate (t + t0))
  have htarget : ∀ t ∈ Icc (-1 : ℝ) 1,
      Integrable (fun s ↦ Real.log
        |t - Q.centeredRearrangement t0 s|)
        taoCaseTwoTrialMeasure := by
    intro t ht
    have htLeft : Q.left ≤ t + t0 := by
      rw [hQleftCenter]
      linarith [ht.1]
    have hs0Mem :=
      Q.extendedInverseCoordinate_mem_centeredRootInterval
        t0 hQleftCenter ht
    exact Q.integrable_log_sub_centeredRearrangement
      taoCaseTwoTrialMeasure f hf t0 ht htLeft hbasicSupport
      (hsingleton _ hs0Mem) (hsource t ht) htargetMem
  apply Q.false_of_normalizedCenteredQuantile_pushforward
    f hf taoCaseTwoTrialMeasure hQleft hQF'
  · simpa [t0] using! hsupport
  · simpa [t0] using! hsingleton
  · simpa [t0] using! hsource
  · simpa [t0] using! htarget
  · simpa [t0] using!
      (taoCaseTwoTrialMeasure_potential_neg hcaseTwo)

end

end Erdos1038
