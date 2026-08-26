import ErdosProblems.Erdos1038.TaoUpperCaseOneCertificateChunks
import Mathlib.Analysis.Convex.Deriv

set_option maxRecDepth 100000

/-!
# A complete checked certificate for Tao's first upper-bound range

This module exposes the analytic consequences of the exact finite
certificates assembled in `TaoUpperCaseOneCertificateChunks`.
-/

open Set

namespace Erdos1038

noncomputable section

theorem taoCaseOneGapSecondDerivative_pos_on_initial
    {t : ℝ} (htLower : Real.sqrt 2 ≤ t) (htUpper : t ≤ 3 / 2) :
    0 < taoCaseOneGapSecondDerivative t := by
  have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hstart : ((707 / 500 : Rat) : ℝ) ≤ t := by
    have h707 : ((707 / 500 : Rat) : ℝ) < Real.sqrt 2 := by
      norm_num
      nlinarith [sqrt_two_sq]
    exact h707.le.trans htLower
  have hfinish : t ≤ (((3 / 2 : Rat) : Rat) : ℝ) := by
    norm_num at htUpper ⊢
    exact htUpper
  rcases exists_interval_of_chain_covers
      taoCaseOneInitialIntervals_cover hstart hfinish with
    ⟨I, hI, hIt⟩
  apply taoCaseOneSecondDerivative_pos_of_certificate hIt
  exact bool_predicate_of_all taoCaseOneInitialIntervals_certify hI

theorem taoCaseOneGap_pos_on_direct
    {t : ℝ} (htLower : 3 / 2 ≤ t)
    (htUpper : t ≤ taoCaseOneCeiling) :
    0 < taoCaseOneGap t := by
  have hstart : (((3 / 2 : Rat) : Rat) : ℝ) ≤ t := by
    norm_num at htLower ⊢
    exact htLower
  have hfinish : t ≤ (((2203 / 1250 : Rat) : Rat) : ℝ) := by
    simpa only [taoCaseOneCeiling, Rat.cast_div, Rat.cast_ofNat] using! htUpper
  rcases exists_interval_of_chain_covers
      taoCaseOneDirectIntervals_cover hstart hfinish with
    ⟨I, hI, hIt⟩
  apply taoCaseOneGap_pos_of_certificate hIt
  exact bool_predicate_of_all taoCaseOneDirectIntervals_certify hI

private theorem continuousOn_taoCaseOneGap_initial :
    ContinuousOn taoCaseOneGap (Icc (Real.sqrt 2) (3 / 2)) := by
  intro t ht
  rcases taoCaseOneInitial_geometry ht.1 ht.2 with
    ⟨hleft, hright, hfarLeft, hfarRight⟩
  exact (hasDerivAt_taoCaseOneGap
    hleft hright hfarLeft hfarRight).continuousAt.continuousWithinAt

private theorem continuousOn_taoCaseOneGapDerivative_initial :
    ContinuousOn taoCaseOneGapDerivative
      (Icc (Real.sqrt 2) (3 / 2)) := by
  intro t ht
  rcases taoCaseOneInitial_geometry ht.1 ht.2 with
    ⟨hleft, hright, hfarLeft, hfarRight⟩
  exact (hasDerivAt_taoCaseOneGapDerivative
    hleft hright hfarLeft hfarRight).continuousAt.continuousWithinAt

theorem strictConvexOn_taoCaseOneGap_initial :
    StrictConvexOn ℝ (Icc (Real.sqrt 2) (3 / 2))
      taoCaseOneGap := by
  have hmonoExplicit :
      StrictMonoOn taoCaseOneGapDerivative
        (Icc (Real.sqrt 2) (3 / 2)) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos
      (convex_Icc (Real.sqrt 2) (3 / 2))
      continuousOn_taoCaseOneGapDerivative_initial
    · intro t ht
      have ht' := interior_subset ht
      rcases taoCaseOneInitial_geometry ht'.1 ht'.2 with
        ⟨hleft, hright, hfarLeft, hfarRight⟩
      exact (hasDerivAt_taoCaseOneGapDerivative
        hleft hright hfarLeft hfarRight).hasDerivWithinAt
    · intro t ht
      have ht' := interior_subset ht
      exact taoCaseOneGapSecondDerivative_pos_on_initial ht'.1 ht'.2
  have hderivEq :
      EqOn (deriv taoCaseOneGap) taoCaseOneGapDerivative
        (Icc (Real.sqrt 2) (3 / 2)) := by
    intro t ht
    rcases taoCaseOneInitial_geometry ht.1 ht.2 with
      ⟨hleft, hright, hfarLeft, hfarRight⟩
    exact (hasDerivAt_taoCaseOneGap
      hleft hright hfarLeft hfarRight).deriv
  have hmonoDeriv :
      StrictMonoOn (deriv taoCaseOneGap)
        (interior (Icc (Real.sqrt 2) (3 / 2))) := by
    intro x hx y hy hxy
    rw [hderivEq (interior_subset hx), hderivEq (interior_subset hy)]
    exact hmonoExplicit (interior_subset hx) (interior_subset hy) hxy
  exact hmonoDeriv.strictConvexOn_of_deriv
    (convex_Icc (Real.sqrt 2) (3 / 2))
    continuousOn_taoCaseOneGap_initial

theorem taoCaseOneGap_pos_on_initial
    {t : ℝ} (htLower : Real.sqrt 2 < t) (htUpper : t ≤ 3 / 2) :
    0 < taoCaseOneGap t := by
  have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrtUpper : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    nlinarith [sqrt_two_sq]
  have hsqrtMem : Real.sqrt 2 ∈ Icc (Real.sqrt 2) (3 / 2) :=
    ⟨le_rfl, hsqrtUpper⟩
  have htMem : t ∈ Icc (Real.sqrt 2) (3 / 2) :=
    ⟨htLower.le, htUpper⟩
  rcases taoCaseOneInitial_geometry le_rfl hsqrtUpper with
    ⟨hleft, hright, hfarLeft, hfarRight⟩
  have hderivZero : HasDerivAt taoCaseOneGap 0 (Real.sqrt 2) := by
    convert! hasDerivAt_taoCaseOneGap
      hleft hright hfarLeft hfarRight using 1
    exact taoCaseOneGapDerivative_at_sqrt_two.symm
  have hslope := strictConvexOn_taoCaseOneGap_initial.lt_slope_of_hasDerivAt
    hsqrtMem htMem htLower hderivZero
  rw [slope_def_field, taoCaseOneGap_at_sqrt_two] at hslope
  have hden : 0 < t - Real.sqrt 2 := sub_pos.mpr htLower
  rcases div_pos_iff.mp hslope with hpos | hneg
  · linarith [hpos.1]
  · linarith [hneg.2]

/-- The checked scalar inequality (2.4) throughout Tao's first range. -/
theorem taoCaseOneGap_pos {t : ℝ}
    (htLower : Real.sqrt 2 < t)
    (htUpper : t < taoCaseOneCeiling) :
    0 < taoCaseOneGap t := by
  by_cases htMid : t ≤ 3 / 2
  · exact taoCaseOneGap_pos_on_initial htLower htMid
  · exact taoCaseOneGap_pos_on_direct (le_of_not_ge htMid) htUpper.le

theorem tao_case_one_ratio {t0 : ℝ}
    (ht0Lower : Real.sqrt 2 < t0)
    (ht0Upper : t0 < taoCaseOneCeiling) :
    -Real.log (t0 - 1) /
          Real.log (taoUpperEdge - (t0 - 1)) <
      Real.log (t0 + 1) /
          (-Real.log (taoUpperEdge - (t0 + 1))) := by
  rcases tao_case_one_interval_geometry ht0Lower ht0Upper with
    ⟨_hl, _hlr, hrM, hMl, hMr1, _hl1⟩
  apply (taoCaseOneGap_pos_iff_ratio hMl (sub_pos.mpr hrM) hMr1).mp
  exact taoCaseOneGap_pos ht0Lower ht0Upper

/-- Tao's two-atom separator exists on the whole first parameter range;
the formerly external numerical comparison is now discharged internally. -/
theorem exists_tao_case_one_twoAtomTrial_checked
    {t0 : ℝ} (ht0Lower : Real.sqrt 2 < t0)
    (ht0Upper : t0 < taoCaseOneCeiling) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ Icc (t0 - 1) (t0 + 1),
        taoTwoAtomTrialPotential taoUpperEdge C t < 0 :=
  exists_tao_case_one_twoAtomTrial ht0Lower ht0Upper
    (tao_case_one_ratio ht0Lower ht0Upper)

end

end Erdos1038

