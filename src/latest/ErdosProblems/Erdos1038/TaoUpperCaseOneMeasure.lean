import ErdosProblems.Erdos1038.TaoUpperCaseOneCertificate
import ErdosProblems.Erdos1038.TaoUpperIntervalTrialMeasures

/-!
# Genuine measure for Tao's first upper-bound trial

The checked Case 1 scalar certificate uses `δ₀ + C δ_M`.  This file records
that finite measure, its exact potential, and its elementary support and
atom facts so it can use the same centered quantile bridge as Cases 2 and 3.
-/

open scoped ENNReal
open MeasureTheory Set

namespace Erdos1038

noncomputable section

def taoCaseOneTrialMeasure (C : ℝ) : Measure ℝ :=
  Measure.dirac 0 + ENNReal.ofReal C • Measure.dirac taoUpperEdge

instance instIsFiniteMeasureTaoCaseOneTrialMeasure (C : ℝ) :
    IsFiniteMeasure (taoCaseOneTrialMeasure C) := by
  letI : IsFiniteMeasure
      (ENNReal.ofReal C • Measure.dirac taoUpperEdge) :=
    (Measure.dirac taoUpperEdge).smul_finite (by simp)
  unfold taoCaseOneTrialMeasure
  infer_instance

theorem integrable_taoCaseOneTrialMeasure (C : ℝ) (g : ℝ → ℝ) :
    Integrable g (taoCaseOneTrialMeasure C) := by
  unfold taoCaseOneTrialMeasure
  apply Integrable.add_measure
  · exact integrable_dirac (by finiteness)
  · exact (integrable_dirac (by finiteness)).smul_measure (by simp)

theorem taoCaseOneTrialMeasure_potential
    {C t : ℝ} (hC : 0 ≤ C) (ht : 0 < t)
    (htM : t < taoUpperEdge) :
    taoTrialMeasurePotential (taoCaseOneTrialMeasure C) t =
      taoTwoAtomTrialPotential taoUpperEdge C t := by
  have hzero : Integrable (fun x : ℝ ↦ Real.log |t - x|)
      (Measure.dirac 0) := integrable_dirac (by finiteness)
  have hedge : Integrable (fun x : ℝ ↦ Real.log |t - x|)
      (ENNReal.ofReal C • Measure.dirac taoUpperEdge) :=
    (integrable_dirac (by finiteness)).smul_measure (by simp)
  rw [taoCaseOneTrialMeasure,
    taoTrialMeasurePotential_add hzero hedge]
  unfold taoTrialMeasurePotential
  rw [integral_dirac, integral_smul_measure,
    ENNReal.toReal_ofReal hC, integral_dirac]
  simp only [smul_eq_mul, sub_zero]
  rw [abs_of_pos ht, abs_of_nonpos (sub_nonpos.mpr htM.le)]
  have hneg : -(t - taoUpperEdge) = taoUpperEdge - t := by ring
  rw [hneg]
  unfold taoTwoAtomTrialPotential
  ring

theorem ae_taoCaseOneTrialMeasure_mem (C : ℝ) :
    ∀ᵐ s ∂taoCaseOneTrialMeasure C,
      s = 0 ∨ s = taoUpperEdge := by
  rw [taoCaseOneTrialMeasure, ae_add_measure_iff]
  constructor
  · simp
  · apply Measure.ae_smul_measure
    simp

theorem taoCaseOneTrialMeasure_singleton
    {C s : ℝ} (hs0 : s ≠ 0) (hsM : s ≠ taoUpperEdge) :
    taoCaseOneTrialMeasure C {s} = 0 := by
  simp [taoCaseOneTrialMeasure, hs0, hsM]

/-- The first trial has no atoms in the translated empirical root interval.
Both of its atoms lie strictly outside that interval. -/
theorem taoCaseOneTrialMeasure_singleton_on_rootInterval
    {C t0 s : ℝ} (ht0Lower : Real.sqrt 2 < t0)
    (ht0Upper : t0 < taoCaseOneCeiling)
    (hs : s ∈ Icc (t0 - 1) (t0 + 1)) :
    taoCaseOneTrialMeasure C {s} = 0 := by
  rcases tao_case_one_interval_geometry ht0Lower ht0Upper with
    ⟨hleftPos, _, hrightM, _, _, _⟩
  apply taoCaseOneTrialMeasure_singleton
  · exact ne_of_gt (hleftPos.trans_le hs.1)
  · exact ne_of_lt (hs.2.trans_lt hrightM)

end

end Erdos1038
