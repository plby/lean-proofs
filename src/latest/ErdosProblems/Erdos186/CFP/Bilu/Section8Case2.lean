/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.ProjectionVolumeCoarse

/-!
# The numerical conclusion of Bilu's Section 8.3, Case 2

Bilu completes Proposition 7.5 by combining four geometric inequalities,
labelled (8.7)--(8.10). Their quotient notation obscures two exact
cancellations. This file records those cancellations in division-free form.
-/

namespace Erdos186.CFP.Bilu.Section8Case2

open scoped ENNReal

/-- Division-free combination of Bilu's inequalities (8.7)--(8.10). -/
theorem combine_equations_8_7_to_8_10
    {C gaugeW innerAbs normW normL volProjOmega volProjB volB V c82 c83 : ℝ}
    (hgaugeW : 0 < gaugeW)
    (hvolB : 0 ≤ volB)
    (hnormW : 0 ≤ normW) (hnormL : 0 ≤ normL)
    (hc83 : 0 ≤ c83)
    (h87 : 2 * C * gaugeW ≤ innerAbs)
    (h88 : normW * volProjOmega ≤ c82 * gaugeW * V)
    (h89 : volProjB ≤ c83 * volProjOmega)
    (h810 : innerAbs * volB ≤ normW * normL * volProjB) :
    2 * C * volB ≤ c82 * c83 * normL * V := by
  have h87' : (2 * C * gaugeW) * volB ≤ innerAbs * volB :=
    mul_le_mul_of_nonneg_right h87 hvolB
  have h89' : normW * normL * volProjB ≤
      normW * normL * (c83 * volProjOmega) :=
    mul_le_mul_of_nonneg_left h89 (mul_nonneg hnormW hnormL)
  have h88' : (normL * c83) * (normW * volProjOmega) ≤
      (normL * c83) * (c82 * gaugeW * V) :=
    mul_le_mul_of_nonneg_left h88 (mul_nonneg hnormL hc83)
  have hproduct : gaugeW * (2 * C * volB) ≤
      gaugeW * (c82 * c83 * normL * V) := by
    calc
      gaugeW * (2 * C * volB) = (2 * C * gaugeW) * volB := by ring
      _ ≤ innerAbs * volB := h87'
      _ ≤ normW * normL * volProjB := h810
      _ ≤ normW * normL * (c83 * volProjOmega) := h89'
      _ = (normL * c83) * (normW * volProjOmega) := by ring
      _ ≤ (normL * c83) * (c82 * gaugeW * V) := h88'
      _ = gaugeW * (c82 * c83 * normL * V) := by ring
  exact le_of_mul_le_mul_left hproduct hgaugeW

/-- `ℝ≥0∞` version of `combine_equations_8_7_to_8_10`, matching the
measure-valued outputs of the geometric lemmas. -/
theorem combine_equations_8_7_to_8_10_ennreal
    {C gaugeW innerAbs normW normL volProjOmega volProjB volB V c82 c83 : ENNReal}
    (hgaugeW0 : gaugeW ≠ 0) (hgaugeWtop : gaugeW ≠ ⊤)
    (h87 : 2 * C * gaugeW ≤ innerAbs)
    (h88 : normW * volProjOmega ≤ c82 * gaugeW * V)
    (h89 : volProjB ≤ c83 * volProjOmega)
    (h810 : innerAbs * volB ≤ normW * normL * volProjB) :
    2 * C * volB ≤ c82 * c83 * normL * V := by
  have h87' : (2 * C * gaugeW) * volB ≤ innerAbs * volB := by
    gcongr
  have h89' : normW * normL * volProjB ≤
      normW * normL * (c83 * volProjOmega) := by
    gcongr
  have h88' : (normL * c83) * (normW * volProjOmega) ≤
      (normL * c83) * (c82 * gaugeW * V) := by
    gcongr
  have hproduct : (2 * C * volB) * gaugeW ≤
      (c82 * c83 * normL * V) * gaugeW := by
    calc
      (2 * C * volB) * gaugeW = (2 * C * gaugeW) * volB := by ac_rfl
      _ ≤ innerAbs * volB := h87'
      _ ≤ normW * normL * volProjB := h810
      _ ≤ normW * normL * (c83 * volProjOmega) := h89'
      _ = (normL * c83) * (normW * volProjOmega) := by ac_rfl
      _ ≤ (normL * c83) * (c82 * gaugeW * V) := h88'
      _ = (c82 * c83 * normL * V) * gaugeW := by ac_rfl
  exact (ENNReal.mul_le_mul_iff_left hgaugeW0 hgaugeWtop).mp hproduct

end Erdos186.CFP.Bilu.Section8Case2

#print axioms Erdos186.CFP.Bilu.Section8Case2.combine_equations_8_7_to_8_10
#print axioms Erdos186.CFP.Bilu.Section8Case2.combine_equations_8_7_to_8_10_ennreal
