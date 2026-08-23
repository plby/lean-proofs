/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos721.NestedDensityStep

/-!
# Constructing the three nested Bohr scales

The structural density step uses three regular scales.  They are all
dilates (up to the doubling automorphism) of the current Bohr set, and hence
have exactly the current rank.  This file constructs those scales and proves
all inclusions required by `CyclicNestedDensityStep.exists_increment_or_terminal`.
-/

namespace Erdos721

open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ENNReal Indicator mu NNReal Pointwise

namespace CyclicNestedScaleConstruction

variable {N : ℕ} [NeZero N]

private lemma dilate_dilate_of_nonneg (B : CyclicBohr.Set N)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (B.dilate a).dilate b = B.dilate (a * b) := by
  cases B with
  | mk frequencies radius radius_nonneg =>
      simp [CyclicBohr.Set.dilate, abs_of_nonneg ha, abs_of_nonneg hb,
        abs_of_nonneg (mul_nonneg ha hb), mul_assoc]
      ring

private lemma nested_dilate_subset (B : CyclicBohr.Set N)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (habc : a * b ≤ c) :
    ((B.dilate a).dilate b).carrier ⊆ (B.dilate c).carrier := by
  rw [dilate_dilate_of_nonneg B ha hb]
  exact CyclicBohr.Set.dilate_mono B (mul_nonneg ha hb) habc

/-- Doubling a small dilate of a dilate stays in twice the corresponding
scale of the original Bohr set. -/
private lemma double_nested_dilate_subset
    (hN : Odd N) (B : CyclicBohr.Set N)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdouble : 2 * (a * b) ≤ c) :
    ((CyclicTwoScaleLifting.doubleBohr hN (B.dilate a)).dilate b).carrier ⊆
      (B.dilate c).carrier := by
  intro x hx
  rw [← CyclicTwoScaleLifting.doubleBohr_dilate,
    CyclicTwoScaleLifting.carrier_doubleBohr, Finset.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' : y ∈ B.dilate (a * b) := by
    rw [← dilate_dilate_of_nonneg B ha hb]
    exact hy
  have hadd := CyclicBohr.Set.add_mem_dilate
    (B := B) (mul_nonneg ha hb) (mul_nonneg ha hb) hy' hy'
  have hsum : a * b + a * b ≤ c := by nlinarith
  have hmono := CyclicBohr.Set.dilate_mono B
    (add_nonneg (mul_nonneg ha hb) (mul_nonneg ha hb)) hsum
  apply hmono
  rw [CyclicTwoScaleLifting.doubleEquiv_apply]
  rw [two_nsmul]
  exact hadd

/-- The canonical three-scale choice.  All ranks are unchanged, while each
successive base radius loses only its displayed explicit factor. -/
theorem exists_canonical_scales
    (hN : Odd N) (m : ℕ) (hm : 0 < m)
    (s : CyclicNestedDensityStep.State N m) :
    ∃ (J K H R : CyclicBohr.Set N)
        (tj dj tk dk u zeta vr eta : ℝ),
      J = s.B.dilate (s.delta / 4) ∧
      K = J.dilate (dj / 8) ∧
      H = (CyclicTwoScaleLifting.doubleBohr hN K).dilate (dk / 16) ∧
      R = H.dilate (zeta / 4) ∧
      0 < J.radius ∧ J.rank = s.B.rank ∧
      1 / 2 ≤ tj ∧ tj ≤ 1 ∧
      dj = (400 * (m : ℝ) * (J.rank : ℝ))⁻¹ ∧
      0 < dj ∧ dj < tj ∧
      (10 * m) * (J.dilate (tj + dj)).carrier.card ≤
        (10 * m + 1) * (J.dilate (tj - dj)).carrier.card ∧
      0 < K.radius ∧ K.rank = J.rank ∧
      1 / 2 ≤ tk ∧ tk ≤ 1 ∧
      dk = (400 * (m : ℝ) * (K.rank : ℝ))⁻¹ ∧
      0 < dk ∧ dk < tk ∧
      (10 * m) * (K.dilate (tk + dk)).carrier.card ≤
        (10 * m + 1) * (K.dilate (tk - dk)).carrier.card ∧
      0 < H.radius ∧ H.rank = K.rank ∧
      1 / 2 ≤ u ∧ u ≤ 1 ∧
      zeta = (400 * (H.rank : ℝ))⁻¹ ∧
      0 < zeta ∧ zeta < u ∧
      10 * (H.dilate (u + zeta)).carrier.card ≤
        11 * (H.dilate (u - zeta)).carrier.card ∧
      0 < R.radius ∧ R.rank = H.rank ∧
      1 / 2 ≤ vr ∧ vr ≤ 1 ∧
      eta = (400 * (R.rank : ℝ))⁻¹ ∧
      0 < eta ∧ eta < vr ∧
      10 * (R.dilate (vr + eta)).carrier.card ≤
        11 * (R.dilate (vr - eta)).carrier.card ∧
      (K.dilate (tk - dk)).carrier ⊆ (J.dilate tj).carrier ∧
      (J.dilate tj).carrier ⊆ (s.B.dilate s.delta).carrier ∧
      ((CyclicTwoScaleLifting.doubleBohr hN K).dilate
        (tk - dk)).carrier ⊆ (J.dilate dj).carrier ∧
      (H.dilate (u - zeta)).carrier ⊆
        ((CyclicTwoScaleLifting.doubleBohr hN K).dilate (dk / 4)).carrier ∧
      (H.dilate (u - zeta)).carrier ⊆ (J.dilate (dj / 4)).carrier ∧
      (H.dilate zeta).carrier ⊆ (J.dilate (dj / 4)).carrier ∧
      (H.dilate zeta).carrier ⊆
        ((CyclicTwoScaleLifting.doubleBohr hN K).dilate (dk / 4)).carrier ∧
      (R.dilate (vr - eta)).carrier ⊆ (J.dilate (dj / 4)).carrier ∧
      (R.dilate (vr - eta)).carrier ⊆
        ((CyclicTwoScaleLifting.doubleBohr hN K).dilate (dk / 4)).carrier ∧
      (R.dilate (vr - eta)).carrier ⊆ (H.dilate zeta).carrier ∧
      (R.dilate eta).carrier ⊆ (J.dilate (dj / 4)).carrier := by
  let J := s.B.dilate (s.delta / 4)
  have hJradius : 0 < J.radius := by
    simp only [J, CyclicBohr.Set.radius_dilate]
    rw [abs_of_pos (div_pos s.delta_pos (by norm_num))]
    exact mul_pos (div_pos s.delta_pos (by norm_num)) s.radius_pos
  have hJrank : 0 < J.rank := by simpa [J] using s.rank_pos
  obtain ⟨tj, dj, htj0, htj1, hdjFormula, hdj, hdjtj, hJregular⟩ :=
    CyclicBohr.exists_fixed_regular_scale_fine J m hJradius hJrank hm
  let K := J.dilate (dj / 8)
  have hKradius : 0 < K.radius := by
    simp only [K, CyclicBohr.Set.radius_dilate]
    positivity
  have hKrank : 0 < K.rank := by simpa [K] using hJrank
  obtain ⟨tk, dk, htk0, htk1, hdkFormula, hdk, hdktk, hKregular⟩ :=
    CyclicBohr.exists_fixed_regular_scale_fine K m hKradius hKrank hm
  let H := (CyclicTwoScaleLifting.doubleBohr hN K).dilate (dk / 16)
  have hHradius : 0 < H.radius := by
    simp only [H, CyclicBohr.Set.radius_dilate,
      CyclicTwoScaleLifting.doubleBohr_radius]
    positivity
  have hHrank : 0 < H.rank := by
    simpa [H] using hKrank
  obtain ⟨u, zeta, hu0, hu1, hzetaFormula, hzeta, hzetau, hHregular⟩ :=
    CyclicBohr.exists_fixed_regular_scale_quantitative H hHradius hHrank
  let R := H.dilate (zeta / 4)
  have hRradius : 0 < R.radius := by
    simp only [R, CyclicBohr.Set.radius_dilate]
    positivity
  have hRrank : 0 < R.rank := by simpa [R] using hHrank
  obtain ⟨vr, eta, hvr0, hvr1, hetaFormula, heta, hetavr, hRregular⟩ :=
    CyclicBohr.exists_fixed_regular_scale_quantitative R hRradius hRrank
  have htkdk0 : 0 ≤ tk - dk := sub_nonneg.mpr hdktk.le
  have hudiff0 : 0 ≤ u - zeta := sub_nonneg.mpr hzetau.le
  have hQJ : (K.dilate (tk - dk)).carrier ⊆ (J.dilate tj).carrier := by
    apply nested_dilate_subset J (by positivity) htkdk0
    have : tk - dk ≤ 1 := by linarith
    nlinarith [htj0]
  have hJB : (J.dilate tj).carrier ⊆
      (s.B.dilate s.delta).carrier := by
    apply nested_dilate_subset s.B
      (div_nonneg s.delta_pos.le (by norm_num))
      (by linarith [htj0])
    nlinarith [htj1, s.delta_pos]
  have hdoubleK :
      ((CyclicTwoScaleLifting.doubleBohr hN K).dilate
        (tk - dk)).carrier ⊆ (J.dilate dj).carrier := by
    apply double_nested_dilate_subset hN J (by positivity) htkdk0
    have : tk - dk ≤ 1 := by linarith
    nlinarith [hdj]
  have hHinnerOuter : (H.dilate (u - zeta)).carrier ⊆
      ((CyclicTwoScaleLifting.doubleBohr hN K).dilate (dk / 4)).carrier := by
    apply nested_dilate_subset (CyclicTwoScaleLifting.doubleBohr hN K)
      (by positivity) hudiff0
    have : u - zeta ≤ 1 := by linarith
    nlinarith [hdk]
  have hHsmallInner : (H.dilate zeta).carrier ⊆
      ((CyclicTwoScaleLifting.doubleBohr hN K).dilate (dk / 4)).carrier := by
    apply nested_dilate_subset (CyclicTwoScaleLifting.doubleBohr hN K)
      (by positivity) hzeta.le
    have : zeta ≤ 1 := by linarith [hu1]
    nlinarith [hdk]
  have hdoubleBase :
      ((CyclicTwoScaleLifting.doubleBohr hN K).dilate (dk / 4)).carrier ⊆
        (J.dilate (dj / 4)).carrier := by
    apply double_nested_dilate_subset hN J (by positivity) (by positivity)
    have hdk1 : dk ≤ 1 := by linarith [htk1]
    nlinarith [hdj]
  have hRinnerH : (R.dilate (vr - eta)).carrier ⊆
      (H.dilate zeta).carrier := by
    apply nested_dilate_subset H
      (div_nonneg hzeta.le (by norm_num))
      (sub_nonneg.mpr hetavr.le)
    have hdiff : vr - eta ≤ 1 := by linarith
    nlinarith [hzeta]
  have hRsmallH : (R.dilate eta).carrier ⊆
      (H.dilate zeta).carrier := by
    apply nested_dilate_subset H
      (div_nonneg hzeta.le (by norm_num)) heta.le
    have heta1 : eta ≤ 1 := hetavr.le.trans hvr1
    nlinarith [hzeta]
  refine ⟨J, K, H, R, tj, dj, tk, dk, u, zeta, vr, eta,
    rfl, rfl, rfl, rfl,
    hJradius, ?_, htj0, htj1, hdjFormula, hdj, hdjtj, hJregular,
    hKradius, ?_, htk0, htk1, hdkFormula, hdk, hdktk, hKregular,
    hHradius, ?_, hu0, hu1, hzetaFormula, hzeta, hzetau, hHregular,
    hRradius, ?_, hvr0, hvr1, hetaFormula, heta, hetavr, hRregular,
    hQJ, hJB, hdoubleK, hHinnerOuter,
    hHinnerOuter.trans hdoubleBase, hHsmallInner.trans hdoubleBase,
    hHsmallInner, hRinnerH.trans (hHsmallInner.trans hdoubleBase),
    hRinnerH.trans hHsmallInner, hRinnerH,
    hRsmallH.trans (hHsmallInner.trans hdoubleBase)⟩
  · simp [J]
  · simp [K]
  · simp [H]
  · simp [R]

/-- The structural density step with its nested scales constructed
canonically. -/
theorem exists_increment_or_terminal
    (hN : Odd N) (m : ℕ) (hm : 8192 ≤ m)
    (s : CyclicNestedDensityStep.State N m)
    (herror :
      3 * (1 / ((5 * m : ℕ) * ((1 - 1 / 8192 : ℝ) * s.beta))) ≤
        (1 / 16 : ℝ) / 4) :
    (∃ s' : CyclicNestedDensityStep.State N m,
      CyclicNestedDensityStep.IncrementOutcome s s') ∨
    ∃ st : CyclicNestedDensityStep.State N m,
      CyclicNestedDensityStep.TerminalOutcome s st := by
  have hm0 : 0 < m := by omega
  obtain ⟨J, K, H, R, tj, dj, tk, dk, u, zeta, vr, eta,
      hJdef, hKdef, hHdef, hRdef, hJradius, hJrankEq, htj0, htj1, hdjFormula,
      hdj, hdjtj, hJregular, hKradius, hKrankEq, htk0, htk1,
      hdkFormula, hdk, hdktk, hKregular, hHradius, hHrankEq,
      hu0, hu1, hzetaFormula, hzeta, hzetau, hHregular,
      hRradius, hRrankEq, hvr0, hvr1, hetaFormula, heta, hetavr,
      hRregular,
      hTestOuter, hOuterSmall, hDoubleTestStable, hWeightInner,
      hWeightOuter, hHsmall, hHsmallInner, hRinnerOuter, hRinnerInner,
      hRinnerH, hRsmall⟩ :=
    exists_canonical_scales hN m hm0 s
  have hJrank : 0 < J.rank := by rw [hJrankEq]; exact s.rank_pos
  have hKrank : 0 < K.rank := by rw [hKrankEq, hJrankEq]; exact s.rank_pos
  have hHrank : 0 < H.rank := by
    rw [hHrankEq, hKrankEq, hJrankEq]
    exact s.rank_pos
  have hRrank : 0 < R.rank := by rw [hRrankEq]; exact hHrank
  have hKrankState : K.rank = s.B.rank := by
    rw [hKrankEq, hJrankEq]
  have hRrankState : R.rank = s.B.rank := by
    rw [hRrankEq, hHrankEq, hKrankEq, hJrankEq]
  obtain ⟨hReferenceRadius, hFloorJ, hFloorK⟩ :=
    CyclicNestedDensityStep.State.canonical_radius_data hN s J K H R
      hJdef hKdef hHdef hRdef hdj (hdjtj.le.trans htj1)
      hdk (hdktk.le.trans htk1) hzeta (hzetau.le.trans hu1)
      heta (hetavr.le.trans hvr1) hdjFormula hdkFormula hzetaFormula
      hetaFormula hJrankEq hKrankState hRrankState
  exact CyclicNestedDensityStep.exists_increment_or_terminal
    hN m hm s J K H R hJradius hJrank htj0 htj1 hdj hdjtj hdjFormula
    hJregular hKradius hKrank htk0 htk1 hdk hdktk hdkFormula hKregular
    hHradius hHrank
    hu0 hu1 hzeta hzetau hHregular hRradius hRrank hvr0 hvr1 heta
    hetavr hRregular hJrankEq hKrankState hRrankState hReferenceRadius
    hFloorJ hFloorK hTestOuter hOuterSmall
    hDoubleTestStable hWeightInner hWeightOuter hHsmall hHsmallInner
    hRinnerOuter hRinnerInner hRinnerH hRsmall herror

end CyclicNestedScaleConstruction
end Erdos721
