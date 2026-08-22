/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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

import Mathlib

/-!
# Second-moment inequalities for Erdős Problem 1165

This file supplies the measure-theoretic and finite forms of the
Paley--Zygmund (second-moment) argument used at the end of Appendix A in
Hao--Li--Okada--Zheng.  It also records exact first- and second-moment
expansions for a finite sum of event indicators.  Thus estimates for the
one-point and two-point probabilities can be inserted without any hidden
probabilistic step.

The division-free inequalities are the primary statements.  They remain
valid when the second moment is zero; ratio forms are derived under the
mathematically necessary positivity hypothesis.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.SecondMoment

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Indicators and finite counts -/

variable {Omega ι : Type*}

/-- The real-valued indicator of an event. -/
def eventIndicator (A : Set Omega) (omega : Omega) : ℝ :=
  if omega ∈ A then 1 else 0

@[simp] lemma eventIndicator_apply (A : Set Omega) (omega : Omega) :
    eventIndicator A omega = if omega ∈ A then 1 else 0 := rfl

@[simp] lemma eventIndicator_of_mem {A : Set Omega} {omega : Omega} (h : omega ∈ A) :
    eventIndicator A omega = 1 := by simp [eventIndicator, h]

@[simp] lemma eventIndicator_of_not_mem {A : Set Omega} {omega : Omega} (h : omega ∉ A) :
    eventIndicator A omega = 0 := by simp [eventIndicator, h]

lemma eventIndicator_nonneg (A : Set Omega) (omega : Omega) :
    0 ≤ eventIndicator A omega := by
  by_cases h : omega ∈ A <;> simp [eventIndicator, h]

@[simp] lemma eventIndicator_mul (A B : Set Omega) (omega : Omega) :
    eventIndicator A omega * eventIndicator B omega = eventIndicator (A ∩ B) omega := by
  by_cases hA : omega ∈ A <;> by_cases hB : omega ∈ B <;>
    simp [eventIndicator, hA, hB]

@[simp] lemma eventIndicator_sq (A : Set Omega) (omega : Omega) :
    eventIndicator A omega ^ 2 = eventIndicator A omega := by
  by_cases hA : omega ∈ A <;> simp [eventIndicator, hA]

lemma measurable_eventIndicator [MeasurableSpace Omega] {A : Set Omega}
    (hA : MeasurableSet A) :
    Measurable (eventIndicator A) := by
  exact Measurable.ite hA measurable_const measurable_const

/-- The number of events in a finite family which occur, represented as a real number. -/
def indicatorCount (I : Finset ι) (A : ι → Set Omega) (omega : Omega) : ℝ :=
  ∑ i ∈ I, eventIndicator (A i) omega

lemma indicatorCount_nonneg (I : Finset ι) (A : ι → Set Omega) (omega : Omega) :
    0 ≤ indicatorCount I A omega := by
  exact Finset.sum_nonneg fun i hi => eventIndicator_nonneg (A i) omega

lemma measurable_indicatorCount [MeasurableSpace Omega]
    (I : Finset ι) (A : ι → Set Omega)
    (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    Measurable (indicatorCount I A) := by
  classical
  unfold indicatorCount
  exact Finset.measurable_sum _ fun i hi => measurable_eventIndicator (hA i hi)

lemma indicatorCount_eq_card_filter (I : Finset ι) (A : ι → Set Omega) (omega : Omega) :
    indicatorCount I A omega = ((I.filter fun i => omega ∈ A i).card : ℝ) := by
  classical
  simp [indicatorCount, eventIndicator]

lemma one_le_indicatorCount_iff (I : Finset ι) (A : ι → Set Omega) (omega : Omega) :
    1 ≤ indicatorCount I A omega ↔ ∃ i ∈ I, omega ∈ A i := by
  classical
  rw [indicatorCount_eq_card_filter]
  norm_num
  exact Finset.filter_nonempty_iff

lemma indicatorCount_pos_iff (I : Finset ι) (A : ι → Set Omega) (omega : Omega) :
    0 < indicatorCount I A omega ↔ ∃ i ∈ I, omega ∈ A i := by
  rw [← one_le_indicatorCount_iff I A omega]
  rw [indicatorCount_eq_card_filter]
  norm_num

lemma indicatorCount_sq_expand (I : Finset ι) (A : ι → Set Omega) (omega : Omega) :
    indicatorCount I A omega ^ 2 =
      ∑ i ∈ I, ∑ j ∈ I, eventIndicator (A i ∩ A j) omega := by
  classical
  simp only [indicatorCount, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simpa [mul_comm] using eventIndicator_mul (A i) (A j) omega

/-! ## Exact indicator moment expansions -/

variable [MeasurableSpace Omega] {mu : Measure Omega}

lemma integral_eventIndicator [IsFiniteMeasure mu] {A : Set Omega}
    (hA : MeasurableSet A) :
    ∫ omega, eventIndicator A omega ∂mu = mu.real A := by
  change ∫ omega, A.indicator (fun _ => (1 : ℝ)) omega ∂mu = mu.real A
  rw [integral_indicator hA]
  simp

lemma integrable_indicatorCount [IsFiniteMeasure mu]
    (I : Finset ι) (A : ι → Set Omega) (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    Integrable (indicatorCount I A) mu := by
  apply integrable_finsetSum I
  intro i hi
  apply Integrable.of_bound (measurable_eventIndicator (hA i hi)).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun omega => by
    by_cases h : omega ∈ A i <;> simp [eventIndicator, h]

lemma integral_indicatorCount [IsFiniteMeasure mu]
    (I : Finset ι) (A : ι → Set Omega) (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    ∫ omega, indicatorCount I A omega ∂mu =
      ∑ i ∈ I, mu.real (A i) := by
  classical
  simp only [indicatorCount]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact integral_eventIndicator (hA i hi)
  · intro i hi
    apply Integrable.of_bound (measurable_eventIndicator (hA i hi)).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun omega => by
      by_cases h : omega ∈ A i <;> simp [eventIndicator, h]

lemma integrable_indicatorCount_sq [IsFiniteMeasure mu]
    (I : Finset ι) (A : ι → Set Omega) (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    Integrable (fun omega => indicatorCount I A omega ^ 2) mu := by
  rw [show (fun omega => indicatorCount I A omega ^ 2) =
      (fun omega => indicatorCount I A omega * indicatorCount I A omega) by
    funext omega
    rw [pow_two]]
  refine Integrable.of_bound (C := (I.card : ℝ) ^ 2) ?_ ?_
  · exact ((measurable_indicatorCount I A hA).mul
      (measurable_indicatorCount I A hA)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun omega => by
      rw [← pow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (indicatorCount_nonneg I A omega)
        (by
          rw [indicatorCount_eq_card_filter]
          exact_mod_cast Finset.card_filter_le I _) 2

lemma integral_indicatorCount_sq [IsFiniteMeasure mu]
    (I : Finset ι) (A : ι → Set Omega) (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    ∫ omega, indicatorCount I A omega ^ 2 ∂mu =
      ∑ i ∈ I, ∑ j ∈ I, mu.real (A i ∩ A j) := by
  classical
  simp_rw [indicatorCount_sq_expand]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      exact integral_eventIndicator ((hA i hi).inter (hA j hj))
    · intro j hj
      apply Integrable.of_bound
        (measurable_eventIndicator ((hA i hi).inter (hA j hj))).aestronglyMeasurable 1
      exact Filter.Eventually.of_forall fun omega => by
        by_cases h : omega ∈ A i ∩ A j <;> simp [eventIndicator, h]
  · intro i hi
    apply integrable_finsetSum I
    intro j hj
    apply Integrable.of_bound
      (measurable_eventIndicator ((hA i hi).inter (hA j hj))).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun omega => by
      by_cases h : omega ∈ A i ∩ A j <;> simp [eventIndicator, h]

omit [MeasurableSpace Omega] in
lemma indicatorCount_positive_set (I : Finset ι) (A : ι → Set Omega) :
    {omega | 0 < indicatorCount I A omega} = ⋃ i ∈ I, A i := by
  classical
  ext omega
  simp [indicatorCount_pos_iff]

omit [MeasurableSpace Omega] in
lemma indicatorCount_one_le_set (I : Finset ι) (A : ι → Set Omega) :
    {omega | 1 ≤ indicatorCount I A omega} = ⋃ i ∈ I, A i := by
  classical
  ext omega
  simp [one_le_indicatorCount_iff]

/-! ## Finite second-moment inequalities -/

lemma finite_secondMoment_mul (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) :
    (∑ i ∈ S, f i) ^ 2 ≤
      ((S.filter fun i => 0 < f i).card : ℝ) * ∑ i ∈ S, f i ^ 2 := by
  classical
  let g : ι → ℝ := fun i => if 0 < f i then 1 else 0
  have hfg : ∀ i ∈ S, f i * g i = f i := by
    intro i hi
    by_cases hpos : 0 < f i
    · simp [g, hpos]
    · have hz : f i = 0 := le_antisymm (not_lt.mp hpos) (hf i hi)
      simp [g, hz]
  have hg : ∑ i ∈ S, g i ^ 2 = ((S.filter fun i => 0 < f i).card : ℝ) := by
    simp [g]
  have hsum : ∑ i ∈ S, f i * g i = ∑ i ∈ S, f i :=
    Finset.sum_congr rfl hfg
  calc
    (∑ i ∈ S, f i) ^ 2 = (∑ i ∈ S, f i * g i) ^ 2 := by rw [hsum]
    _ ≤ (∑ i ∈ S, f i ^ 2) * ∑ i ∈ S, g i ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq S f g
    _ = ((S.filter fun i => 0 < f i).card : ℝ) * ∑ i ∈ S, f i ^ 2 := by
      rw [hg, mul_comm]

lemma finite_secondMoment_ratio (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) (hsecond : 0 < ∑ i ∈ S, f i ^ 2) :
    (∑ i ∈ S, f i) ^ 2 / (∑ i ∈ S, f i ^ 2) ≤
      ((S.filter fun i => 0 < f i).card : ℝ) := by
  rw [div_le_iff₀ hsecond]
  simpa [mul_comm] using finite_secondMoment_mul S f hf

/-! ## Integral Cauchy--Schwarz and Paley--Zygmund -/

/-- Squared Cauchy--Schwarz for real Bochner integrals. -/
lemma integral_mul_sq_le_integral_sq_mul_integral_sq
    (f g : Omega → ℝ)
    (hf : Integrable (fun omega => f omega ^ 2) mu)
    (hg : Integrable (fun omega => g omega ^ 2) mu)
    (hfg : Integrable (fun omega => f omega * g omega) mu) :
    (∫ omega, f omega * g omega ∂mu) ^ 2 ≤
      (∫ omega, f omega ^ 2 ∂mu) * (∫ omega, g omega ^ 2 ∂mu) := by
  have h_cauchy_schwarz :
      0 ≤ ∫ omega,
        (f omega -
          (∫ omega, f omega * g omega ∂mu) /
            (∫ omega, g omega ^ 2 ∂mu) * g omega) ^ 2 ∂mu :=
    integral_nonneg fun _ => sq_nonneg _
  by_cases h : ∫ omega, g omega ^ 2 ∂mu = 0 <;>
      simp only [h, sub_sq, mul_pow] at h_cauchy_schwarz ⊢
  · rw [integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)] at h
    · have hgzero : g =ᵐ[mu] 0 := h.mono fun omega homega => by
        simp only [Pi.zero_apply]
        exact sq_eq_zero_iff.mp (by simpa using homega)
      have hfgzero : ∫ omega, f omega * g omega ∂mu = 0 := by
        apply integral_eq_zero_of_ae
        exact hgzero.mono fun omega homega => by simp [homega]
      simp [hfgzero]
    · exact hg
  · rw [integral_add, integral_sub] at h_cauchy_schwarz
    · simp only [div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm,
        integral_mul_const] at h_cauchy_schwarz ⊢
      simp only [← mul_assoc, integral_mul_const] at h_cauchy_schwarz ⊢
      have hfn : 0 ≤ ∫ omega, f omega ^ 2 ∂mu :=
        integral_nonneg fun omega => sq_nonneg (f omega)
      have hgn : 0 ≤ ∫ omega, g omega ^ 2 ∂mu :=
        integral_nonneg fun omega => sq_nonneg (g omega)
      nlinarith [inv_mul_cancel_left₀ h (∫ omega, f omega * g omega ∂mu),
        inv_mul_cancel₀ h]
    · exact hf
    · convert hfg.mul_const
        (2 * ((∫ omega, f omega * g omega ∂mu) /
          (∫ omega, g omega ^ 2 ∂mu))) using 2
      all_goals ring
    · refine Integrable.sub hf ?_
      convert hfg.mul_const
        (2 * ((∫ omega, f omega * g omega ∂mu) /
          (∫ omega, g omega ^ 2 ∂mu))) using 2
      all_goals ring
    · exact hg.const_mul _

/-- Division-free second-moment inequality.  For a nonnegative random
variable, the square of its first moment is bounded by its second moment
times the measure of its positive support. -/
theorem integral_secondMoment_mul [IsFiniteMeasure mu]
    (Z : Omega → ℝ) (hZ : 0 ≤ Z)
    (hZmeas : Measurable Z) (hZint : Integrable Z mu)
    (hZ2 : Integrable (fun omega => Z omega ^ 2) mu) :
    (∫ omega, Z omega ∂mu) ^ 2 ≤
      (∫ omega, Z omega ^ 2 ∂mu) * mu.real {omega | 0 < Z omega} := by
  let support : Set Omega := {omega | 0 < Z omega}
  let oneSupport : Omega → ℝ := eventIndicator support
  have hsupport : MeasurableSet support :=
    measurableSet_lt measurable_const hZmeas
  have hone : Integrable oneSupport mu := by
    apply Integrable.of_bound
      (measurable_eventIndicator hsupport).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun omega => by
      by_cases h : omega ∈ support <;> simp [eventIndicator, h]
  have hone2 : Integrable (fun omega => oneSupport omega ^ 2) mu :=
    hone.congr (Filter.Eventually.of_forall fun omega => by
      exact (eventIndicator_sq support omega).symm)
  have hprod : Integrable (fun omega => Z omega * oneSupport omega) mu :=
    hZint.mul_bdd (c := 1) (measurable_eventIndicator hsupport).aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => by
        by_cases h : omega ∈ support <;> simp [oneSupport, h])
  have hmul := integral_mul_sq_le_integral_sq_mul_integral_sq
    Z oneSupport hZ2 hone2 hprod
  have hfirst : (∫ omega, Z omega * oneSupport omega ∂mu) = ∫ omega, Z omega ∂mu := by
    apply integral_congr_ae
    filter_upwards with omega
    by_cases hpos : 0 < Z omega
    · simp [oneSupport, support, hpos]
    · have hz : Z omega = 0 := le_antisymm (not_lt.mp hpos) (hZ omega)
      simp [hz]
  have hsecond : (∫ omega, oneSupport omega ^ 2 ∂mu) = mu.real support := by
    calc
      (∫ omega, oneSupport omega ^ 2 ∂mu) = ∫ omega, oneSupport omega ∂mu := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun omega => eventIndicator_sq support omega
      _ = mu.real support := integral_eventIndicator hsupport
  simpa only [hfirst, hsecond, support] using hmul

/-- Ratio form of the second-moment method. -/
theorem integral_secondMoment_ratio [IsFiniteMeasure mu]
    (Z : Omega → ℝ) (hZ : 0 ≤ Z)
    (hZmeas : Measurable Z) (hZint : Integrable Z mu)
    (hZ2 : Integrable (fun omega => Z omega ^ 2) mu)
    (hsecond : 0 < ∫ omega, Z omega ^ 2 ∂mu) :
    (∫ omega, Z omega ∂mu) ^ 2 /
        (∫ omega, Z omega ^ 2 ∂mu) ≤
      mu.real {omega | 0 < Z omega} := by
  rw [div_le_iff₀ hsecond]
  simpa [mul_comm] using integral_secondMoment_mul Z hZ hZmeas hZint hZ2

/-- Paley--Zygmund in division-free form. -/
theorem paleyZygmund_mul [IsProbabilityMeasure mu]
    (Z : Omega → ℝ) (hZ : 0 ≤ Z)
    (hZmeas : Measurable Z) (hZint : Integrable Z mu)
    (hZ2 : Integrable (fun omega => Z omega ^ 2) mu)
    {theta : ℝ} (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    ((1 - theta) * ∫ omega, Z omega ∂mu) ^ 2 ≤
      (∫ omega, Z omega ^ 2 ∂mu) *
        mu.real {omega | theta * (∫ omega, Z omega ∂mu) ≤ Z omega} := by
  let mean : ℝ := ∫ omega, Z omega ∂mu
  let upper : Set Omega := {omega | theta * mean ≤ Z omega}
  let oneUpper : Omega → ℝ := eventIndicator upper
  have hupper : MeasurableSet upper :=
    measurableSet_le measurable_const hZmeas
  have hone : Integrable oneUpper mu := by
    apply Integrable.of_bound
      (measurable_eventIndicator hupper).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun omega => by
      by_cases h : omega ∈ upper <;> simp [eventIndicator, h]
  have hone2 : Integrable (fun omega => oneUpper omega ^ 2) mu :=
    hone.congr (Filter.Eventually.of_forall fun omega => by
      exact (eventIndicator_sq upper omega).symm)
  have hprod : Integrable (fun omega => Z omega * oneUpper omega) mu :=
    hZint.mul_bdd (c := 1) (measurable_eventIndicator hupper).aestronglyMeasurable
      (Filter.Eventually.of_forall fun omega => by
        by_cases h : omega ∈ upper <;> simp [oneUpper, h])
  have hmean_nonneg : 0 ≤ mean := integral_nonneg hZ
  have hlower : (1 - theta) * mean ≤
      ∫ omega, Z omega * oneUpper omega ∂mu := by
    have hsplit : mean =
        (∫ omega, Z omega * eventIndicator (upperᶜ) omega ∂mu) +
          ∫ omega, Z omega * oneUpper omega ∂mu := by
      rw [← integral_add]
      · exact congrArg (fun f : Omega → ℝ => ∫ omega, f omega ∂mu) (funext fun omega => by
          by_cases h : omega ∈ upper <;>
            simp [oneUpper, eventIndicator, h])
      · exact hZint.mul_bdd (c := 1)
          (measurable_eventIndicator hupper.compl).aestronglyMeasurable
          (Filter.Eventually.of_forall fun omega => by
            by_cases h : omega ∈ upperᶜ <;> simp [eventIndicator, h])
      · exact hprod
    have hcomplement :
        ∫ omega, Z omega * eventIndicator (upperᶜ) omega ∂mu ≤ theta * mean := by
      have hmono :
          (∫ omega, Z omega * eventIndicator (upperᶜ) omega ∂mu) ≤
            ∫ _ : Omega, theta * mean ∂mu := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun omega =>
            mul_nonneg (hZ omega) (eventIndicator_nonneg upperᶜ omega)
        · exact integrable_const _
        · filter_upwards with omega
          by_cases hmem : omega ∈ upper
          · simp [eventIndicator, hmem]
            exact mul_nonneg htheta0 hmean_nonneg
          · have hcomp : omega ∈ upperᶜ := hmem
            rw [eventIndicator_of_mem hcomp, mul_one]
            exact (lt_of_not_ge (by simpa [upper] using hmem)).le
      simpa using hmono
    calc
      (1 - theta) * mean = mean - theta * mean := by ring
      _ ≤ mean - (∫ omega, Z omega * eventIndicator (upperᶜ) omega ∂mu) :=
        sub_le_sub_left hcomplement mean
      _ = ∫ omega, Z omega * oneUpper omega ∂mu := by linarith only [hsplit]
  have hmul := integral_mul_sq_le_integral_sq_mul_integral_sq
    Z oneUpper hZ2 hone2 hprod
  have hlower_nonneg : 0 ≤ (1 - theta) * mean :=
    mul_nonneg (sub_nonneg.mpr htheta1) hmean_nonneg
  have hsq : ((1 - theta) * mean) ^ 2 ≤
      (∫ omega, Z omega * oneUpper omega ∂mu) ^ 2 := by
    exact (sq_le_sq₀ hlower_nonneg
      (integral_nonneg fun omega =>
        mul_nonneg (hZ omega) (eventIndicator_nonneg upper omega))).mpr hlower
  have hsecond : (∫ omega, oneUpper omega ^ 2 ∂mu) = mu.real upper := by
    calc
      (∫ omega, oneUpper omega ^ 2 ∂mu) = ∫ omega, oneUpper omega ∂mu := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun omega => eventIndicator_sq upper omega
      _ = mu.real upper := integral_eventIndicator hupper
  exact hsq.trans (by simpa only [hsecond, upper, mean] using hmul)

/-- Paley--Zygmund in ratio form. -/
theorem paleyZygmund_ratio [IsProbabilityMeasure mu]
    (Z : Omega → ℝ) (hZ : 0 ≤ Z)
    (hZmeas : Measurable Z) (hZint : Integrable Z mu)
    (hZ2 : Integrable (fun omega => Z omega ^ 2) mu)
    (hsecond : 0 < ∫ omega, Z omega ^ 2 ∂mu)
    {theta : ℝ} (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    ((1 - theta) * ∫ omega, Z omega ∂mu) ^ 2 /
        (∫ omega, Z omega ^ 2 ∂mu) ≤
      mu.real {omega | theta * (∫ omega, Z omega ∂mu) ≤ Z omega} := by
  rw [div_le_iff₀ hsecond]
  simpa [mul_comm] using
    paleyZygmund_mul Z hZ hZmeas hZint hZ2 htheta0 htheta1

/-! ## The exact Appendix-A indicator-count consequence -/

/-- The second-moment estimate for a finite sum of indicators, written
entirely in terms of one-point and pair probabilities. -/
theorem indicatorCount_secondMoment_bound [IsFiniteMeasure mu]
    (I : Finset ι) (A : ι → Set Omega) (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    (∑ i ∈ I, mu.real (A i)) ^ 2 ≤
      (∑ i ∈ I, ∑ j ∈ I, mu.real (A i ∩ A j)) *
        mu.real (⋃ i ∈ I, A i) := by
  have h := integral_secondMoment_mul (mu := mu) (indicatorCount I A)
    (indicatorCount_nonneg I A) (measurable_indicatorCount I A hA)
    (integrable_indicatorCount I A hA)
    (integrable_indicatorCount_sq I A hA)
  rwa [integral_indicatorCount I A hA, integral_indicatorCount_sq I A hA,
    indicatorCount_positive_set I A] at h

/-- Ratio form used after bounding the pair sum in the Appendix-A
second-moment computation. -/
theorem indicatorCount_secondMoment_ratio [IsFiniteMeasure mu]
    (I : Finset ι) (A : ι → Set Omega) (hA : ∀ i ∈ I, MeasurableSet (A i))
    (hpair : 0 < ∑ i ∈ I, ∑ j ∈ I, mu.real (A i ∩ A j)) :
    (∑ i ∈ I, mu.real (A i)) ^ 2 /
        (∑ i ∈ I, ∑ j ∈ I, mu.real (A i ∩ A j)) ≤
      mu.real (⋃ i ∈ I, A i) := by
  rw [div_le_iff₀ hpair]
  simpa [mul_comm] using indicatorCount_secondMoment_bound (mu := mu) I A hA

/-- The exact algebraic last step in the Appendix-A second-moment method.
If `L` is a lower bound for the one-point sum and `U` is an upper bound for
the pair sum, then `L² ≤ U` times the probability of at least one event. -/
theorem indicatorCount_union_lower_mul [IsFiniteMeasure mu]
    (I : Finset ι) (A : ι → Set Omega) (hA : ∀ i ∈ I, MeasurableSet (A i))
    {L U : ℝ} (hL : 0 ≤ L)
    (hfirst : L ≤ ∑ i ∈ I, mu.real (A i))
    (hsecond : (∑ i ∈ I, ∑ j ∈ I, mu.real (A i ∩ A j)) ≤ U) :
    L ^ 2 ≤ U * mu.real (⋃ i ∈ I, A i) := by
  calc
    L ^ 2 ≤ (∑ i ∈ I, mu.real (A i)) ^ 2 :=
      pow_le_pow_left₀ hL hfirst 2
    _ ≤ (∑ i ∈ I, ∑ j ∈ I, mu.real (A i ∩ A j)) *
        mu.real (⋃ i ∈ I, A i) :=
      indicatorCount_secondMoment_bound (mu := mu) I A hA
    _ ≤ U * mu.real (⋃ i ∈ I, A i) :=
      mul_le_mul_of_nonneg_right hsecond measureReal_nonneg

/-- Ratio version of `indicatorCount_union_lower_mul`, matching the usual
display of the second-moment method. -/
theorem indicatorCount_union_lower [IsFiniteMeasure mu]
    (I : Finset ι) (A : ι → Set Omega) (hA : ∀ i ∈ I, MeasurableSet (A i))
    {L U : ℝ} (hL : 0 ≤ L) (hU : 0 < U)
    (hfirst : L ≤ ∑ i ∈ I, mu.real (A i))
    (hsecond : (∑ i ∈ I, ∑ j ∈ I, mu.real (A i ∩ A j)) ≤ U) :
    L ^ 2 / U ≤ mu.real (⋃ i ∈ I, A i) := by
  rw [div_le_iff₀ hU]
  simpa [mul_comm] using
    indicatorCount_union_lower_mul (mu := mu) I A hA hL hfirst hsecond

end

end Erdos1165.SecondMoment
