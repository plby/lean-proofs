/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos636.AugmentationFull
import ErdosProblems.Erdos636.AugmentationGraphPartial

/-!
# Probability bookkeeping for the graph-valued full exposure

This file is the probability-only part of the graph full exposure.  It
turns the affine endpoint identity in `PartialExposureData`, per-item
probability estimates, and per-increment second-moment estimates into the
simultaneous full-exposure event.  The only aggregate hypothesis is the
explicit numerical risk budget `<= 1 / 6`; neither the endpoint event nor
the union of failures is left as an assumed probability bound.
-/

open Classical
open scoped BigOperators

namespace Erdos636
namespace AugmentationGraphFullProbability

open Erdos88.Concentration

universe u v

noncomputable section

/-! ## Finset half-slice concentration adapters -/

/-- The Boolean-slice linear statistic is the sum over the finset selected
by `boolSliceEquivFinsetLen`. -/
lemma sliceLinear_boolSliceEquivFinsetLen
    {I : Type u} [Fintype I] [DecidableEq I]
    (s : ℕ) (a : I → ℝ) (omega : Erdos88.Fourier.BoolSlice I s) :
    AntiConcentration.sliceLinear s a omega =
      HalfSample.sliceSum a
        (Erdos88.Fourier.boolSliceEquivFinsetLen I s omega) := by
  classical
  change (∑ i, a i * if omega.1 i then 1 else 0) =
    ∑ i ∈ SlicePersistence.sampleFinset s omega, a i
  calc
    (∑ i, a i * if omega.1 i then 1 else 0) =
        ∑ i, if i ∈ SlicePersistence.sampleFinset s omega then a i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hmem : i ∈ SlicePersistence.sampleFinset s omega
      · simp [hmem, SlicePersistence.mem_sampleFinset.mp hmem]
      · have hfalse : ¬ omega.1 i := by
          simpa only [SlicePersistence.mem_sampleFinset] using hmem
        simp [hmem, hfalse]
    _ = ∑ i ∈ SlicePersistence.sampleFinset s omega, a i := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext i
        simp
      · simp

/-- The direct selected-coordinate sum used by the partial-exposure module
has the same finset-half-slice decoding. -/
lemma graphPartialSliceSum_boolSliceEquivFinsetLen
    {I : Type u} [Fintype I] [DecidableEq I]
    (s : ℕ) (a : I → ℝ) (omega : Erdos88.Fourier.BoolSlice I s) :
    AugmentationGraphPartial.sliceSum s a omega =
      HalfSample.sliceSum a
        (Erdos88.Fourier.boolSliceEquivFinsetLen I s omega) := by
  rfl

/-- Bounded-difference concentration for a real coefficient sum on a
finset-valued uniform half-slice.  The centre is written as half of the
total coefficient sum, rather than as an abstract expectation. -/
theorem halfSlice_sum_two_sided_probability
    {I : Type u} [Fintype I] [DecidableEq I]
    {s : ℕ} (hcard : Fintype.card I = 2 * s) (hs : 0 < s)
    (a : I → ℝ) (B t : ℝ) (hB : 0 < B) (ht : 0 ≤ t)
    (hbounded : ∀ i, |a i| ≤ B) :
    uniformProbability (fun omega : HalfSample.Slice I s ↦
        t ≤ |HalfSample.sliceSum a omega - (∑ i, a i) / 2|) ≤
      2 * Real.exp (-t ^ 2 / (2 * s * (4 * B) ^ 2)) := by
  let : Nonempty (HalfSample.Slice I s) := HalfSample.sliceNonempty hcard
  let E : Erdos88.Fourier.BoolSlice I s ≃ HalfSample.Slice I s :=
    Erdos88.Fourier.boolSliceEquivFinsetLen I s
  let : Nonempty (Erdos88.Fourier.BoolSlice I s) :=
    (Equiv.nonempty_congr E).mpr inferInstance
  have hIpos : 0 < Fintype.card I := by omega
  let : Nonempty I := Fintype.card_pos_iff.mp hIpos
  have hsle : s ≤ Fintype.card I := by omega
  have htail := AugmentationGraphPartial.boolSlice_sum_two_sided_probability
    s hsle hs a B t hB ht hbounded
  have hmean : uniformExpectation
      (AugmentationGraphPartial.sliceSum s a) = (∑ i, a i) / 2 := by
    rw [AugmentationGraphPartial.uniformExpectation_sliceSum s hsle a]
    have hcardReal : (Fintype.card I : ℝ) = 2 * (s : ℝ) := by
      exact_mod_cast hcard
    rw [hcardReal]
    field_simp
  let P : HalfSample.Slice I s → Prop := fun omega ↦
    t ≤ |HalfSample.sliceSum a omega - (∑ i, a i) / 2|
  have hprob :
      uniformProbability
          (fun omega : Erdos88.Fourier.BoolSlice I s ↦ P (E omega)) =
        uniformProbability P :=
    SlicePersistence.uniformProbability_equiv E P
  rw [← hprob]
  have hevent :
      (fun omega : Erdos88.Fourier.BoolSlice I s ↦ P (E omega)) =
        (fun omega ↦ t ≤
          |AugmentationGraphPartial.sliceSum s a omega -
            uniformExpectation (AugmentationGraphPartial.sliceSum s a)|) := by
    funext omega
    simp only [P, E, graphPartialSliceSum_boolSliceEquivFinsetLen, hmean]
  rw [hevent]
  exact htail

/-- The integer `l1`/small-total anti-concentration estimate, transported
from Boolean functions to finset-valued slice points. -/
theorem halfSlice_point_probability_le_of_integer_l1_small_sum
    {I : Type u} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (mu c theta : ℝ) (B s : ℕ)
    (hs : s ≤ Fintype.card I)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2)
    (htheta : 0 < theta) (hB : 1 ≤ B) (hI : 0 < Fintype.card I)
    (hbounded : ∀ i, |a i| ≤ (B : ℤ))
    (hmean : (Fintype.card I : ℝ) * mu = ∑ i, (a i : ℝ))
    (hl1 : theta * Fintype.card I ≤ ∑ i, |(a i : ℝ)|)
    (hsmall : |∑ i, (a i : ℝ)| < theta / 2 * Fintype.card I)
    (hsel : c * Fintype.card I ≤ s)
    (hunsel : c * Fintype.card I ≤ Fintype.card I - s)
    (x : ℝ) :
    uniformProbability (fun omega : HalfSample.Slice I s ↦
        HalfSample.sliceSum (fun i ↦ (a i : ℝ)) omega = x) ≤
      AntiConcentration.variancePointMassConstant c (theta ^ 2 / 4) B /
        Real.sqrt (Fintype.card I : ℝ) := by
  let : Nonempty (HalfSample.Slice I s) := by
    obtain ⟨S, _hS, hScard⟩ :=
      Finset.exists_subset_card_eq
        (show s ≤ (Finset.univ : Finset I).card by simpa using hs)
    exact ⟨⟨S, hScard⟩⟩
  let E : Erdos88.Fourier.BoolSlice I s ≃ HalfSample.Slice I s :=
    Erdos88.Fourier.boolSliceEquivFinsetLen I s
  let : Nonempty (Erdos88.Fourier.BoolSlice I s) :=
    (Equiv.nonempty_congr E).mpr inferInstance
  have hanti :=
    AntiConcentration.slice_point_probability_le_of_integer_l1_small_sum
      a mu c theta B s hc0 hc1 htheta hB hI hbounded hmean hl1 hsmall
        hsel hunsel x
  let P : HalfSample.Slice I s → Prop := fun omega ↦
    HalfSample.sliceSum (fun i ↦ (a i : ℝ)) omega = x
  have hprob :
      uniformProbability
          (fun omega : Erdos88.Fourier.BoolSlice I s ↦ P (E omega)) =
        uniformProbability P :=
    SlicePersistence.uniformProbability_equiv E P
  rw [← hprob]
  simpa only [P, E, sliceLinear_boolSliceEquivFinsetLen,
    uniformProbability, Erdos88.Fourier.finProbability] using hanti

/-- The affine endpoint identity and the deterministic mean-rise inequality
give the half-probability endpoint event by complementation symmetry of a
uniform half-sample. -/
theorem one_half_le_endpointProbability
    {D : Type u} [Fintype D]
    {X : Type v} {s tau : ℕ}
    (hcard : Fintype.card D = 2 * s)
    (P : AugmentationFull.PartialExposureData D X s tau)
    (lam : ℝ)
    (hmeanRise : lam <=
      P.endpointOffset + (∑ d, P.endpointCoeff d) / 2) :
    (1 : ℝ) / 2 <= uniformProbability
      (fun omega : AugmentationFull.Sample D s =>
        lam <= P.path omega tau - P.path omega 0) := by
  let : Nonempty (AugmentationFull.Sample D s) :=
    HalfSample.sliceNonempty hcard
  have hhalf : (1 : ℝ) / 2 <=
      uniformProbability (fun omega : AugmentationFull.Sample D s =>
        (∑ d, P.endpointCoeff d) / 2 <=
          HalfSample.sliceSum P.endpointCoeff omega) := by
    simpa [HalfSample.sliceProbability, Erdos88.Fourier.finProbability,
      uniformProbability] using
        HalfSample.one_half_le_sliceProbability_ge_half_total
          hcard P.endpointCoeff
  refine hhalf.trans (uniformProbability_mono ?_)
  intro omega homega
  rw [P.endpointIdentity]
  linarith

/-- The disjunction of the four non-endpoint failures in the full exposure. -/
def failureEvent
    {D : Type u} [Fintype D]
    {X : Type v} [LinearOrder X] [DecidableEq X]
    {s tau : ℕ}
    (P : AugmentationFull.PartialExposureData D X s tau)
    (E rho kappa tGeom tCollision tDegree : ℝ)
    (omega : AugmentationFull.Sample D s) : Prop :=
  tGeom <= CollisionCounting.eventCount (Finset.range (tau + 1))
      P.geometricBad omega ∨
  tCollision <= CollisionCounting.eventCount (Finset.range (tau + 1))
      (AugmentationFull.collisionBad P E) omega ∨
  tDegree <= CollisionCounting.eventCount P.candidates P.degreeBad omega ∨
  kappa <= AugmentationFull.tailBudget P rho omega

/-- Per-item geometric, collision, and degree bounds together with the
per-increment second-moment estimate bound the probability of the complete
failure disjunction by the displayed sum of four risks. -/
theorem uniformProbability_failureEvent_le_itemRisk
    {D : Type u} [Fintype D] [DecidableEq D]
    {X : Type v} [LinearOrder X] [DecidableEq X]
    {s tau : ℕ}
    (hcard : Fintype.card D = 2 * s)
    (P : AugmentationFull.PartialExposureData D X s tau)
    (E v Q kappa tGeom tCollision tDegree : ℝ)
    (hv : 0 < v) (hQ : 0 < Q) (hkappa : 0 < kappa) (hE : 0 < E)
    (htGeom : 0 < tGeom) (htCollision : 0 < tCollision)
    (htDegree : 0 < tDegree)
    (pGeom pCollision pDegree : ℝ)
    (hgeom : ∀ i < tau + 1,
      uniformProbability (P.geometricBad i) <= pGeom)
    (hcollision : ∀ i < tau + 1,
      ∀ x ∈ P.candidates, ∀ y ∈ P.candidates, x ≠ y ->
        uniformProbability (fun omega =>
          P.value i x omega = P.value i y omega) <= pCollision)
    (hdegree : ∀ x ∈ P.candidates,
      uniformProbability (P.degreeBad x) <= pDegree)
    (hsecond : ∀ i < tau,
      uniformExpectation (fun omega : AugmentationFull.Sample D s =>
        (AugmentationFull.increment P omega i) ^ 2) <= v) :
    uniformProbability
        (failureEvent P E (Q * Real.sqrt v) kappa
          tGeom tCollision tDegree) <=
      (tau + 1 : ℕ) * pGeom / tGeom +
        (tau + 1 : ℕ) *
            (P.candidates.card.choose 2 * pCollision / E) / tCollision +
        P.candidates.card * pDegree / tDegree +
        (tau * (Real.sqrt v / Q)) / kappa := by
  let : Nonempty (AugmentationFull.Sample D s) :=
    HalfSample.sliceNonempty hcard
  let geomFail : AugmentationFull.Sample D s -> Prop := fun omega =>
    tGeom <= CollisionCounting.eventCount (Finset.range (tau + 1))
      P.geometricBad omega
  let collisionFail : AugmentationFull.Sample D s -> Prop := fun omega =>
    tCollision <= CollisionCounting.eventCount (Finset.range (tau + 1))
      (AugmentationFull.collisionBad P E) omega
  let degreeFail : AugmentationFull.Sample D s -> Prop := fun omega =>
    tDegree <= CollisionCounting.eventCount P.candidates P.degreeBad omega
  let tailFail : AugmentationFull.Sample D s -> Prop := fun omega =>
    kappa <= AugmentationFull.tailBudget P (Q * Real.sqrt v) omega
  have hgeomProb : uniformProbability geomFail <=
      (tau + 1 : ℕ) * pGeom / tGeom := by
    simpa [geomFail] using
      (CollisionCounting.uniformProbability_eventCount_ge_le
        (Finset.range (tau + 1)) P.geometricBad pGeom tGeom htGeom
        (fun i hi => hgeom i (Finset.mem_range.mp hi)))
  have hcollisionOne : ∀ i < tau + 1,
      uniformProbability (AugmentationFull.collisionBad P E i) <=
        P.candidates.card.choose 2 * pCollision / E := by
    intro i hi
    change uniformProbability (fun omega => E <=
      ((CollisionCounting.collisionEdges
        P.candidates (P.value i) omega).card : ℝ)) <= _
    exact CollisionCounting.uniformProbability_card_collisionEdges_ge_le
      P.candidates (P.value i) pCollision E hE (hcollision i hi)
  have hcollisionProb : uniformProbability collisionFail <=
      (tau + 1 : ℕ) *
          (P.candidates.card.choose 2 * pCollision / E) / tCollision := by
    simpa [collisionFail] using
      (CollisionCounting.uniformProbability_eventCount_ge_le
        (Finset.range (tau + 1)) (AugmentationFull.collisionBad P E)
        (P.candidates.card.choose 2 * pCollision / E)
        tCollision htCollision
        (fun i hi => hcollisionOne i (Finset.mem_range.mp hi)))
  have hdegreeProb : uniformProbability degreeFail <=
      P.candidates.card * pDegree / tDegree := by
    exact CollisionCounting.uniformProbability_eventCount_ge_le
      P.candidates P.degreeBad pDegree tDegree htDegree hdegree
  have htailMean : uniformExpectation
      (AugmentationFull.tailBudget P (Q * Real.sqrt v)) <=
        tau * (Real.sqrt v / Q) :=
    AugmentationFull.uniformExpectation_tailBudget_le
      hcard P hv hQ hsecond
  have htailNonneg : ∀ omega,
      0 <= AugmentationFull.tailBudget P (Q * Real.sqrt v) omega := by
    intro omega
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  have htailProb : uniformProbability tailFail <=
      (tau * (Real.sqrt v / Q)) / kappa :=
    AugmentationFull.uniformProbability_le_of_expectation_le
      (AugmentationFull.tailBudget P (Q * Real.sqrt v)) kappa _
        hkappa htailNonneg htailMean
  let risk : AugmentationFull.Sample D s -> ℝ := fun omega =>
    (if geomFail omega then 1 else 0) +
      (if collisionFail omega then 1 else 0) +
      (if degreeFail omega then 1 else 0) +
      (if tailFail omega then 1 else 0)
  have hriskMean : uniformExpectation risk <=
      (tau + 1 : ℕ) * pGeom / tGeom +
        (tau + 1 : ℕ) *
            (P.candidates.card.choose 2 * pCollision / E) / tCollision +
        P.candidates.card * pDegree / tDegree +
        (tau * (Real.sqrt v / Q)) / kappa := by
    rw [show uniformExpectation risk =
        uniformProbability geomFail + uniformProbability collisionFail +
          uniformProbability degreeFail + uniformProbability tailFail by
      simp only [risk, uniformExpectation_add,
        AugmentationFull.uniformExpectation_indicator]]
    linarith
  have hriskNonneg : ∀ omega, 0 <= risk omega := by
    intro omega
    dsimp only [risk]
    split_ifs <;> norm_num
  have hriskProb : uniformProbability (fun omega => (1 : ℝ) <= risk omega) <=
      (tau + 1 : ℕ) * pGeom / tGeom +
        (tau + 1 : ℕ) *
            (P.candidates.card.choose 2 * pCollision / E) / tCollision +
        P.candidates.card * pDegree / tDegree +
        (tau * (Real.sqrt v / Q)) / kappa := by
    simpa only [div_one] using
      (AugmentationFull.uniformProbability_le_of_expectation_le risk 1 _
        (by norm_num) hriskNonneg hriskMean)
  calc
    uniformProbability
        (failureEvent P E (Q * Real.sqrt v) kappa
          tGeom tCollision tDegree) <=
        uniformProbability (fun omega => (1 : ℝ) <= risk omega) := by
      apply uniformProbability_mono
      intro omega homega
      change geomFail omega ∨ collisionFail omega ∨
        degreeFail omega ∨ tailFail omega at homega
      rcases homega with homega | homega | homega | homega
      · dsimp only [risk]
        rw [if_pos homega]
        split_ifs <;> norm_num
      · dsimp only [risk]
        rw [if_pos homega]
        split_ifs <;> norm_num
      · dsimp only [risk]
        rw [if_pos homega]
        split_ifs <;> norm_num
      · dsimp only [risk]
        rw [if_pos homega]
        split_ifs <;> norm_num
    _ <= _ := hriskProb

/-- **Balanced full-exposure probability bound.**

Half-sample symmetry supplies the endpoint event with probability at least
`1 / 2`.  The four explicitly estimated risks have total probability at
most `1 / 6`; hence their simultaneous complement together with the
endpoint event, namely `FullExposureEvent`, has probability at least
`1 / 3`. -/
theorem one_third_le_uniformProbability_fullExposureEvent_of_itemBounds
    {D : Type u} [Fintype D] [DecidableEq D]
    {X : Type v} [LinearOrder X] [DecidableEq X]
    {s tau : ℕ}
    (hcard : Fintype.card D = 2 * s)
    (P : AugmentationFull.PartialExposureData D X s tau)
    (lam E v Q kappa tGeom tCollision tDegree : ℝ)
    (hv : 0 < v) (hQ : 0 < Q) (hkappa : 0 < kappa) (hE : 0 < E)
    (htGeom : 0 < tGeom) (htCollision : 0 < tCollision)
    (htDegree : 0 < tDegree)
    (hmeanRise : lam <=
      P.endpointOffset + (∑ d, P.endpointCoeff d) / 2)
    (pGeom pCollision pDegree : ℝ)
    (hgeom : ∀ i < tau + 1,
      uniformProbability (P.geometricBad i) <= pGeom)
    (hcollision : ∀ i < tau + 1,
      ∀ x ∈ P.candidates, ∀ y ∈ P.candidates, x ≠ y ->
        uniformProbability (fun omega =>
          P.value i x omega = P.value i y omega) <= pCollision)
    (hdegree : ∀ x ∈ P.candidates,
      uniformProbability (P.degreeBad x) <= pDegree)
    (hsecond : ∀ i < tau,
      uniformExpectation (fun omega : AugmentationFull.Sample D s =>
        (AugmentationFull.increment P omega i) ^ 2) <= v)
    (hrisk :
      (tau + 1 : ℕ) * pGeom / tGeom +
          (tau + 1 : ℕ) *
              (P.candidates.card.choose 2 * pCollision / E) / tCollision +
          P.candidates.card * pDegree / tDegree +
          (tau * (Real.sqrt v / Q)) / kappa <= 1 / 6) :
    (1 : ℝ) / 3 <= uniformProbability
      (AugmentationFull.FullExposureEvent P lam E (Q * Real.sqrt v) kappa
        tGeom tCollision tDegree) := by
  let : Nonempty (AugmentationFull.Sample D s) :=
    HalfSample.sliceNonempty hcard
  let endpoint : AugmentationFull.Sample D s -> Prop := fun omega =>
    lam <= P.path omega tau - P.path omega 0
  have hendpoint : (1 : ℝ) / 2 <= uniformProbability endpoint := by
    simpa [endpoint] using
      one_half_le_endpointProbability hcard P lam hmeanRise
  have hfailure : uniformProbability
      (failureEvent P E (Q * Real.sqrt v) kappa
        tGeom tCollision tDegree) <= 1 / 6 :=
    (uniformProbability_failureEvent_le_itemRisk hcard P E v Q kappa
      tGeom tCollision tDegree hv hQ hkappa hE htGeom htCollision htDegree
      pGeom pCollision pDegree hgeom hcollision hdegree hsecond).trans hrisk
  have hsurvive := AugmentationFull.sub_le_uniformProbability_and_not
    endpoint
    (failureEvent P E (Q * Real.sqrt v) kappa
      tGeom tCollision tDegree)
    (1 / 2) (1 / 6) hendpoint hfailure
  have hthird : (1 : ℝ) / 3 <= uniformProbability (fun omega =>
      endpoint omega ∧
        ¬ failureEvent P E (Q * Real.sqrt v) kappa
          tGeom tCollision tDegree omega) := by
    norm_num at hsurvive ⊢
    exact hsurvive
  refine hthird.trans (uniformProbability_mono ?_)
  intro omega homega
  rcases homega with ⟨hendpointOmega, hfailureOmega⟩
  change ¬ (_ ∨ _ ∨ _ ∨ _) at hfailureOmega
  push Not at hfailureOmega
  rcases hfailureOmega with
    ⟨hgeomOmega, hcollisionOmega, hdegreeOmega, htailOmega⟩
  exact ⟨hendpointOmega, hgeomOmega, hcollisionOmega,
    hdegreeOmega, htailOmega⟩

end

end AugmentationGraphFullProbability
end Erdos636
