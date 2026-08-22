/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.AppendixPairMomentActualKernel
import ErdosProblems.Erdos1165.MarkedBridgeFactorization

/-!
# The retained common-prefix mass in the far-pair estimate

After all inner-to-outer pieces have been removed, exact stopped-word
factorization leaves a nonnegative weight for the common prefix and two
continuation weights.  The elementary inequality proved here is the precise
finite summation step behind HLOZ's division by the prefix mass.  It is
separate from the stopped-word construction so that no conditional
independence of a future entrance vector is asserted.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AppendixPairReferenceMass

open AppendixFirstMoment AppendixPairMoment MarkedTerminalDisintegration
open Proposition13Assembly Proposition13Scales

noncomputable section

/-- One marginal mass after retaining a common prefix. -/
def prefixMarginalMass {Prefix : Type*} [Fintype Prefix]
    (prefixWeight tailWeight : Prefix → ℝ) : ℝ :=
  ∑ a, prefixWeight a * tailWeight a

/-- Joint mass of two continuations sharing the same retained prefix. -/
def sharedPrefixMass {Prefix : Type*} [Fintype Prefix]
    (prefixWeight leftTail rightTail : Prefix → ℝ) : ℝ :=
  ∑ a, prefixWeight a * leftTail a * rightTail a

lemma prefixMarginalMass_nonneg
    {Prefix : Type*} [Fintype Prefix]
    {prefixWeight tailWeight : Prefix → ℝ}
    (hprefix : ∀ a, 0 ≤ prefixWeight a)
    (htail : ∀ a, 0 ≤ tailWeight a) :
    0 ≤ prefixMarginalMass prefixWeight tailWeight := by
  unfold prefixMarginalMass
  exact Finset.sum_nonneg fun a _ ↦ mul_nonneg (hprefix a) (htail a)

lemma sharedPrefixMass_nonneg
    {Prefix : Type*} [Fintype Prefix]
    {prefixWeight leftTail rightTail : Prefix → ℝ}
    (hprefix : ∀ a, 0 ≤ prefixWeight a)
    (hleft : ∀ a, 0 ≤ leftTail a)
    (hright : ∀ a, 0 ≤ rightTail a) :
    0 ≤ sharedPrefixMass prefixWeight leftTail rightTail := by
  unfold sharedPrefixMass
  exact Finset.sum_nonneg fun a _ ↦
    mul_nonneg (mul_nonneg (hprefix a) (hleft a)) (hright a)

/-- Common-prefix Cauchy bookkeeping without square roots: if every retained
prefix atom has mass at least `prefixLower`, then its joint two-continuation
mass is at most the product of the two marginals divided by `prefixLower`.

The proof first bounds the diagonal sum by the full product of sums.  This is
the exact operation performed after the stopped-word Tonelli factorization. -/
theorem sharedPrefixMass_le_marginal_mul_div
    {Prefix : Type*} [Fintype Prefix]
    {prefixWeight leftTail rightTail : Prefix → ℝ}
    {prefixLower : ℝ}
    (hlower : 0 < prefixLower)
    (hprefixLower : ∀ a, prefixLower ≤ prefixWeight a)
    (hleft : ∀ a, 0 ≤ leftTail a)
    (hright : ∀ a, 0 ≤ rightTail a) :
    sharedPrefixMass prefixWeight leftTail rightTail ≤
      prefixMarginalMass prefixWeight leftTail *
          prefixMarginalMass prefixWeight rightTail /
        prefixLower := by
  have hprefix (a : Prefix) : 0 ≤ prefixWeight a :=
    hlower.le.trans (hprefixLower a)
  have hscaled : prefixLower *
        sharedPrefixMass prefixWeight leftTail rightTail ≤
      prefixMarginalMass prefixWeight leftTail *
        prefixMarginalMass prefixWeight rightTail := by
    unfold sharedPrefixMass prefixMarginalMass
    calc
      prefixLower * ∑ a, prefixWeight a * leftTail a * rightTail a =
          ∑ a, prefixLower *
            (prefixWeight a * leftTail a * rightTail a) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ a, (prefixWeight a * leftTail a) *
          (prefixWeight a * rightTail a) := by
        apply Finset.sum_le_sum
        intro a _ha
        have htail0 : 0 ≤ leftTail a * rightTail a :=
          mul_nonneg (hleft a) (hright a)
        calc
          prefixLower * (prefixWeight a * leftTail a * rightTail a) =
              (prefixLower * prefixWeight a) *
                (leftTail a * rightTail a) := by ring
          _ ≤ (prefixWeight a * prefixWeight a) *
                (leftTail a * rightTail a) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (hprefixLower a) (hprefix a))
              htail0
          _ = (prefixWeight a * leftTail a) *
                (prefixWeight a * rightTail a) := by ring
      _ ≤ (∑ a, prefixWeight a * leftTail a) *
          ∑ a, prefixWeight a * rightTail a := by
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro a _ha
        have hsingle : prefixWeight a * rightTail a ≤
            ∑ b, prefixWeight b * rightTail b := by
          exact Finset.single_le_sum
            (fun b _hb ↦ mul_nonneg (hprefix b) (hright b))
            (Finset.mem_univ a)
        exact mul_le_mul_of_nonneg_left hsingle
          (mul_nonneg (hprefix a) (hleft a))
  apply (le_div_iff₀ hlower).2
  simpa [mul_comm] using hscaled

/-- If both one-point marginals are bounded by `pointUpper`, the retained
joint reference mass has the exact `pointUpper² / prefixLower` envelope. -/
theorem sharedPrefixMass_le_sq_div
    {Prefix : Type*} [Fintype Prefix]
    {prefixWeight leftTail rightTail : Prefix → ℝ}
    {prefixLower pointUpper : ℝ}
    (hlower : 0 < prefixLower)
    (hprefixLower : ∀ a, prefixLower ≤ prefixWeight a)
    (hleft : ∀ a, 0 ≤ leftTail a)
    (hright : ∀ a, 0 ≤ rightTail a)
    (hleftMarginal :
      prefixMarginalMass prefixWeight leftTail ≤ pointUpper)
    (hrightMarginal :
      prefixMarginalMass prefixWeight rightTail ≤ pointUpper) :
    sharedPrefixMass prefixWeight leftTail rightTail ≤
      pointUpper ^ 2 / prefixLower := by
  have hprefix (a : Prefix) : 0 ≤ prefixWeight a :=
    hlower.le.trans (hprefixLower a)
  have hleft0 : 0 ≤ prefixMarginalMass prefixWeight leftTail :=
    prefixMarginalMass_nonneg hprefix hleft
  have hright0 : 0 ≤ prefixMarginalMass prefixWeight rightTail :=
    prefixMarginalMass_nonneg hprefix hright
  have hpoint0 : 0 ≤ pointUpper := hleft0.trans hleftMarginal
  have hproduct :
      prefixMarginalMass prefixWeight leftTail *
          prefixMarginalMass prefixWeight rightTail ≤ pointUpper ^ 2 := by
    rw [pow_two]
    exact mul_le_mul hleftMarginal hrightMarginal hright0 hpoint0
  exact (sharedPrefixMass_le_marginal_mul_div hlower hprefixLower
    hleft hright).trans (div_le_div_of_nonneg_right hproduct hlower.le)

/-- Adapter from an exact stopped-word/Tonelli factorization of the retained
reference skeleton to the correlation envelope used by
`stoppedFarPair_le_of_markedStoppedData`.

`hfactor` is an equality with an explicit common-prefix sum, rather than an
assumed pair estimate.  `MarkedBridgeFactorization` is designed to establish
this equality atom by atom for the concrete annular skeleton. -/
theorem referenceEventMass_mul_successful_le_sq_div_of_prefix_factorization
    {Prefix : Type*} [Fintype Prefix] {m : ℕ}
    (referenceMass : Fin m → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    (successful : Set StepPath)
    (prefixWeight leftTail rightTail : Prefix → ℝ)
    {prefixLower pointUpper : ℝ}
    (hfactor :
      (referenceEventMass referenceMass visitEvent).toReal *
          fairSteps.real successful =
        sharedPrefixMass prefixWeight leftTail rightTail)
    (hlower : 0 < prefixLower)
    (hprefixLower : ∀ a, prefixLower ≤ prefixWeight a)
    (hleft : ∀ a, 0 ≤ leftTail a)
    (hright : ∀ a, 0 ≤ rightTail a)
    (hleftMarginal :
      prefixMarginalMass prefixWeight leftTail ≤ pointUpper)
    (hrightMarginal :
      prefixMarginalMass prefixWeight rightTail ≤ pointUpper) :
    (referenceEventMass referenceMass visitEvent).toReal *
        fairSteps.real successful ≤ pointUpper ^ 2 / prefixLower := by
  rw [hfactor]
  exact sharedPrefixMass_le_sq_div hlower hprefixLower hleft hright
    hleftMarginal hrightMarginal

/-! ## The scalar profile-prefix specialization

For the HLOZ far-pair decomposition the shared object is the prescribed
profile through the separation scale, not an arbitrary atom of a partition.
Once the complementary stopped words have been summed, its mass is therefore
one scalar.  The following form is the one that can consume the analytic
lower bound `prefixProfileLower` without the false assertion that every
individual stopped skeleton atom has that much mass. -/

/-- Two continuations sharing a scalar prefix have joint mass at most the
product of their marginal upper bounds divided by any positive lower bound
for the prefix mass. -/
theorem commonPrefix_mul_left_mul_right_le_sq_div
    {prefixMass left right prefixLower pointUpper : ℝ}
    (hlower : 0 < prefixLower)
    (hprefix : prefixLower ≤ prefixMass)
    (hleft0 : 0 ≤ left) (hright0 : 0 ≤ right)
    (hleft : prefixMass * left ≤ pointUpper)
    (hright : prefixMass * right ≤ pointUpper) :
    prefixMass * left * right ≤ pointUpper ^ 2 / prefixLower := by
  have hprefix0 : 0 ≤ prefixMass := hlower.le.trans hprefix
  have hleftMarginal0 : 0 ≤ prefixMass * left := mul_nonneg hprefix0 hleft0
  have hrightMarginal0 : 0 ≤ prefixMass * right := mul_nonneg hprefix0 hright0
  have hpoint0 : 0 ≤ pointUpper := hleftMarginal0.trans hleft
  apply (le_div_iff₀ hlower).2
  calc
    prefixMass * left * right * prefixLower ≤
        (prefixMass * left) * (prefixMass * right) := by
      have := mul_le_mul_of_nonneg_left hprefix hleftMarginal0
      nlinarith
    _ ≤ pointUpper * pointUpper :=
      mul_le_mul hleft hright hrightMarginal0 hpoint0
    _ = pointUpper ^ 2 := by ring

/-- Exact adapter for the retained stopped-word factorization at the concrete
HLOZ profile prefix.  The assumptions are only the three independently
proved ingredients:

* `hfactor`, the Tonelli/stopped-word equality after summing the complementary
  skeleton;
* `hprofile`, the A.11/A.12 lower bound for the common prescribed prefix;
* the two one-point marginal bounds.

In particular the desired pair inequality is not an assumption. -/
theorem referenceEventMass_mul_successful_le_pairPrefixEnvelope
    {m prefixScale : ℕ}
    (referenceMass : Fin m → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    (successful : Set StepPath)
    (profileWeight leftContinuation rightContinuation pointUpper : ℝ)
    (hfactor :
      (referenceEventMass referenceMass visitEvent).toReal *
          fairSteps.real successful =
        profileWeight * leftContinuation * rightContinuation)
    (hprofile : prefixProfileLower prefixScale ≤ profileWeight)
    (hleft0 : 0 ≤ leftContinuation)
    (hright0 : 0 ≤ rightContinuation)
    (hleft : profileWeight * leftContinuation ≤ pointUpper)
    (hright : profileWeight * rightContinuation ≤ pointUpper) :
    (referenceEventMass referenceMass visitEvent).toReal *
        fairSteps.real successful ≤
      pointUpper ^ 2 / prefixProfileLower prefixScale := by
  rw [hfactor]
  exact commonPrefix_mul_left_mul_right_le_sq_div
    (prefixProfileLower_pos prefixScale) hprofile hleft0 hright0 hleft hright

/-- The same adapter with the actual constrained profile mass.  Here the
prefix lower comparison is discharged by the checked shifted A.11 and finite
A.12 estimate, so the only equality still required from the spatial layer is
the literal stopped-word factorization. -/
theorem referenceEventMass_mul_successful_le_pairPrefixEnvelope_of_constrainedProfile
    {m prefixScale : ℕ}
    (referenceMass : Fin m → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    (successful : Set StepPath)
    (leftContinuation rightContinuation pointUpper : ℝ)
    (hcutoff : GaussianGeometricCutoff.geometricCutoff ≤ prefixScale)
    (hfactor :
      (referenceEventMass referenceMass visitEvent).toReal *
          fairSteps.real successful =
        constrainedProfileWeight prefixScale chosenProfileDelta *
          leftContinuation * rightContinuation)
    (hleft0 : 0 ≤ leftContinuation)
    (hright0 : 0 ≤ rightContinuation)
    (hleft : constrainedProfileWeight prefixScale chosenProfileDelta *
        leftContinuation ≤ pointUpper)
    (hright : constrainedProfileWeight prefixScale chosenProfileDelta *
        rightContinuation ≤ pointUpper) :
    (referenceEventMass referenceMass visitEvent).toReal *
        fairSteps.real successful ≤
      pointUpper ^ 2 / prefixProfileLower prefixScale := by
  exact referenceEventMass_mul_successful_le_pairPrefixEnvelope
    referenceMass visitEvent successful
    (constrainedProfileWeight prefixScale chosenProfileDelta)
    leftContinuation rightContinuation pointUpper hfactor
    (prefixProfileLower_le_constrainedProfileWeight hcutoff)
    hleft0 hright0 hleft hright

/-! ## The source-aligned outside/tail decomposition

In HLOZ (A.16)--(A.17), the factor multiplying the complete outside
skeleton is a *uniform upper bound* for the inside continuation, after
partitioning by the number of crossings of the separating annulus.  There
is no assertion that the aggregate outside and inside masses factor through
one independent random prefix.  The following elementary lemma records the
actual multiplication step. -/

/-- If the retained outside skeleton is bounded by the one-point mass and
the reference continuation is bounded by the one-point mass divided by the
checked prefix lower bound, their product has the required far-pair
envelope. -/
theorem referenceEventMass_mul_successful_le_pairPrefixEnvelope_of_tail_upper
    {m prefixScale : ℕ}
    (referenceMass : Fin m → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    (successful : Set StepPath)
    {pointUpper : ℝ}
    (hpoint0 : 0 ≤ pointUpper)
    (hsuccessful : fairSteps.real successful ≤ pointUpper)
    (htail : (referenceEventMass referenceMass visitEvent).toReal ≤
      pointUpper / prefixProfileLower prefixScale) :
    (referenceEventMass referenceMass visitEvent).toReal *
        fairSteps.real successful ≤
      pointUpper ^ 2 / prefixProfileLower prefixScale := by
  have hprefix0 : 0 ≤ prefixProfileLower prefixScale :=
    prefixProfileLower_nonneg prefixScale
  have htail0 : 0 ≤
      (referenceEventMass referenceMass visitEvent).toReal :=
    ENNReal.toReal_nonneg
  calc
    (referenceEventMass referenceMass visitEvent).toReal *
          fairSteps.real successful ≤
        (pointUpper / prefixProfileLower prefixScale) * pointUpper :=
      mul_le_mul htail hsuccessful measureReal_nonneg
        (div_nonneg hpoint0 hprefix0)
    _ = pointUpper ^ 2 / prefixProfileLower prefixScale := by ring

/-- Source-correct two-stage A.16 bound.  The endpoint-integrated radial
profile continuation is charged to the complete stopped-skeleton event,
while the point-local-time terminal visit vector is a separate normalized
marked kernel.  Thus no radial offspring count is represented by
`terminalMarkedKernel`. -/
theorem referenceEventMass_mul_successful_le_pairPrefixEnvelope_of_twoStage
    {m prefixScale : ℕ}
    (referenceMass : Fin m → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    (successful retained : Set StepPath)
    (radialTail pointUpper : ℝ)
    (hpoint0 : 0 ≤ pointUpper)
    (hterminal :
      (referenceEventMass referenceMass visitEvent).toReal ≤ 1)
    (hsuccessful : fairSteps.real successful ≤
      radialTail * fairSteps.real retained)
    (hretained : fairSteps.real retained ≤ pointUpper)
    (hradial : radialTail ≤
      pointUpper / prefixProfileLower prefixScale) :
    (referenceEventMass referenceMass visitEvent).toReal *
        fairSteps.real successful ≤
      pointUpper ^ 2 / prefixProfileLower prefixScale := by
  have hretained0 : 0 ≤ fairSteps.real retained := measureReal_nonneg
  calc
    (referenceEventMass referenceMass visitEvent).toReal *
          fairSteps.real successful ≤
        1 * (radialTail * fairSteps.real retained) :=
      mul_le_mul hterminal hsuccessful measureReal_nonneg (by norm_num)
    _ = radialTail * fairSteps.real retained := one_mul _
    _ ≤ (pointUpper / prefixProfileLower prefixScale) * pointUpper :=
      mul_le_mul hradial hretained hretained0
        (div_nonneg hpoint0 (prefixProfileLower_nonneg prefixScale))
    _ = pointUpper ^ 2 / prefixProfileLower prefixScale := by ring

/-- Complete marked-stopped-data glue in the exact A.16--A.17 shape.  The
spatial construction must prove two genuine one-point facts: an upper bound
for the complete retained outside skeleton and a uniform upper bound for the
inside reference continuation.  No pair inequality or aggregate
independence statement is assumed. -/
theorem stoppedFarPair_le_of_markedStoppedData_and_tail_upper
    {blockLength scale prefixScale : ℕ} {profileDelta thickDelta : ℝ}
    {i : ℕ} {x y : Point}
    {Data Entrance Exit : Type*} {m : ℕ}
    (successful : Set StepPath)
    (loss : Fin m → ℝ≥0∞)
    (referenceMass : Fin m → ℕ → ℝ≥0∞)
    (skeletonWeight : Data →
      (Fin m → Entrance) → (Fin m → Exit) → ℝ≥0∞)
    (skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞)
    (markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    {harnackFactor pointUpper : ℝ}
    (hupper : MarkedKernelUpper loss referenceMass skeletonKernel markedKernel)
    (hdecompose : MarkedStoppedDataUpperDecomposition fairSteps
      (stoppedThickPointEvent (i * blockLength)
          scale profileDelta thickDelta x ∩
        stoppedThickPointEvent (i * blockLength)
          scale profileDelta thickDelta y)
      successful skeletonWeight skeletonKernel markedKernel visitEvent)
    (hcoefficient :
      (∏ j, loss j) * referenceEventMass referenceMass visitEvent ≠ ⊤)
    (hloss : (∏ j, loss j).toReal ≤ harnackFactor)
    (hharnack0 : 0 ≤ harnackFactor)
    (hpoint0 : 0 ≤ pointUpper)
    (hsuccessful : fairSteps.real successful ≤ pointUpper)
    (htail : (referenceEventMass referenceMass visitEvent).toReal ≤
      pointUpper / prefixProfileLower prefixScale) :
    fairSteps.real
        (stoppedThickPointEvent (i * blockLength)
            scale profileDelta thickDelta x ∩
          stoppedThickPointEvent (i * blockLength)
            scale profileDelta thickDelta y) ≤
      harnackFactor * (pointUpper ^ 2 / prefixProfileLower prefixScale) := by
  apply stoppedFarPair_le_of_markedStoppedData successful loss referenceMass
    skeletonWeight skeletonKernel markedKernel visitEvent hupper hdecompose
    hcoefficient hloss hharnack0
  exact referenceEventMass_mul_successful_le_pairPrefixEnvelope_of_tail_upper
    referenceMass visitEvent successful hpoint0 hsuccessful htail

/-- Complete glue theorem from a literal marked stopped-skeleton upper
decomposition and the scalar constrained-profile factorization to the
pointwise far-pair inequality.  This removes the abstract `href` premise of
`stoppedFarPair_le_of_markedStoppedData`; the remaining premises are the
actual kernel comparison, atom decomposition, and stopped-word equality. -/
theorem stoppedFarPair_le_of_markedStoppedData_and_constrainedProfileFactorization
    {blockLength scale prefixScale : ℕ} {profileDelta thickDelta : ℝ}
    {i : ℕ} {x y : Point}
    {Data Entrance Exit : Type*} {m : ℕ}
    (successful : Set StepPath)
    (loss : Fin m → ℝ≥0∞)
    (referenceMass : Fin m → ℕ → ℝ≥0∞)
    (skeletonWeight : Data →
      (Fin m → Entrance) → (Fin m → Exit) → ℝ≥0∞)
    (skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞)
    (markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    {harnackFactor pointUpper : ℝ}
    (hupper : MarkedKernelUpper loss referenceMass skeletonKernel markedKernel)
    (hdecompose : MarkedStoppedDataUpperDecomposition fairSteps
      (stoppedThickPointEvent (i * blockLength)
          scale profileDelta thickDelta x ∩
        stoppedThickPointEvent (i * blockLength)
          scale profileDelta thickDelta y)
      successful skeletonWeight skeletonKernel markedKernel visitEvent)
    (hcoefficient :
      (∏ j, loss j) * referenceEventMass referenceMass visitEvent ≠ ⊤)
    (hloss : (∏ j, loss j).toReal ≤ harnackFactor)
    (hharnack0 : 0 ≤ harnackFactor)
    (leftContinuation rightContinuation : ℝ)
    (hcutoff : GaussianGeometricCutoff.geometricCutoff ≤ prefixScale)
    (hfactor :
      (referenceEventMass referenceMass visitEvent).toReal *
          fairSteps.real successful =
        constrainedProfileWeight prefixScale chosenProfileDelta *
          leftContinuation * rightContinuation)
    (hleft0 : 0 ≤ leftContinuation)
    (hright0 : 0 ≤ rightContinuation)
    (hleft : constrainedProfileWeight prefixScale chosenProfileDelta *
        leftContinuation ≤ pointUpper)
    (hright : constrainedProfileWeight prefixScale chosenProfileDelta *
        rightContinuation ≤ pointUpper) :
    fairSteps.real
        (stoppedThickPointEvent (i * blockLength)
            scale profileDelta thickDelta x ∩
          stoppedThickPointEvent (i * blockLength)
            scale profileDelta thickDelta y) ≤
      harnackFactor * (pointUpper ^ 2 / prefixProfileLower prefixScale) := by
  apply stoppedFarPair_le_of_markedStoppedData successful loss referenceMass
    skeletonWeight skeletonKernel markedKernel visitEvent hupper hdecompose
    hcoefficient hloss hharnack0
  exact referenceEventMass_mul_successful_le_pairPrefixEnvelope_of_constrainedProfile
    referenceMass visitEvent successful leftContinuation rightContinuation
    pointUpper hcutoff hfactor hleft0 hright0 hleft hright

end

end Erdos1165.AppendixPairReferenceMass
