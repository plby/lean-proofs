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

import ErdosProblems.Erdos1165.AppendixA11A12ScaleCertificate
import ErdosProblems.Erdos1165.ProfileGapChain

/-!
# Full complementary-skeleton transfer for an Appendix-A profile

The future successful-point event cannot be conditioned at the first inner
entrance.  Instead one erases every marked inner-to-outer piece and retains
the complete complementary skeleton, including both endpoints of every
erased piece.  Its law is represented by an arbitrary nonnegative weight
`skeletonWeight` and an unmarked joint bridge kernel `skeletonKernel`.

For a fixed constrained profile, a `ProfileGapChain` records all offspring
counts in the erased pieces.  The marked joint kernel retains that gap chain
and the outer endpoints.  A pointwise marked Poisson-kernel comparison may
therefore be multiplied by the arbitrary skeleton weight and summed without
discarding any future dependence.  The exact weak-composition identity from
`ProfileGapChain` turns the resulting reference mass into `profileWeight`.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace Erdos1165.AnnularProfileMarkedSkeleton

noncomputable section

open AppendixFirstMoment AppendixA11A12ScaleCertificate
  Proposition13Assembly Proposition13Scales ProfileGapChain

/-! ## Kernel algebra with an arbitrary complementary skeleton -/

/-- Pointwise comparison of the joint profile-marked bridge kernel with its
unmarked bridge kernel.  The exit endpoint is retained explicitly. -/
def ProfileMarkedKernelLower
    {Entrance Exit : Type*} {n : ℕ} (m : Profile n)
    (loss : ℝ≥0∞) (skeletonKernel : Entrance → Exit → ℝ≥0∞)
    (markedKernel : Entrance → GapChain (profileList m) → Exit → ℝ≥0∞) : Prop :=
  ∀ u chain z,
    loss * ENNReal.ofReal (gapChainMass (profileList m) chain) *
        skeletonKernel u z ≤ markedKernel u chain z

/-- Mass of an unmarked complete complementary skeleton. -/
def successfulSkeletonMass
    {Data Entrance Exit : Type*}
    (skeletonWeight : Data → Entrance → Exit → ℝ≥0∞)
    (skeletonKernel : Entrance → Exit → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' data, ∑' u, ∑' z,
    skeletonWeight data u z * skeletonKernel u z

/-- Mass after reinserting every marked inner-to-outer piece realizing a
fixed profile. -/
def markedProfileMass
    {Data Entrance Exit : Type*} {n : ℕ} (m : Profile n)
    (skeletonWeight : Data → Entrance → Exit → ℝ≥0∞)
    (markedKernel : Entrance → GapChain (profileList m) → Exit → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' data, ∑' u, ∑' z, ∑' chain,
    skeletonWeight data u z * markedKernel u chain z

/-- Exact event bookkeeping for the full stopped skeleton.  The first field
is equality for the unmarked complementary-skeleton partition.  The second
is only the required containment direction after the marked pieces are
reinserted. -/
structure ProfileMarkedStoppedDecomposition
    {Omega Data Entrance Exit : Type*} [MeasurableSpace Omega]
    {n : ℕ} (m : Profile n) (mu : Measure Omega)
    (successful terminalEvent : Set Omega)
    (skeletonWeight : Data → Entrance → Exit → ℝ≥0∞)
    (skeletonKernel : Entrance → Exit → ℝ≥0∞)
    (markedKernel : Entrance → GapChain (profileList m) → Exit → ℝ≥0∞) : Prop where
  successful_eq :
    mu successful = successfulSkeletonMass skeletonWeight skeletonKernel
  marked_le_terminal :
    markedProfileMass m skeletonWeight markedKernel ≤ mu terminalEvent

private theorem fixedSkeleton_markedProfile_lower
    {Entrance Exit : Type*} {n : ℕ} {m : Profile n}
    (loss : ℝ≥0∞)
    (skeletonKernel : Entrance → Exit → ℝ≥0∞)
    (markedKernel : Entrance → GapChain (profileList m) → Exit → ℝ≥0∞)
    (hlower : ProfileMarkedKernelLower m loss skeletonKernel markedKernel)
    (weight : ℝ≥0∞) (u : Entrance) (z : Exit) :
    loss * (∑ chain : GapChain (profileList m),
        ENNReal.ofReal (gapChainMass (profileList m) chain)) *
        (weight * skeletonKernel u z) ≤
      ∑' chain : GapChain (profileList m), weight * markedKernel u chain z := by
  rw [← tsum_fintype (L := SummationFilter.unconditional _),
    ← ENNReal.tsum_mul_left,
    ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro chain
  calc
    loss * ENNReal.ofReal (gapChainMass (profileList m) chain) *
        (weight * skeletonKernel u z) =
      weight * (loss * ENNReal.ofReal (gapChainMass (profileList m) chain) *
        skeletonKernel u z) := by ac_rfl
    _ ≤ weight * markedKernel u chain z :=
      mul_le_mul le_rfl (hlower u chain z) bot_le bot_le

/-- The marked comparison survives summation over an arbitrary complete
complementary-skeleton weight. -/
theorem markedProfileMass_lower
    {Data Entrance Exit : Type*} {n : ℕ} {m : Profile n}
    (loss : ℝ≥0∞)
    (skeletonWeight : Data → Entrance → Exit → ℝ≥0∞)
    (skeletonKernel : Entrance → Exit → ℝ≥0∞)
    (markedKernel : Entrance → GapChain (profileList m) → Exit → ℝ≥0∞)
    (hlower : ProfileMarkedKernelLower m loss skeletonKernel markedKernel) :
    loss * (∑ chain : GapChain (profileList m),
        ENNReal.ofReal (gapChainMass (profileList m) chain)) *
        successfulSkeletonMass skeletonWeight skeletonKernel ≤
      markedProfileMass m skeletonWeight markedKernel := by
  rw [successfulSkeletonMass, markedProfileMass,
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro data
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro u
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro z
  exact fixedSkeleton_markedProfile_lower loss skeletonKernel markedKernel
    hlower (skeletonWeight data u z) u z

/-- Event-level conclusion for a fixed constrained profile. -/
theorem event_lower_of_profileMarkedStoppedData
    {Omega Data Entrance Exit : Type*} [MeasurableSpace Omega]
    {n : ℕ} {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m)
    (mu : Measure Omega) (successful terminalEvent : Set Omega)
    (loss : ℝ≥0∞)
    (skeletonWeight : Data → Entrance → Exit → ℝ≥0∞)
    (skeletonKernel : Entrance → Exit → ℝ≥0∞)
    (markedKernel : Entrance → GapChain (profileList m) → Exit → ℝ≥0∞)
    (hlower : ProfileMarkedKernelLower m loss skeletonKernel markedKernel)
    (hdecompose : ProfileMarkedStoppedDecomposition m mu successful terminalEvent
      skeletonWeight skeletonKernel markedKernel) :
    loss * ENNReal.ofReal (profileWeight m) * mu successful ≤
      mu terminalEvent := by
  rw [hdecompose.successful_eq,
    ← sum_ofReal_gapChainMass_profile_eq_ofReal_profileWeight hdelta hm]
  exact (markedProfileMass_lower loss skeletonWeight skeletonKernel
    markedKernel hlower).trans hdecompose.marked_le_terminal

/-- Real-probability form of the fixed-profile full-skeleton estimate. -/
theorem event_real_lower_of_profileMarkedStoppedData
    {Omega Data Entrance Exit : Type*} [MeasurableSpace Omega]
    {n : ℕ} {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m)
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (successful terminalEvent : Set Omega)
    (loss : ℝ≥0∞)
    (skeletonWeight : Data → Entrance → Exit → ℝ≥0∞)
    (skeletonKernel : Entrance → Exit → ℝ≥0∞)
    (markedKernel : Entrance → GapChain (profileList m) → Exit → ℝ≥0∞)
    (hlower : ProfileMarkedKernelLower m loss skeletonKernel markedKernel)
    (hdecompose : ProfileMarkedStoppedDecomposition m mu successful terminalEvent
      skeletonWeight skeletonKernel markedKernel) :
    (loss.toReal * profileWeight m) * mu.real successful ≤
      mu.real terminalEvent := by
  have h := event_lower_of_profileMarkedStoppedData hdelta hm mu successful
    terminalEvent loss skeletonWeight skeletonKernel markedKernel hlower hdecompose
  have hreal := ENNReal.toReal_mono (measure_ne_top mu terminalEvent) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (profileWeight_nonneg m)] at hreal
  simpa only [Measure.real] using hreal

/-! ## Literal atoms and summation over constrained profiles -/

/-- A fixed constrained profile together with a genuine full-skeleton
marked disintegration of its literal atom. -/
structure FullSkeletonProfileAtom
    (blockStart scale : ℕ) (profileDelta historyLoss : ℝ)
    (x : Point) (m : Profile scale) where
  Data : Type*
  Entrance : Type*
  Exit : Type*
  successful : Set StepPath
  atom : Set StepPath
  loss : ℝ≥0∞
  skeletonWeight : Data → Entrance → Exit → ℝ≥0∞
  skeletonKernel : Entrance → Exit → ℝ≥0∞
  markedKernel : Entrance → GapChain (profileList m) → Exit → ℝ≥0∞
  kernel_lower :
    ProfileMarkedKernelLower m loss skeletonKernel markedKernel
  decomposition :
    ProfileMarkedStoppedDecomposition m fairSteps successful atom
      skeletonWeight skeletonKernel markedKernel
  historyLoss_nonneg : 0 ≤ historyLoss
  historyLoss_le :
    historyLoss ≤ loss.toReal * fairSteps.real successful
  atom_measurable : MeasurableSet atom
  atom_subset : atom ⊆
    stoppedSuccessfulPointEvent blockStart scale profileDelta x

theorem FullSkeletonProfileAtom.historyLoss_mul_profileWeight_le
    {blockStart scale : ℕ} {profileDelta historyLoss : ℝ} {x : Point}
    {m : Profile scale} (hm : IsConstrainedProfile profileDelta m)
    (a : FullSkeletonProfileAtom blockStart scale profileDelta historyLoss x m)
    (hdelta : profileDelta ≤ 1) :
    historyLoss * profileWeight m ≤ fairSteps.real a.atom := by
  have hmarked := event_real_lower_of_profileMarkedStoppedData hdelta hm
    fairSteps a.successful a.atom a.loss a.skeletonWeight a.skeletonKernel
      a.markedKernel a.kernel_lower a.decomposition
  have hweight : 0 ≤ profileWeight m := profileWeight_nonneg m
  calc
    historyLoss * profileWeight m ≤
        (a.loss.toReal * fairSteps.real a.successful) * profileWeight m :=
      mul_le_mul_of_nonneg_right a.historyLoss_le hweight
    _ = (a.loss.toReal * profileWeight m) * fairSteps.real a.successful := by ring
    _ ≤ fairSteps.real a.atom := hmarked

/-- Pairwise-disjoint literal full-skeleton atoms, one for every constrained
profile. -/
structure FullSkeletonProfileFamily
    (blockStart scale : ℕ) (profileDelta historyLoss : ℝ) (x : Point) where
  atom : ∀ m : ↥(constrainedProfiles scale profileDelta),
    FullSkeletonProfileAtom blockStart scale profileDelta historyLoss x m.1
  disjoint : Pairwise fun m m' : ↥(constrainedProfiles scale profileDelta) ↦
    Disjoint (atom m).atom (atom m').atom

def FullSkeletonProfileFamily.event
    {blockStart scale : ℕ} {profileDelta historyLoss : ℝ} {x : Point}
    (family : FullSkeletonProfileFamily
      blockStart scale profileDelta historyLoss x) : Set StepPath :=
  ⋃ m : ↥(constrainedProfiles scale profileDelta), (family.atom m).atom

lemma FullSkeletonProfileFamily.event_subset
    {blockStart scale : ℕ} {profileDelta historyLoss : ℝ} {x : Point}
    (family : FullSkeletonProfileFamily
      blockStart scale profileDelta historyLoss x) :
    family.event ⊆ stoppedSuccessfulPointEvent blockStart scale profileDelta x := by
  intro omega homega
  simp only [FullSkeletonProfileFamily.event, mem_iUnion] at homega
  obtain ⟨m, hatom⟩ := homega
  exact (family.atom m).atom_subset hatom

lemma FullSkeletonProfileFamily.measure_event_eq_sum
    {blockStart scale : ℕ} {profileDelta historyLoss : ℝ} {x : Point}
    (family : FullSkeletonProfileFamily
      blockStart scale profileDelta historyLoss x) :
    fairSteps family.event =
      ∑ m : ↥(constrainedProfiles scale profileDelta),
        fairSteps (family.atom m).atom := by
  unfold FullSkeletonProfileFamily.event
  rw [measure_iUnion family.disjoint]
  · simp only [tsum_fintype]
  · intro m
    exact (family.atom m).atom_measurable

theorem FullSkeletonProfileFamily.historyLoss_mul_constrainedProfileWeight_le
    {blockStart scale : ℕ} {profileDelta historyLoss : ℝ} {x : Point}
    (hdelta : profileDelta ≤ 1)
    (family : FullSkeletonProfileFamily
      blockStart scale profileDelta historyLoss x) :
    historyLoss * constrainedProfileWeight scale profileDelta ≤
      fairSteps.real
        (stoppedSuccessfulPointEvent blockStart scale profileDelta x) := by
  have hsum :
      historyLoss * constrainedProfileWeight scale profileDelta ≤
        ∑ m : ↥(constrainedProfiles scale profileDelta),
          fairSteps.real (family.atom m).atom := by
    unfold constrainedProfileWeight
    rw [← Finset.sum_attach, Finset.mul_sum]
    exact Finset.sum_le_sum fun m _hm ↦
      (family.atom m).historyLoss_mul_profileWeight_le
        (mem_constrainedProfiles.mp m.property) hdelta
  have hunion :
      (∑ m : ↥(constrainedProfiles scale profileDelta),
          fairSteps.real (family.atom m).atom) =
        fairSteps.real family.event := by
    rw [Measure.real, family.measure_event_eq_sum,
      ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top fairSteps _)]
    rfl
  rw [hunion] at hsum
  exact hsum.trans (measureReal_mono family.event_subset)

/-- The corrected walk-facing transfer obtained from genuine full
complementary-skeleton families. -/
theorem annularOnePointProfileTransfer_of_fullSkeletonFamilies
    {delta : ℝ} {n : ℕ}
    (families : ∀ (i : Fin (chosenBlockCount delta n)) x,
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      FullSkeletonProfileFamily
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta
        (annularHistoryLoss delta n) x) :
    AnnularOnePointProfileTransfer delta n := by
  refine ⟨?_⟩
  intro i x hx
  exact (families i x hx).historyLoss_mul_constrainedProfileWeight_le
    (by norm_num [chosenProfileDelta])

end

end Erdos1165.AnnularProfileMarkedSkeleton
