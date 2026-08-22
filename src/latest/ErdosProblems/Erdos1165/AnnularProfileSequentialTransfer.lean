/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.AppendixA11A12ScaleCertificate
import ErdosProblems.Erdos1165.SequentialStoppedAtoms

/-!
# Literal sequential stopped histories for the Appendix-A profile

This is the measure-theoretic bridge from full stopped-history atoms to the
walk-facing constrained-profile estimate.  A profile atom is built by
successively adjoining measurable fresh-tail conditions at genuine stopping
times.  `SequentialStoppedAtoms.atomEvent_measure_mem_Icc_prod_on` supplies
its probability lower bound from the one-step annular kernels.

The final family retains one atom for every constrained profile.  The atoms
must be pairwise disjoint and pathwise contained in the literal stopped
successful-point event.  Summing them proves the desired lower bound.  No
conditional equality for a coarse future vector, and no assumption already
equivalent to the final union-event estimate, occurs here.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.AnnularProfileSequentialTransfer

noncomputable section

open AppendixFirstMoment AppendixA11A12ScaleCertificate
  Proposition13Assembly Proposition13Scales SequentialStoppedAtoms
  TerminalExcursionBridge

/-- A single literal stopped-history atom realizing one prescribed internal
profile.  All past events are measurable at the next clock, while the fresh
kernel is bounded only on the geometrically valid stopped-position shell. -/
structure SequentialProfileAtom (blockStart scale : ℕ) (profileDelta historyLoss : ℝ)
    (x : Point) (m : Profile scale) where
  initial : Set StepPath
  tau : ℕ → StepPath → WithTop ℕ
  fresh : ℕ → Point → Set StepPath
  stages : ℕ
  valid : ℕ → Set Point
  lower : ℕ → ℝ≥0∞
  upper : ℕ → ℝ≥0∞
  stopping : ∀ j, IsStoppingTime incrementFiltration (tau j)
  history_measurable : ∀ j, IsMeasurableAtWithTopStopping (tau j)
    (atomEvent initial tau fresh j)
  finite : ∀ j, ∀ᵐ omega ∂fairSteps, tau j omega < ⊤
  support : ∀ j omega, omega ∈ atomEvent initial tau fresh j →
    tau j omega < ⊤ → stoppedPosition (tau j) omega ∈ valid j
  fresh_measurable : ∀ j z, MeasurableSet (fresh j z)
  fresh_probability : ∀ j z, z ∈ valid j →
    fairSteps (fresh j z) ∈ Set.Icc (lower j) (upper j)
  historyLoss_nonneg : 0 ≤ historyLoss
  numerical_lower :
    ENNReal.ofReal (historyLoss * profileWeight m) ≤
      fairSteps initial * ∏ j ∈ Finset.range stages, lower j
  atom_measurable : MeasurableSet (atomEvent initial tau fresh stages)
  atom_subset : atomEvent initial tau fresh stages ⊆
    stoppedSuccessfulPointEvent blockStart scale profileDelta x

/-- The actual event represented by a sequential profile atom. -/
def SequentialProfileAtom.event
    {blockStart scale : ℕ} {profileDelta historyLoss : ℝ} {x : Point}
    {m : Profile scale}
    (a : SequentialProfileAtom blockStart scale profileDelta historyLoss x m) :
    Set StepPath :=
  atomEvent a.initial a.tau a.fresh a.stages

/-- A one-profile lower bound obtained by applying full-history sequential
strong Markov at every coordinate. -/
theorem SequentialProfileAtom.loss_mul_profileWeight_le_measureReal
    {blockStart scale : ℕ} {profileDelta historyLoss : ℝ} {x : Point}
    {m : Profile scale}
    (a : SequentialProfileAtom blockStart scale profileDelta historyLoss x m) :
    historyLoss * profileWeight m ≤
      fairSteps.real a.event := by
  have hiter := atomEvent_measure_mem_Icc_prod_on
    a.stopping a.history_measurable a.finite a.valid a.support
    a.fresh_measurable a.lower a.upper a.fresh_probability a.stages
  have henn : ENNReal.ofReal (historyLoss * profileWeight m) ≤
      fairSteps a.event := a.numerical_lower.trans hiter.1
  have hreal := ENNReal.toReal_mono (measure_ne_top fairSteps a.event) henn
  have hnonneg : 0 ≤ historyLoss * profileWeight m :=
    mul_nonneg a.historyLoss_nonneg (profileWeight_nonneg m)
  simpa only [ENNReal.toReal_ofReal hnonneg, Measure.real] using hreal

/-- A disjoint full-history atom for every constrained profile. -/
structure SequentialProfileFamily (blockStart scale : ℕ)
    (profileDelta historyLoss : ℝ) (x : Point) where
  atom : ∀ m : Profile scale,
    SequentialProfileAtom blockStart scale profileDelta historyLoss x m
  disjoint : ∀ m ∈ constrainedProfiles scale profileDelta,
    ∀ m' ∈ constrainedProfiles scale profileDelta, m ≠ m' →
      Disjoint (atom m).event (atom m').event

/-- The finite union of the literal full-history atoms for all constrained
profiles. -/
def SequentialProfileFamily.event
    {blockStart scale : ℕ} {profileDelta historyLoss : ℝ} {x : Point}
    (family : SequentialProfileFamily blockStart scale profileDelta historyLoss x) :
    Set StepPath :=
  ⋃ m ∈ constrainedProfiles scale profileDelta, (family.atom m).event

lemma SequentialProfileFamily.event_subset
    {blockStart scale : ℕ} {profileDelta historyLoss : ℝ} {x : Point}
    (family : SequentialProfileFamily blockStart scale profileDelta historyLoss x) :
    family.event ⊆
      stoppedSuccessfulPointEvent blockStart scale profileDelta x := by
  intro omega homega
  simp only [SequentialProfileFamily.event, mem_iUnion] at homega
  obtain ⟨m, _hm, hatom⟩ := homega
  exact (family.atom m).atom_subset hatom

lemma SequentialProfileFamily.measure_event_eq_sum
    {blockStart scale : ℕ} {profileDelta historyLoss : ℝ} {x : Point}
    (family : SequentialProfileFamily blockStart scale profileDelta historyLoss x) :
    fairSteps family.event =
      ∑ m ∈ constrainedProfiles scale profileDelta,
        fairSteps (family.atom m).event := by
  unfold SequentialProfileFamily.event
  apply measure_biUnion_finset
  · intro m hm m' hm' hne
    exact family.disjoint m hm m' hm' hne
  · intro m _hm
    exact (family.atom m).atom_measurable

/-- Summing the disjoint sequential atoms gives the complete constrained
profile lower bound with the honest annular-history loss. -/
theorem SequentialProfileFamily.historyLoss_mul_constrainedProfileWeight_le
    {blockStart scale : ℕ} {profileDelta historyLoss : ℝ} {x : Point}
    (family : SequentialProfileFamily blockStart scale profileDelta historyLoss x) :
    historyLoss * constrainedProfileWeight scale profileDelta ≤
      fairSteps.real
        (stoppedSuccessfulPointEvent blockStart scale profileDelta x) := by
  have hsum :
      historyLoss * constrainedProfileWeight scale profileDelta ≤
        ∑ m ∈ constrainedProfiles scale profileDelta,
          fairSteps.real (family.atom m).event := by
    unfold constrainedProfileWeight
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun m _hm ↦
      (family.atom m).loss_mul_profileWeight_le_measureReal
  have hunion :
      (∑ m ∈ constrainedProfiles scale profileDelta,
          fairSteps.real (family.atom m).event) =
        fairSteps.real family.event := by
    rw [Measure.real, family.measure_event_eq_sum,
      ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top fairSteps _)]
    rfl
  rw [hunion] at hsum
  exact hsum.trans (measureReal_mono family.event_subset)

/-- Construct the corrected walk-facing one-point transfer from literal
sequential stopped histories at every deterministic block and candidate. -/
theorem annularOnePointProfileTransfer_of_sequentialFamilies
    {delta : ℝ} {n : ℕ}
    (families : ∀ (i : Fin (chosenBlockCount delta n)) x,
      x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      SequentialProfileFamily
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta
        (annularHistoryLoss delta n) x) :
    AnnularOnePointProfileTransfer delta n := by
  refine ⟨?_⟩
  intro i x hx
  let family := families i x hx
  exact family.historyLoss_mul_constrainedProfileWeight_le

end

end Erdos1165.AnnularProfileSequentialTransfer
