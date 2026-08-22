/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.AnnularProfileSequentialTransfer

/-!
# Sequential upper transfer for a complete annular profile

The existing sequential profile family is tailored to the first-moment
lower bound.  The retained outside skeleton in the far-pair argument also
needs the dual statement: an exact disjoint profile partition, together
with endpoint-integrated one-step upper kernels, bounds the whole successful
event by an explicit multiple of `constrainedProfileWeight`.

This file supplies that measure-theoretic step.  Its premises are literal
stopping-time atoms and a numerical product bound, not an assumed upper
bound for the union event.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.AnnularProfileSequentialUpper

open AppendixFirstMoment Proposition13Assembly SequentialStoppedAtoms
open TerminalExcursionBridge

noncomputable section

/-- One full-history stopped atom realizing a prescribed profile, with its
actual endpoint-integrated kernel product bounded from above. -/
structure SequentialProfileUpperAtom
    (blockStart scale : ℕ) (profileDelta historyGain : ℝ)
    (x : Point) (m : Profile scale) where
  initial : Set StepPath
  tau : ℕ → StepPath → WithTop ℕ
  fresh : ℕ → Point → Set StepPath
  stages : ℕ
  valid : ℕ → Set Point
  lower : ℕ → ℝ≥0∞
  upper : ℕ → ℝ≥0∞
  stopping : ∀ j < stages, IsStoppingTime incrementFiltration (tau j)
  history_measurable : ∀ j < stages, IsMeasurableAtWithTopStopping (tau j)
    (atomEvent initial tau fresh j)
  finite : ∀ j < stages, ∀ᵐ omega ∂fairSteps, tau j omega < ⊤
  support : ∀ j < stages, ∀ omega, omega ∈ atomEvent initial tau fresh j →
    tau j omega < ⊤ → stoppedPosition (tau j) omega ∈ valid j
  fresh_measurable : ∀ j < stages, ∀ z, MeasurableSet (fresh j z)
  fresh_probability : ∀ j < stages, ∀ z, z ∈ valid j →
    fairSteps (fresh j z) ∈ Set.Icc (lower j) (upper j)
  historyGain_nonneg : 0 ≤ historyGain
  numerical_upper :
    fairSteps initial * ∏ j ∈ Finset.range stages, upper j ≤
      ENNReal.ofReal (historyGain * profileWeight m)
  atom_measurable : MeasurableSet (atomEvent initial tau fresh stages)
  atom_subset : atomEvent initial tau fresh stages ⊆
    stoppedSuccessfulPointEvent blockStart scale profileDelta x

def SequentialProfileUpperAtom.event
    {blockStart scale : ℕ} {profileDelta historyGain : ℝ} {x : Point}
    {m : Profile scale}
    (a : SequentialProfileUpperAtom
      blockStart scale profileDelta historyGain x m) : Set StepPath :=
  atomEvent a.initial a.tau a.fresh a.stages

/-- Sequential strong Markov plus the explicit product estimate gives the
one-profile upper bound. -/
theorem SequentialProfileUpperAtom.measureReal_le_gain_mul_profileWeight
    {blockStart scale : ℕ} {profileDelta historyGain : ℝ} {x : Point}
    {m : Profile scale}
    (a : SequentialProfileUpperAtom
      blockStart scale profileDelta historyGain x m) :
    fairSteps.real a.event ≤ historyGain * profileWeight m := by
  have hiter := atomEvent_measure_mem_Icc_prod_on_bounded a.stages
    a.stopping a.history_measurable a.finite a.valid a.support
    a.fresh_measurable a.lower a.upper a.fresh_probability
  have henn : fairSteps a.event ≤
      ENNReal.ofReal (historyGain * profileWeight m) :=
    hiter.2.trans a.numerical_upper
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top henn
  have hnonneg : 0 ≤ historyGain * profileWeight m :=
    mul_nonneg a.historyGain_nonneg (profileWeight_nonneg m)
  simpa only [Measure.real, ENNReal.toReal_ofReal hnonneg] using hreal

/-- A disjoint family which covers the entire successful event, not merely
a selected lower-bound subevent. -/
structure SequentialProfileUpperFamily
    (blockStart scale : ℕ) (profileDelta historyGain : ℝ) (x : Point) where
  atom : ∀ m : Profile scale,
    SequentialProfileUpperAtom
      blockStart scale profileDelta historyGain x m
  disjoint : ∀ m ∈ constrainedProfiles scale profileDelta,
    ∀ m' ∈ constrainedProfiles scale profileDelta, m ≠ m' →
      Disjoint (atom m).event (atom m').event
  cover : stoppedSuccessfulPointEvent blockStart scale profileDelta x =
    ⋃ m ∈ constrainedProfiles scale profileDelta, (atom m).event

def SequentialProfileUpperFamily.event
    {blockStart scale : ℕ} {profileDelta historyGain : ℝ} {x : Point}
    (family : SequentialProfileUpperFamily
      blockStart scale profileDelta historyGain x) : Set StepPath :=
  ⋃ m ∈ constrainedProfiles scale profileDelta, (family.atom m).event

lemma SequentialProfileUpperFamily.measure_event_eq_sum
    {blockStart scale : ℕ} {profileDelta historyGain : ℝ} {x : Point}
    (family : SequentialProfileUpperFamily
      blockStart scale profileDelta historyGain x) :
    fairSteps family.event =
      ∑ m ∈ constrainedProfiles scale profileDelta,
        fairSteps (family.atom m).event := by
  unfold SequentialProfileUpperFamily.event
  apply measure_biUnion_finset
  · intro m hm m' hm' hne
    exact family.disjoint m hm m' hm' hne
  · intro m _hm
    exact (family.atom m).atom_measurable

/-- Summing all disjoint upper atoms bounds the literal successful event by
the checked constrained-profile mass. -/
theorem SequentialProfileUpperFamily.measureReal_le_gain_mul_constrainedProfileWeight
    {blockStart scale : ℕ} {profileDelta historyGain : ℝ} {x : Point}
    (family : SequentialProfileUpperFamily
      blockStart scale profileDelta historyGain x) :
    fairSteps.real
        (stoppedSuccessfulPointEvent blockStart scale profileDelta x) ≤
      historyGain * constrainedProfileWeight scale profileDelta := by
  have hsum :
      (∑ m ∈ constrainedProfiles scale profileDelta,
          fairSteps.real (family.atom m).event) ≤
        historyGain * constrainedProfileWeight scale profileDelta := by
    unfold constrainedProfileWeight
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun m _hm ↦
      (family.atom m).measureReal_le_gain_mul_profileWeight
  have hunion :
      (∑ m ∈ constrainedProfiles scale profileDelta,
          fairSteps.real (family.atom m).event) =
        fairSteps.real family.event := by
    rw [Measure.real, family.measure_event_eq_sum,
      ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top fairSteps _)]
    rfl
  rw [hunion] at hsum
  rw [family.cover]
  simpa only [SequentialProfileUpperFamily.event] using hsum

end

end Erdos1165.AnnularProfileSequentialUpper
