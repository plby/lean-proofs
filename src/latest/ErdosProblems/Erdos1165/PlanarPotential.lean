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

import ErdosProblems.Erdos1165.Basic

/-!
# Elementary planar simple-random-walk potential theory

This file supplies the probability-space and stopping-time foundations needed
by a formalization of the planar favorite-site theorem of Hao--Li--Okada--Zheng.
It deliberately contains only proved facts: finite cylinder probabilities,
translation and central-reflection symmetry, canonical hitting times, and
finite Green-function bounds.

The logarithmic potential-kernel estimates, recurrence theorem, strong Markov
decomposition, and moderate-deviation estimates used in the published proof
are not presently available in Mathlib; they are not postulated here.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165

namespace PlanarPotential

lemma directionVector_injective : Function.Injective directionVector := by
  intro d e h
  fin_cases d <;> fin_cases e <;> simp_all [directionVector]

/-- The walk started from `a` and driven by `ω`. -/
def trajectoryFrom (a : Point) (ω : StepPath) (n : ℕ) : Point :=
  a + trajectory ω n

@[simp] lemma trajectoryFrom_zero (a : Point) (ω : StepPath) :
    trajectoryFrom a ω 0 = a := by simp [trajectoryFrom]

lemma trajectoryFrom_succ (a : Point) (ω : StepPath) (n : ℕ) :
    trajectoryFrom a ω (n + 1) = trajectoryFrom a ω n + directionVector (ω n) := by
  rw [trajectoryFrom, trajectoryFrom, trajectory_succ]
  abel

lemma trajectoryFrom_eq_add_trajectory (a : Point) (ω : StepPath) (n : ℕ) :
    trajectoryFrom a ω n = a + trajectory ω n := by
  rfl

lemma measurable_trajectoryFrom (a : Point) : Measurable (trajectoryFrom a) := by
  apply measurable_pi_lambda
  intro n
  change Measurable fun ω : StepPath ↦
    (a.1 + (trajectory ω n).1, a.2 + (trajectory ω n).2)
  have htraj : Measurable (fun ω : StepPath ↦ trajectory ω n) :=
    (measurable_pi_apply n).comp measurable_trajectory
  exact (measurable_const.add htraj.fst).prodMk (measurable_const.add htraj.snd)

/-- The law of planar simple random walk started from `a`. -/
noncomputable def simpleRandomWalkFrom (a : Point) : Measure WalkPath :=
  fairSteps.map (trajectoryFrom a)

noncomputable instance (a : Point) : IsProbabilityMeasure (simpleRandomWalkFrom a) := by
  unfold simpleRandomWalkFrom
  exact Measure.isProbabilityMeasure_map (measurable_trajectoryFrom a).aemeasurable

/-! ## Exact finite-prefix probabilities -/

/-- The event that the first `n` increments agree with `ω₀`. -/
def stepCylinder (ω₀ : StepPath) (n : ℕ) : Set StepPath :=
  Set.pi (Finset.range n) fun j ↦ {ω₀ j}

lemma measurableSet_stepCylinder (ω₀ : StepPath) (n : ℕ) :
    MeasurableSet (stepCylinder ω₀ n) := by
  exact MeasurableSet.pi (Finset.range n).countable_toSet fun _ _ ↦ MeasurableSet.singleton _

lemma mem_stepCylinder_iff (ω ω₀ : StepPath) (n : ℕ) :
    ω ∈ stepCylinder ω₀ n ↔ ∀ j < n, ω j = ω₀ j := by
  simp [stepCylinder]

/-- Every prescribed length-`n` increment word has probability exactly `4⁻ⁿ`. -/
theorem fairSteps_stepCylinder (ω₀ : StepPath) (n : ℕ) :
    fairSteps (stepCylinder ω₀ n) = (4 : ℝ≥0∞)⁻¹ ^ n := by
  rw [fairSteps, stepCylinder, Measure.infinitePi_pi]
  · simp [fairStep_singleton]
  · intro i hi
    exact MeasurableSet.singleton _

/-- The event that a path agrees with `s₀` through time `n`, inclusive. -/
def walkCylinder (s₀ : WalkPath) (n : ℕ) : Set WalkPath :=
  Set.pi (Finset.range (n + 1)) fun j ↦ {s₀ j}

lemma measurableSet_walkCylinder (s₀ : WalkPath) (n : ℕ) :
    MeasurableSet (walkCylinder s₀ n) := by
  exact MeasurableSet.pi (Finset.range (n + 1)).countable_toSet
    fun _ _ ↦ MeasurableSet.singleton _

lemma mem_walkCylinder_iff (s s₀ : WalkPath) (n : ℕ) :
    s ∈ walkCylinder s₀ n ↔ ∀ j ≤ n, s j = s₀ j := by
  simp only [walkCylinder, Set.mem_pi, Finset.mem_coe, Finset.mem_range]
  constructor
  · intro h j hj
    exact h j (Nat.lt_succ_iff.mpr hj)
  · intro h j hj
    exact h j (Nat.le_of_lt_succ hj)

lemma trajectory_mem_walkCylinder_iff (ω ω₀ : StepPath) (n : ℕ) :
    trajectory ω ∈ walkCylinder (trajectory ω₀) n ↔ ω ∈ stepCylinder ω₀ n := by
  rw [mem_walkCylinder_iff, mem_stepCylinder_iff]
  constructor
  · intro h j hj
    have hsucc := h (j + 1) (Nat.succ_le_iff.mpr hj)
    have hprev := h j (Nat.le_trans (Nat.le_succ j) (Nat.succ_le_iff.mpr hj))
    rw [trajectory_succ, trajectory_succ, hprev] at hsucc
    exact directionVector_injective (add_left_cancel hsucc)
  · intro h j hj
    rw [trajectory]
    apply Finset.sum_congr rfl
    intro k hk
    rw [h k ((Finset.mem_range.mp hk).trans_le hj)]

/-- Every admissible walk prefix of length `n` has probability exactly `4⁻ⁿ`. -/
theorem simpleRandomWalk_walkCylinder (ω₀ : StepPath) (n : ℕ) :
    simpleRandomWalk (walkCylinder (trajectory ω₀) n) = (4 : ℝ≥0∞)⁻¹ ^ n := by
  rw [simpleRandomWalk, Measure.map_apply measurable_trajectory
    (measurableSet_walkCylinder (trajectory ω₀) n)]
  have heq : trajectory ⁻¹' walkCylinder (trajectory ω₀) n = stepCylinder ω₀ n := by
    ext ω
    exact trajectory_mem_walkCylinder_iff ω ω₀ n
  rw [heq, fairSteps_stepCylinder]

/-! ## Translation and reflection symmetry -/

/-- Translate every point of a path by `a`. -/
def translatePath (a : Point) (s : WalkPath) : WalkPath := fun n ↦ a + s n

lemma measurable_translatePath (a : Point) : Measurable (translatePath a) := by
  apply measurable_pi_lambda
  intro n
  change Measurable fun s : WalkPath ↦ (a.1 + (s n).1, a.2 + (s n).2)
  have heval : Measurable (fun s : WalkPath ↦ s n) := measurable_pi_apply n
  exact (measurable_const.add heval.fst).prodMk (measurable_const.add heval.snd)

lemma translatePath_trajectory (a : Point) (ω : StepPath) :
    translatePath a (trajectory ω) = trajectoryFrom a ω := by
  funext n
  exact (trajectoryFrom_eq_add_trajectory a ω n).symm

/-- Starting at `a` is precisely translating the origin-started path law by `a`. -/
theorem simpleRandomWalkFrom_eq_map_translatePath (a : Point) :
    simpleRandomWalkFrom a = simpleRandomWalk.map (translatePath a) := by
  rw [simpleRandomWalkFrom, simpleRandomWalk,
    Measure.map_map (measurable_translatePath a) measurable_trajectory]
  congr 1

/-- Reverse each of the four increments. -/
def reverseDirection : Direction → Direction := ![1, 0, 3, 2]

@[simp] lemma reverseDirection_involutive : Function.Involutive reverseDirection := by
  intro d
  fin_cases d <;> rfl

lemma reverseDirection_bijective : Function.Bijective reverseDirection :=
  reverseDirection_involutive.bijective

lemma directionVector_reverseDirection (d : Direction) :
    directionVector (reverseDirection d) = -directionVector d := by
  fin_cases d <;> decide

/-- Reverse every increment. -/
def reverseSteps (ω : StepPath) : StepPath := fun n ↦ reverseDirection (ω n)

lemma measurable_reverseSteps : Measurable reverseSteps := by
  apply measurable_pi_lambda
  intro n
  exact (measurable_of_countable reverseDirection).comp (measurable_pi_apply n)

/-- Reflect every point through the origin. -/
def reflectPath (s : WalkPath) : WalkPath := fun n ↦ -s n

lemma measurable_reflectPath : Measurable reflectPath := by
  apply measurable_pi_lambda
  intro n
  change Measurable fun s : WalkPath ↦ (-((s n).1), -((s n).2))
  have heval : Measurable (fun s : WalkPath ↦ s n) := measurable_pi_apply n
  exact heval.fst.neg.prodMk heval.snd.neg

lemma trajectory_reverseSteps (ω : StepPath) :
    trajectory (reverseSteps ω) = reflectPath (trajectory ω) := by
  funext n
  simp only [trajectory, reverseSteps, reflectPath,
    directionVector_reverseDirection]
  rw [Finset.sum_neg_distrib]

lemma fairStep_map_reverseDirection : fairStep.map reverseDirection = fairStep := by
  refine Measure.ext_of_singleton fun d ↦ ?_
  rw [Measure.map_apply (measurable_of_countable _) (MeasurableSet.singleton _)]
  have hpre : reverseDirection ⁻¹' ({d} : Set Direction) = {reverseDirection d} := by
    ext e
    constructor
    · intro he
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at he ⊢
      rw [← reverseDirection_involutive e, he]
    · intro he
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at he ⊢
      rw [he, reverseDirection_involutive]
  rw [hpre, fairStep_singleton, fairStep_singleton]

theorem fairSteps_map_reverseSteps : fairSteps.map reverseSteps = fairSteps := by
  have hmap := Measure.infinitePi_map_pi
    (μ := fun _ : ℕ ↦ fairStep) (Y := fun _ : ℕ ↦ Direction)
    (f := fun _ : ℕ ↦ reverseDirection) (fun _ ↦ measurable_of_countable _)
  rw [fairSteps, show reverseSteps =
      (fun ω : StepPath ↦ fun n : ℕ ↦ reverseDirection (ω n)) by rfl, hmap]
  congr 1
  funext n
  exact fairStep_map_reverseDirection

/-- The origin-started path law is invariant under central reflection. -/
theorem simpleRandomWalk_map_reflectPath :
    simpleRandomWalk.map reflectPath = simpleRandomWalk := by
  rw [simpleRandomWalk, Measure.map_map measurable_reflectPath measurable_trajectory]
  have hcomp : reflectPath ∘ trajectory = trajectory ∘ reverseSteps := by
    funext ω
    exact (trajectory_reverseSteps ω).symm
  rw [hcomp, ← Measure.map_map measurable_trajectory measurable_reverseSteps,
    fairSteps_map_reverseSteps]

/-! ## Hitting times -/

/-- The coordinate process on canonical path space. -/
def coordinateProcess (n : ℕ) (s : WalkPath) : Point := s n

/-- The canonical filtration generated by coordinates through the current time. -/
def walkFiltration : Filtration ℕ (inferInstance : MeasurableSpace WalkPath) :=
  Filtration.piLE (X := fun _ : ℕ ↦ Point)

lemma coordinateProcess_adapted : Adapted walkFiltration coordinateProcess := by
  intro n
  rw [walkFiltration, Filtration.piLE_eq_comap_frestrictLe]
  apply Measurable.of_comap_le
  exact MeasurableSpace.comap_le_comap_of_eq_comp
    (fun u : ((i : Finset.Iic n) → Point) ↦ u ⟨n, by simp⟩)
    (measurable_pi_apply (⟨n, by simp⟩ : Finset.Iic n)) (by
      funext s
      rfl)

/-- The first time at or after time `0` at which a canonical path visits `x`. -/
noncomputable def firstHit (x : Point) : WalkPath → WithTop ℕ :=
  hittingAfter coordinateProcess {x} 0

/-- The first visit to `x` between times `0` and `N`, defaulting to `N` if absent. -/
noncomputable def firstHitBefore (x : Point) (N : ℕ) : WalkPath → ℕ :=
  hittingBtwn coordinateProcess {x} 0 N

theorem firstHit_isStoppingTime (x : Point) :
    IsStoppingTime walkFiltration (firstHit x) := by
  exact coordinateProcess_adapted.isStoppingTime_hittingAfter (MeasurableSet.singleton x)

theorem firstHitBefore_isStoppingTime (x : Point) (N : ℕ) :
    IsStoppingTime walkFiltration (fun s ↦ (firstHitBefore x N s : WithTop ℕ)) := by
  exact coordinateProcess_adapted.isStoppingTime_hittingBtwn (MeasurableSet.singleton x)

theorem firstHit_eq_top_iff (s : WalkPath) (x : Point) :
    firstHit x s = ⊤ ↔ ∀ n, s n ≠ x := by
  simp [firstHit, coordinateProcess, hittingAfter_eq_top_iff]

theorem firstHit_le_iff (s : WalkPath) (x : Point) (N : ℕ) :
    firstHit x s ≤ N ↔ ∃ n ≤ N, s n = x := by
  simpa [firstHit, coordinateProcess] using
    (hittingAfter_le_iff (u := coordinateProcess) (s := ({x} : Set Point))
      (n := 0) (i := N) (ω := s))

/-! ## Finite Green functions -/

lemma localTime_le (s : WalkPath) (n : ℕ) (x : Point) : localTime s n x ≤ n + 1 := by
  unfold localTime localTimePrefix
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

@[simp] lemma localTime_zero_origin (s : WalkPath) (hs : s 0 = 0) :
    0 < localTime s 0 0 := by
  rw [localTime, localTimePrefix, Finset.card_pos]
  exact ⟨0, by simp [pathPrefix, hs]⟩

/-- The finite-horizon Green function, i.e. expected local time. -/
noncomputable def finiteGreen (n : ℕ) (x : Point) : ℝ≥0∞ :=
  ∫⁻ s, (localTime s n x : ℝ≥0∞) ∂simpleRandomWalk

lemma finiteGreen_le (n : ℕ) (x : Point) : finiteGreen n x ≤ n + 1 := by
  rw [finiteGreen]
  calc
    (∫⁻ s, (localTime s n x : ℝ≥0∞) ∂simpleRandomWalk)
        ≤ ∫⁻ _s : WalkPath, (n + 1 : ℝ≥0∞) ∂simpleRandomWalk := by
          apply lintegral_mono
          intro s
          change (localTime s n x : ℝ≥0∞) ≤ (n + 1 : ℝ≥0∞)
          exact_mod_cast localTime_le s n x
    _ = n + 1 := by simp

lemma simpleRandomWalk_trajectory_zero :
    ∀ᵐ s ∂simpleRandomWalk, s 0 = 0 := by
  have hmeas : MeasurableSet {s : WalkPath | s 0 = 0} :=
    measurableSet_eq_fun (measurable_pi_apply 0) measurable_const
  apply (mem_ae_iff_prob_eq_one hmeas).mpr
  rw [simpleRandomWalk, Measure.map_apply measurable_trajectory hmeas]
  rw [show trajectory ⁻¹' {s : WalkPath | s 0 = 0} = Set.univ by
    ext ω
    simp [trajectory_zero]]
  exact measure_univ

lemma one_le_finiteGreen_origin (n : ℕ) : 1 ≤ finiteGreen n 0 := by
  rw [finiteGreen]
  calc
    (1 : ℝ≥0∞) = ∫⁻ _s : WalkPath, 1 ∂simpleRandomWalk := by simp
    _ ≤ ∫⁻ s, (localTime s n 0 : ℝ≥0∞) ∂simpleRandomWalk := by
      apply lintegral_mono_ae
      filter_upwards [simpleRandomWalk_trajectory_zero] with s hs
      exact_mod_cast (show 1 ≤ localTime s n 0 by
        rw [localTime, localTimePrefix, Finset.one_le_card]
        refine ⟨(0 : Fin (n + 1)), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        simpa [pathPrefix] using hs)

end PlanarPotential

end Erdos1165
