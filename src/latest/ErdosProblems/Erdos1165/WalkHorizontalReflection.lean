/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.Basic

/-!
# Horizontal reflection of planar simple random walk

The two column pairings used in the HLOZ six-pairing cover are exchanged by
reflection in the vertical axis.  This file records that symmetry at the path
and probability-law level.  Event-specific transport of column bases and
their partners belongs in the screening module.
-/

open MeasureTheory Set

namespace Erdos1165

/-- Reflection in the vertical axis. -/
def horizontalReflectPoint (x : Point) : Point := (-x.1, x.2)

/-- Apply vertical-axis reflection to every point of a path. -/
def horizontalReflectPath (s : WalkPath) : WalkPath :=
  fun n ↦ horizontalReflectPoint (s n)

/-- Reflect the horizontal directions and fix the vertical directions. -/
def horizontalReflectDirection : Direction → Direction
  | ⟨0, _⟩ => ⟨1, by omega⟩
  | ⟨1, _⟩ => ⟨0, by omega⟩
  | ⟨2, _⟩ => ⟨2, by omega⟩
  | ⟨3, _⟩ => ⟨3, by omega⟩

/-- Coordinatewise reflection of the increment sequence. -/
def horizontalReflectSteps (omega : StepPath) : StepPath :=
  fun n ↦ horizontalReflectDirection (omega n)

lemma measurable_horizontalReflectPoint : Measurable horizontalReflectPoint := by
  unfold horizontalReflectPoint
  fun_prop

lemma measurable_horizontalReflectPath : Measurable horizontalReflectPath := by
  unfold horizontalReflectPath
  fun_prop

lemma measurable_horizontalReflectDirection :
    Measurable horizontalReflectDirection := measurable_of_countable _

lemma measurable_horizontalReflectSteps : Measurable horizontalReflectSteps := by
  unfold horizontalReflectSteps
  fun_prop

@[simp] lemma horizontalReflectPoint_involutive (x : Point) :
    horizontalReflectPoint (horizontalReflectPoint x) = x := by
  rcases x with ⟨x₁, x₂⟩
  simp [horizontalReflectPoint]

@[simp] lemma horizontalReflectDirection_involutive (d : Direction) :
    horizontalReflectDirection (horizontalReflectDirection d) = d := by
  fin_cases d <;> rfl

@[simp] lemma horizontalReflectPath_involutive (s : WalkPath) :
    horizontalReflectPath (horizontalReflectPath s) = s := by
  funext n
  exact horizontalReflectPoint_involutive (s n)

lemma directionVector_horizontalReflectDirection (d : Direction) :
    directionVector (horizontalReflectDirection d) =
      horizontalReflectPoint (directionVector d) := by
  fin_cases d <;> rfl

lemma horizontalReflectPoint_add (x y : Point) :
    horizontalReflectPoint (x + y) =
      horizontalReflectPoint x + horizontalReflectPoint y := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  change (-(x₁ + y₁), x₂ + y₂) =
    (-x₁ + -y₁, x₂ + y₂)
  apply Prod.ext
  · omega
  · rfl

/-- Reflecting all increments reflects the resulting trajectory. -/
lemma horizontalReflectPath_trajectory (omega : StepPath) :
    horizontalReflectPath (trajectory omega) =
      trajectory (horizontalReflectSteps omega) := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
      change horizontalReflectPoint (trajectory omega n) =
        trajectory (horizontalReflectSteps omega) n at ih
      change horizontalReflectPoint (trajectory omega (n + 1)) =
        trajectory (horizontalReflectSteps omega) (n + 1)
      rw [trajectory_succ, trajectory_succ]
      change horizontalReflectPoint
          (trajectory omega n + directionVector (omega n)) =
        trajectory (horizontalReflectSteps omega) n +
          directionVector (horizontalReflectDirection (omega n))
      rw [horizontalReflectPoint_add, ih,
        directionVector_horizontalReflectDirection]

/-- The uniform one-step law is invariant under horizontal reflection. -/
theorem fairStep_map_horizontalReflectDirection :
    fairStep.map horizontalReflectDirection = fairStep := by
  apply Measure.ext_of_singleton
  intro d
  rw [Measure.map_apply measurable_horizontalReflectDirection
    (measurableSet_singleton d)]
  have hpre : horizontalReflectDirection ⁻¹' ({d} : Set Direction) =
      {horizontalReflectDirection d} := by
    ext e
    constructor
    · intro he
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at he ⊢
      rw [← he, horizontalReflectDirection_involutive]
    · intro he
      simp only [Set.mem_singleton_iff] at he
      subst e
      simp
  rw [hpre, fairStep_singleton, fairStep_singleton]

/-- The IID increment law is invariant under coordinatewise reflection. -/
theorem fairSteps_map_horizontalReflectSteps :
    fairSteps.map horizontalReflectSteps = fairSteps := by
  have hmap := Measure.infinitePi_map_pi
    (μ := fun _ : ℕ ↦ fairStep) (Y := fun _ : ℕ ↦ Direction)
    (f := fun _ : ℕ ↦ horizontalReflectDirection)
    (fun _ ↦ measurable_horizontalReflectDirection)
  rw [fairSteps, show horizontalReflectSteps =
      (fun omega : StepPath ↦ fun n : ℕ ↦
        horizontalReflectDirection (omega n)) by rfl, hmap]
  congr 1
  funext n
  exact fairStep_map_horizontalReflectDirection

/-- The origin-started planar simple-random-walk law is invariant under
reflection in the vertical axis. -/
theorem simpleRandomWalk_map_horizontalReflectPath :
    simpleRandomWalk.map horizontalReflectPath = simpleRandomWalk := by
  calc
    simpleRandomWalk.map horizontalReflectPath =
        fairSteps.map (horizontalReflectPath ∘ trajectory) := by
      rw [simpleRandomWalk, Measure.map_map measurable_horizontalReflectPath
        measurable_trajectory]
    _ = fairSteps.map (trajectory ∘ horizontalReflectSteps) := by
      congr 1
      funext omega
      exact horizontalReflectPath_trajectory omega
    _ = (fairSteps.map horizontalReflectSteps).map trajectory := by
      rw [Measure.map_map measurable_trajectory
        measurable_horizontalReflectSteps]
    _ = fairSteps.map trajectory := by
      rw [fairSteps_map_horizontalReflectSteps]
    _ = simpleRandomWalk := rfl

/-- A measurable event and its horizontal-reflection preimage have the same
simple-random-walk probability. -/
theorem simpleRandomWalk_preimage_horizontalReflectPath
    {A : Set WalkPath} (hA : MeasurableSet A) :
    simpleRandomWalk (horizontalReflectPath ⁻¹' A) = simpleRandomWalk A := by
  rw [← Measure.map_apply_of_aemeasurable
      measurable_horizontalReflectPath.aemeasurable hA,
    simpleRandomWalk_map_horizontalReflectPath]

end Erdos1165
