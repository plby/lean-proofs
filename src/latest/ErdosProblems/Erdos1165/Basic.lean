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
# Basic objects for Erdős Problem 1165

This file constructs the canonical planar simple symmetric random walk, its
finite-prefix local times and favorite sites, and the measurable
infinitely-often events used by the main theorem.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165

/-! ## The canonical planar simple random walk -/

/-- The four equiprobable directions of planar simple random walk. -/
abbrev Direction := Fin 4

/-- Lattice points are represented by pairs of integers. -/
abbrev Point := ℤ × ℤ

/-- A sequence of independent directions. -/
abbrev StepPath := ℕ → Direction

/-- A path in the integer lattice. -/
abbrev WalkPath := ℕ → Point

/-- The lattice displacement belonging to one direction. -/
def directionVector : Direction → Point
  | ⟨0, _⟩ => (1, 0)
  | ⟨1, _⟩ => (-1, 0)
  | ⟨2, _⟩ => (0, 1)
  | ⟨3, _⟩ => (0, -1)

lemma measurable_directionVector : Measurable directionVector := measurable_of_countable _

lemma directionVector_injective : Function.Injective directionVector := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [directionVector]

/-- The uniform law on the four directions. -/
noncomputable def fairStep : Measure Direction :=
  ProbabilityTheory.uniformOn Set.univ

noncomputable instance : IsProbabilityMeasure fairStep := by
  unfold fairStep
  infer_instance

@[simp] lemma fairStep_singleton (d : Direction) : fairStep {d} = 1 / 4 := by
  rw [fairStep, uniformOn_univ]
  norm_num

/-- The IID product law of all increments. -/
noncomputable def fairSteps : Measure StepPath :=
  Measure.infinitePi fun _ : ℕ ↦ fairStep

noncomputable instance : IsProbabilityMeasure fairSteps := by
  unfold fairSteps
  infer_instance

lemma fairSteps_eval (n : ℕ) : fairSteps.map (fun ω ↦ ω n) = fairStep := by
  exact Measure.infinitePi_map_eval (fun _ : ℕ ↦ fairStep) n

lemma fairSteps_independent : iIndepFun (fun n (ω : StepPath) ↦ ω n) fairSteps := by
  exact iIndepFun_infinitePi (P := fun _ : ℕ ↦ fairStep) fun _ ↦ measurable_id

/-- The trajectory determined by an increment sequence.  Time `0` is the origin
and the position at time `n` is the sum of the first `n` increments. -/
def trajectory (ω : StepPath) (n : ℕ) : Point :=
  ∑ j ∈ Finset.range n, directionVector (ω j)

@[simp] lemma trajectory_zero (ω : StepPath) : trajectory ω 0 = (0, 0) := by
  rfl

lemma trajectory_succ (ω : StepPath) (n : ℕ) :
    trajectory ω (n + 1) = trajectory ω n + directionVector (ω n) := by
  simp [trajectory, Finset.sum_range_succ]

lemma trajectory_increment (ω : StepPath) (n : ℕ) :
    trajectory ω (n + 1) - trajectory ω n = directionVector (ω n) := by
  rw [trajectory_succ]
  abel

lemma measurable_trajectory : Measurable trajectory := by
  apply measurable_pi_lambda
  intro n
  unfold trajectory
  fun_prop

/-- The law of planar simple symmetric random walk, as a measure on lattice-valued paths. -/
noncomputable def simpleRandomWalk : Measure WalkPath :=
  fairSteps.map trajectory

noncomputable instance : IsProbabilityMeasure simpleRandomWalk := by
  unfold simpleRandomWalk
  exact Measure.isProbabilityMeasure_map measurable_trajectory.aemeasurable

lemma simpleRandomWalk_starts_at_origin :
    ∀ᵐ s ∂simpleRandomWalk, s 0 = (0, 0) := by
  rw [simpleRandomWalk, ae_map_iff measurable_trajectory.aemeasurable
    (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const)]
  exact Filter.Eventually.of_forall trajectory_zero

lemma simpleRandomWalk_increment_map (n : ℕ) :
    simpleRandomWalk.map (fun s : WalkPath ↦ s (n + 1) - s n) =
      fairStep.map directionVector := by
  calc
    simpleRandomWalk.map (fun s : WalkPath ↦ s (n + 1) - s n) =
        fairSteps.map ((fun s : WalkPath ↦ s (n + 1) - s n) ∘ trajectory) := by
      rw [simpleRandomWalk, Measure.map_map (by fun_prop) measurable_trajectory]
    _ = fairSteps.map (directionVector ∘ fun ω : StepPath ↦ ω n) := by
      congr 1
      funext ω
      exact trajectory_increment ω n
    _ = (fairSteps.map (fun ω : StepPath ↦ ω n)).map directionVector := by
      rw [Measure.map_map measurable_directionVector (by fun_prop)]
    _ = fairStep.map directionVector := by rw [fairSteps_eval]

lemma simpleRandomWalk_each_increment (n : ℕ) (d : Direction) :
    simpleRandomWalk {s | s (n + 1) - s n = directionVector d} = 1 / 4 := by
  have hinc : Measurable (fun s : WalkPath ↦ s (n + 1) - s n) := by fun_prop
  have hsingle : MeasurableSet ({directionVector d} : Set Point) := measurableSet_singleton _
  change simpleRandomWalk ((fun s : WalkPath ↦ s (n + 1) - s n) ⁻¹'
    {directionVector d}) = 1 / 4
  rw [← Measure.map_apply_of_aemeasurable hinc.aemeasurable hsingle,
    simpleRandomWalk_increment_map]
  rw [Measure.map_apply_of_aemeasurable measurable_directionVector.aemeasurable hsingle]
  have hpre : directionVector ⁻¹' {directionVector d} = {d} := by
    ext e
    simp [directionVector_injective.eq_iff]
  rw [hpre, fairStep_singleton]

/-! ## Local time and favorite sites -/

/-- The finite path prefix through time `n`, including both times `0` and `n`. -/
def pathPrefix (s : WalkPath) (n : ℕ) : Fin (n + 1) → Point :=
  fun j ↦ s j

/-- The local time of `x` in a finite prefix. -/
def localTimePrefix {n : ℕ} (u : Fin (n + 1) → Point) (x : Point) : ℕ :=
  (Finset.univ.filter fun j ↦ u j = x).card

/-- The finite set of sites visited by a prefix. -/
def visitedPrefix {n : ℕ} (u : Fin (n + 1) → Point) : Finset Point :=
  Finset.univ.image u

/-- The maximal local time in a finite prefix. -/
def maxLocalTimePrefix {n : ℕ} (u : Fin (n + 1) → Point) : ℕ :=
  (visitedPrefix u).sup (localTimePrefix u)

/-- The favorite sites of a finite prefix. -/
def favoritePrefix {n : ℕ} (u : Fin (n + 1) → Point) : Finset Point :=
  (visitedPrefix u).filter fun x ↦ localTimePrefix u x = maxLocalTimePrefix u

/-- The local time of a path at a site, counting times `0, ..., n`. -/
def localTime (s : WalkPath) (n : ℕ) (x : Point) : ℕ :=
  localTimePrefix (pathPrefix s n) x

/-- The finite range of a path through time `n`. -/
def visitedSites (s : WalkPath) (n : ℕ) : Finset Point :=
  visitedPrefix (pathPrefix s n)

/-- The maximal local time of a path through time `n`. -/
def maxLocalTime (s : WalkPath) (n : ℕ) : ℕ :=
  maxLocalTimePrefix (pathPrefix s n)

/-- The set of favorite sites at time `n`. -/
def favoriteSites (s : WalkPath) (n : ℕ) : Finset Point :=
  favoritePrefix (pathPrefix s n)

/-- The number of favorite sites at time `n`. -/
def favoriteCount (s : WalkPath) (n : ℕ) : ℕ :=
  (favoriteSites s n).card

lemma mem_visitedPrefix_iff {n : ℕ} {u : Fin (n + 1) → Point} {x : Point} :
    x ∈ visitedPrefix u ↔ ∃ j, u j = x := by
  simp [visitedPrefix]

lemma visitedPrefix_nonempty {n : ℕ} (u : Fin (n + 1) → Point) :
    (visitedPrefix u).Nonempty := by
  exact ⟨u 0, by simp [visitedPrefix]⟩

lemma localTimePrefix_pos_of_mem_visited {n : ℕ} {u : Fin (n + 1) → Point} {x : Point}
    (hx : x ∈ visitedPrefix u) : 0 < localTimePrefix u x := by
  rw [mem_visitedPrefix_iff] at hx
  obtain ⟨j, rfl⟩ := hx
  rw [localTimePrefix, Finset.card_pos]
  exact ⟨j, by simp⟩

lemma localTimePrefix_eq_zero_of_notMem_visited {n : ℕ}
    {u : Fin (n + 1) → Point} {x : Point} (hx : x ∉ visitedPrefix u) :
    localTimePrefix u x = 0 := by
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro j _ hj
  apply hx
  exact mem_visitedPrefix_iff.mpr ⟨j, hj⟩

lemma localTimePrefix_le_maxLocalTimePrefix {n : ℕ}
    (u : Fin (n + 1) → Point) {x : Point} (hx : x ∈ visitedPrefix u) :
    localTimePrefix u x ≤ maxLocalTimePrefix u := by
  exact Finset.le_sup (f := localTimePrefix u) hx

lemma exists_mem_favoritePrefix {n : ℕ} (u : Fin (n + 1) → Point) :
    ∃ x, x ∈ favoritePrefix u := by
  obtain ⟨x, hx, hmax⟩ :=
    Finset.exists_mem_eq_sup (visitedPrefix u) (visitedPrefix_nonempty u) (localTimePrefix u)
  refine ⟨x, ?_⟩
  rw [favoritePrefix, Finset.mem_filter]
  exact ⟨hx, hmax.symm⟩

lemma favoritePrefix_nonempty {n : ℕ} (u : Fin (n + 1) → Point) :
    (favoritePrefix u).Nonempty := by
  obtain ⟨x, hx⟩ := exists_mem_favoritePrefix u
  exact ⟨x, hx⟩

/-- The finite-prefix definition is exactly the global argmax definition from the problem. -/
theorem mem_favoriteSites_iff_forall (s : WalkPath) (n : ℕ) (x : Point) :
    x ∈ favoriteSites s n ↔ ∀ y : Point, localTime s n y ≤ localTime s n x := by
  constructor
  · intro hx y
    rw [favoriteSites, favoritePrefix] at hx
    obtain ⟨hxVisited, hxMax⟩ := Finset.mem_filter.mp hx
    by_cases hy : y ∈ visitedSites s n
    · change y ∈ visitedPrefix (pathPrefix s n) at hy
      change localTimePrefix (pathPrefix s n) y ≤ localTimePrefix (pathPrefix s n) x
      rw [hxMax]
      exact localTimePrefix_le_maxLocalTimePrefix (pathPrefix s n) hy
    · rw [localTime, localTimePrefix_eq_zero_of_notMem_visited hy]
      exact Nat.zero_le _
  · intro h
    have hxVisited : x ∈ visitedSites s n := by
      by_contra hx
      have hx0 : localTime s n x = 0 := localTimePrefix_eq_zero_of_notMem_visited hx
      obtain ⟨y, hy⟩ := visitedPrefix_nonempty (pathPrefix s n)
      have hypos : 0 < localTime s n y := localTimePrefix_pos_of_mem_visited hy
      exact (Nat.not_lt_of_ge (h y)) (by simpa [hx0] using hypos)
    rw [favoriteSites, favoritePrefix, Finset.mem_filter]
    refine ⟨hxVisited, ?_⟩
    apply Nat.le_antisymm
    · exact localTimePrefix_le_maxLocalTimePrefix (pathPrefix s n) hxVisited
    · apply Finset.sup_le
      intro y hy
      exact h y

lemma favoriteSites_nonempty (s : WalkPath) (n : ℕ) :
    (favoriteSites s n).Nonempty := favoritePrefix_nonempty (pathPrefix s n)

lemma favoriteCount_pos (s : WalkPath) (n : ℕ) : 0 < favoriteCount s n := by
  exact Finset.card_pos.mpr (favoriteSites_nonempty s n)

/-! ## Measurability and the infinitely-often event -/

lemma measurable_pathPrefix (n : ℕ) : Measurable fun s : WalkPath ↦ pathPrefix s n := by
  exact measurable_pi_lambda _ fun i ↦ measurable_pi_apply (i : ℕ)

lemma measurable_favoriteCount (n : ℕ) : Measurable fun s : WalkPath ↦ favoriteCount s n := by
  exact (measurable_of_countable
    (fun u : Fin (n + 1) → Point ↦ (favoritePrefix u).card)).comp (measurable_pathPrefix n)

/-- The event that exactly `r` favorite sites occur infinitely often. -/
def favoriteEvent (r : ℕ) : Set WalkPath :=
  {s | ∃ᶠ n in atTop, favoriteCount s n = r}

theorem mem_favoriteEvent_iff (s : WalkPath) (r : ℕ) :
    s ∈ favoriteEvent r ↔ ∃ᶠ n in atTop, favoriteCount s n = r := Iff.rfl

theorem mem_favoriteEvent_iff_infinite (s : WalkPath) (r : ℕ) :
    s ∈ favoriteEvent r ↔ Set.Infinite {n | favoriteCount s n = r} := by
  exact Nat.frequently_atTop_iff_infinite

lemma measurableSet_favoriteEvent (r : ℕ) : MeasurableSet (favoriteEvent r) := by
  rw [favoriteEvent, show {s : WalkPath | ∃ᶠ n in atTop, favoriteCount s n = r} =
      limsup (fun n ↦ {s | favoriteCount s n = r}) atTop by
        ext s
        change (∃ᶠ n in atTop, favoriteCount s n = r) ↔
          s ∈ limsup (fun n ↦ {s | favoriteCount s n = r}) atTop
        simp only [mem_limsup_iff_frequently_mem, mem_ofPred_eq]]
  exact MeasurableSet.measurableSet_limsup fun n ↦
    measurableSet_eq_fun (measurable_favoriteCount n) measurable_const

/-! ## The elementary pathwise content of the HLOZ limsup theorem -/

/-- The almost-sure conclusion of the planar theorem in a form tailored to
natural-valued favorite counts. -/
def HLOZConclusion (s : WalkPath) : Prop :=
  (∃ᶠ n in atTop, 3 ≤ favoriteCount s n) ∧
    ∀ᶠ n in atTop, favoriteCount s n ≤ 3

lemma hlozConclusion_three_frequently {s : WalkPath} (hs : HLOZConclusion s) :
    ∃ᶠ n in atTop, favoriteCount s n = 3 := by
  exact (hs.1.and_eventually hs.2).mono fun _ h ↦ Nat.le_antisymm h.2 h.1

lemma hlozConclusion_not_frequently_of_four_le {s : WalkPath} (hs : HLOZConclusion s)
    {r : ℕ} (hr : 4 ≤ r) : ¬∃ᶠ n in atTop, favoriteCount s n = r := by
  intro hfreq
  obtain ⟨n, hn, hle⟩ := hfreq.and_eventually hs.2 |>.exists
  omega

end Erdos1165
