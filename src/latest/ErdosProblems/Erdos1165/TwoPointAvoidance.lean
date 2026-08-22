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

import ErdosProblems.Erdos1165.PlanarPotential

/-!
# A finite uniform two-point avoidance bound

Hao--Li--Okada--Zheng use the scale-uniform planar estimate
`inf_x P(H_{\{0,x\}} >= n) \asymp 1 / log n`.  Its proof depends on the
logarithmic asymptotic of the planar potential kernel, which is not currently
available in Mathlib or in the preceding files of this development.

This file proves, without any analytic hypothesis, a weaker but genuinely
uniform finite-horizon substitute.  Given the second forbidden point `x`,
choose a cardinal direction whose directed coordinate is nonpositive at `x`.
Force the first step to be in that direction and forbid the opposite step
thereafter.  The directed coordinate then stays strictly positive, so neither
`0` nor `x` can be visited.  The resulting cylinder has exact probability

`(1 / 4) * (3 / 4) ^ (n - 1)`

through a positive horizon `n`.  This is exponentially smaller than the HLOZ
bound and therefore does not replace the missing potential-kernel estimate in
the proof of the favorite-site theorem.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165
namespace TwoPointAvoidance

open PlanarPotential

/-! ## A directed lattice coordinate -/

/-- Coordinate in a cardinal direction: east, west, north, or south. -/
def directedCoordinate : Direction → Point → ℤ
  | ⟨0, _⟩, x => x.1
  | ⟨1, _⟩, x => -x.1
  | ⟨2, _⟩, x => x.2
  | ⟨3, _⟩, x => -x.2

@[simp] lemma directedCoordinate_zero (d : Direction) :
    directedCoordinate d (0 : Point) = 0 := by
  fin_cases d <;> rfl

lemma directedCoordinate_add (d : Direction) (x y : Point) :
    directedCoordinate d (x + y) = directedCoordinate d x + directedCoordinate d y := by
  fin_cases d <;> simp [directedCoordinate, add_comm]

lemma directedCoordinate_sum (d : Direction) (A : Finset ℕ) (f : ℕ → Point) :
    directedCoordinate d (∑ j ∈ A, f j) = ∑ j ∈ A, directedCoordinate d (f j) := by
  fin_cases d <;> simp [directedCoordinate, Prod.fst_sum, Prod.snd_sum]

@[simp] lemma directedCoordinate_directionVector_self (d : Direction) :
    directedCoordinate d (directionVector d) = 1 := by
  fin_cases d <;> rfl

lemma directedCoordinate_directionVector_nonneg_of_ne_reverse
    (d e : Direction) (h : e ≠ reverseDirection d) :
    0 ≤ directedCoordinate d (directionVector e) := by
  fin_cases d <;> fin_cases e <;> simp_all [directedCoordinate, reverseDirection,
    directionVector]

/-- Every point lies in the closed nonpositive half-space for at least one
cardinal directed coordinate. -/
lemma exists_direction_directedCoordinate_nonpos (x : Point) :
    ∃ d : Direction, directedCoordinate d x ≤ 0 := by
  by_cases hx : x.1 ≤ 0
  · exact ⟨0, by simpa [directedCoordinate]⟩
  · refine ⟨1, ?_⟩
    simp only [directedCoordinate]
    omega

/-! ## The monotone half-space cylinder -/

/-- At time zero force direction `d`; at every later constrained time forbid
the opposite direction. -/
def monotoneRayRestriction (d : Direction) (j : ℕ) : Set Direction :=
  if j = 0 then {d} else ({reverseDirection d} : Set Direction)ᶜ

/-- The finite increment cylinder used for the avoidance lower bound. -/
def monotoneRayCylinder (d : Direction) (n : ℕ) : Set StepPath :=
  Set.pi (Finset.range n) (monotoneRayRestriction d)

lemma measurableSet_monotoneRayCylinder (d : Direction) (n : ℕ) :
    MeasurableSet (monotoneRayCylinder d n) := by
  exact MeasurableSet.pi (Finset.range n).countable_toSet fun j _ ↦ by
    by_cases hj : j = 0
    · simp [monotoneRayRestriction, hj]
    · simp [monotoneRayRestriction, hj]

lemma mem_monotoneRayCylinder_iff (d : Direction) (n : ℕ) (omega : StepPath) :
    omega ∈ monotoneRayCylinder d n ↔
      ∀ j < n, omega j ∈ monotoneRayRestriction d j := by
  simp [monotoneRayCylinder]

lemma fairStep_compl_singleton (d : Direction) :
    fairStep ({d} : Set Direction)ᶜ = 3 / 4 := by
  rw [measure_compl (MeasurableSet.singleton d) (by simp [fairStep_singleton])]
  rw [measure_univ, fairStep_singleton]
  apply ENNReal.sub_eq_of_eq_add (by norm_num)
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num

/-- Exact mass of the explicit half-space cylinder. -/
theorem fairSteps_monotoneRayCylinder (d : Direction) (n : ℕ) :
    fairSteps (monotoneRayCylinder d (n + 1)) =
      (1 / 4 : ℝ≥0∞) * (3 / 4 : ℝ≥0∞) ^ n := by
  rw [fairSteps, monotoneRayCylinder, Measure.infinitePi_pi]
  · rw [Finset.prod_range_succ']
    have hzero : fairStep (monotoneRayRestriction d 0) = (1 / 4 : ℝ≥0∞) := by
      rw [show monotoneRayRestriction d 0 = ({d} : Set Direction) by
        simp [monotoneRayRestriction]]
      exact fairStep_singleton d
    have hsucc (j : ℕ) :
        fairStep (monotoneRayRestriction d (j + 1)) = (3 / 4 : ℝ≥0∞) := by
      rw [show monotoneRayRestriction d (j + 1) =
          ({reverseDirection d} : Set Direction)ᶜ by
        simp [monotoneRayRestriction]]
      exact fairStep_compl_singleton (reverseDirection d)
    rw [hzero]
    simp_rw [hsucc]
    simp only [Finset.prod_const, Finset.card_range]
    exact mul_comm _ _
  · intro j hj
    by_cases hj0 : j = 0
    · simp [monotoneRayRestriction, hj0]
    · simp [monotoneRayRestriction, hj0]

/-! ## Cylinder paths avoid two prescribed points -/

/-- The walk avoids both the origin and `x` at every strictly positive time
through `n`.  Time zero is intentionally excluded, as in the positive hitting
time convention used by HLOZ. -/
def avoidsTwoPointsThrough (x : Point) (n : ℕ) : Set StepPath :=
  {omega | ∀ k, 0 < k → k ≤ n →
    trajectory omega k ≠ (0 : Point) ∧ trajectory omega k ≠ x}

/-- The same finite avoidance event on canonical path space. -/
def walkAvoidsTwoPointsThrough (x : Point) (n : ℕ) : Set WalkPath :=
  {s | ∀ k, 0 < k → k ≤ n → s k ≠ (0 : Point) ∧ s k ≠ x}

lemma measurableSet_walkAvoidsTwoPointsThrough (x : Point) (n : ℕ) :
    MeasurableSet (walkAvoidsTwoPointsThrough x n) := by
  unfold walkAvoidsTwoPointsThrough
  measurability

lemma avoidsTwoPointsThrough_eq_preimage (x : Point) (n : ℕ) :
    avoidsTwoPointsThrough x n =
      trajectory ⁻¹' walkAvoidsTwoPointsThrough x n := by
  rfl

lemma directedCoordinate_trajectory (d : Direction) (omega : StepPath) (k : ℕ) :
    directedCoordinate d (trajectory omega k) =
      ∑ j ∈ Finset.range k, directedCoordinate d (directionVector (omega j)) := by
  exact directedCoordinate_sum d (Finset.range k) (fun j ↦ directionVector (omega j))

lemma directedCoordinate_trajectory_pos_of_mem_monotoneRayCylinder
    (d : Direction) (omega : StepPath) (n k : ℕ)
    (homega : omega ∈ monotoneRayCylinder d (n + 1))
    (hkpos : 0 < k) (hkn : k ≤ n + 1) :
    0 < directedCoordinate d (trajectory omega k) := by
  rw [directedCoordinate_trajectory]
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hkpos
  rw [show Nat.succ 0 + q = q + 1 by omega]
  rw [Finset.sum_range_succ']
  have hmem := (mem_monotoneRayCylinder_iff d (n + 1) omega).mp homega
  have hzero : omega 0 = d := by
    simpa [monotoneRayRestriction] using hmem 0 (by omega)
  rw [hzero, directedCoordinate_directionVector_self]
  have hnonneg :
      0 ≤ ∑ j ∈ Finset.range q,
        directedCoordinate d (directionVector (omega (j + 1))) := by
    apply Finset.sum_nonneg
    intro j hj
    have hjq : j < q := Finset.mem_range.mp hj
    have hnot : omega (j + 1) ≠ reverseDirection d := by
      have hm := hmem (j + 1) (by omega)
      simpa [monotoneRayRestriction] using hm
    exact directedCoordinate_directionVector_nonneg_of_ne_reverse d (omega (j + 1)) hnot
  omega

lemma monotoneRayCylinder_subset_avoidsTwoPointsThrough
    (x : Point) (d : Direction) (n : ℕ) (hxd : directedCoordinate d x ≤ 0) :
    monotoneRayCylinder d (n + 1) ⊆ avoidsTwoPointsThrough x (n + 1) := by
  intro omega homega k hkpos hkn
  have hpositive := directedCoordinate_trajectory_pos_of_mem_monotoneRayCylinder
    d omega n k homega hkpos hkn
  constructor
  · intro hzero
    rw [hzero, directedCoordinate_zero] at hpositive
    omega
  · intro hx
    rw [hx] at hpositive
    omega

/-- A completely proved finite substitute for the HLOZ uniform two-point
avoidance estimate.  It is uniform in the second forbidden point, but has
exponential rather than logarithmic scale. -/
theorem fairSteps_avoidsTwoPointsThrough_lower (x : Point) (n : ℕ) :
    (1 / 4 : ℝ≥0∞) * (3 / 4 : ℝ≥0∞) ^ n ≤
      fairSteps (avoidsTwoPointsThrough x (n + 1)) := by
  obtain ⟨d, hd⟩ := exists_direction_directedCoordinate_nonpos x
  rw [← fairSteps_monotoneRayCylinder d n]
  exact measure_mono (monotoneRayCylinder_subset_avoidsTwoPointsThrough x d n hd)

/-- Path-space version of `fairSteps_avoidsTwoPointsThrough_lower`, for the
canonical planar-walk law used in the statement of Erdős Problem 1165. -/
theorem simpleRandomWalk_walkAvoidsTwoPointsThrough_lower (x : Point) (n : ℕ) :
    (1 / 4 : ℝ≥0∞) * (3 / 4 : ℝ≥0∞) ^ n ≤
      simpleRandomWalk (walkAvoidsTwoPointsThrough x (n + 1)) := by
  rw [simpleRandomWalk, Measure.map_apply measurable_trajectory
    (measurableSet_walkAvoidsTwoPointsThrough x (n + 1))]
  rw [← avoidsTwoPointsThrough_eq_preimage]
  exact fairSteps_avoidsTwoPointsThrough_lower x n

end TwoPointAvoidance
end Erdos1165
