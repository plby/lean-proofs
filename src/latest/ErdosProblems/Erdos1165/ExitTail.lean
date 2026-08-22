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

import ErdosProblems.Erdos1165.Annulus
import ErdosProblems.Erdos1165.Markov

/-!
# An exponential tail for exit from a finite coordinate box

This file proves a deliberately crude, but completely uniform, exit-time
estimate for planar simple random walk.  From any point of the box
`[-R,R]^2`, a run of `2R+1` eastward steps leaves the box.  Disjoint blocks of
increments are independent, and each such run has probability `4^-(2R+1)`.
Consequently the probability of remaining in the box for `q` blocks is at
most

`(1 - 4^-(2R+1))^q <= exp (-q * 4^-(2R+1))`.

No potential-kernel or recurrence estimate is used.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1165
namespace ExitTail

open Annulus

/-- The length of a block which is guaranteed to cross `[-R,R]` when every
increment in the block is eastward. -/
def escapeBlockLength (R : ℕ) : ℕ := 2 * R + 1

/-- The event that the walk started from `a` has not exited the coordinate box
through time `N`.  This is the tail event `{N < tau}`, written without an
infinite-valued hitting-time convention. -/
def staysInCoordinateBoxThrough (a : Point) (R N : ℕ) : Set StepPath :=
  {omega | ∀ k ≤ N, a + trajectory omega k ∈ coordinateBox R}

/-- Extend a finite increment word by eastward steps. -/
def extendStepPrefix {N : ℕ} (u : Fin N → Direction) : StepPath :=
  fun j => if hj : j < N then u ⟨j, hj⟩ else 0

lemma trajectory_extendStepPrefix (omega : StepPath) {k N : ℕ} (hk : k ≤ N) :
    trajectory (extendStepPrefix (stepPrefix N omega)) k = trajectory omega k := by
  unfold trajectory
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j < k := Finset.mem_range.mp hj
  have hjN : j < N := hjk.trans_le hk
  simp [extendStepPrefix, stepPrefix, hjN]

/-- The survival event depends only on the first `N` increments. -/
def survivalPrefixSet (a : Point) (R N : ℕ) : Set (Fin N → Direction) :=
  {u | extendStepPrefix u ∈ staysInCoordinateBoxThrough a R N}

lemma staysInCoordinateBoxThrough_eq_preimage (a : Point) (R N : ℕ) :
    staysInCoordinateBoxThrough a R N =
      stepPrefix N ⁻¹' survivalPrefixSet a R N := by
  ext omega
  constructor
  · intro homega k hk
    rw [trajectory_extendStepPrefix omega hk]
    exact homega k hk
  · intro homega k hk
    rw [← trajectory_extendStepPrefix omega hk]
    exact homega k hk

lemma measurableSet_staysInCoordinateBoxThrough (a : Point) (R N : ℕ) :
    MeasurableSet (staysInCoordinateBoxThrough a R N) := by
  rw [staysInCoordinateBoxThrough_eq_preimage]
  exact (measurable_stepPrefix N) (Set.to_countable _).measurableSet

lemma measurableSet_staysInCoordinateBoxThrough_incrementFiltration
    (a : Point) (R N : ℕ) :
    MeasurableSet[incrementFiltration N] (staysInCoordinateBoxThrough a R N) := by
  rw [incrementFiltration_apply, staysInCoordinateBoxThrough_eq_preimage]
  exact ⟨survivalPrefixSet a R N, (Set.to_countable _).measurableSet, rfl⟩

/-- The constant word consisting entirely of eastward increments. -/
def eastWord (L : ℕ) : Fin L → Direction := fun _ => 0

/-- A run of `L` eastward steps beginning at time `n`. -/
def eastBlock (n L : ℕ) : Set StepPath :=
  {omega | stepBlock n L omega = eastWord L}

lemma measurableSet_eastBlock (n L : ℕ) : MeasurableSet (eastBlock n L) := by
  exact measurableSet_eq_fun (measurable_stepBlock n L) measurable_const

/-- A block of `L` independent increments is all eastward with probability
exactly `4^-L`. -/
lemma fairBlock_eastWord (L : ℕ) :
    fairBlock L {eastWord L} = (4 : ℝ≥0∞)⁻¹ ^ L := by
  have hset : ({eastWord L} : Set (Fin L → Direction)) =
      Set.pi (Finset.univ : Finset (Fin L)) (fun _ => ({0} : Set Direction)) := by
    ext u
    simp [eastWord, funext_iff]
  rw [fairBlock, hset, Measure.infinitePi_pi]
  · simp [fairStep_singleton]
  · intro i hi
    exact MeasurableSet.singleton _

lemma fairBlock_not_eastWord (L : ℕ) :
    fairBlock L ({eastWord L} : Set (Fin L → Direction))ᶜ =
      1 - (4 : ℝ≥0∞)⁻¹ ^ L := by
  rw [measure_compl (MeasurableSet.singleton _) (by simp), measure_univ,
    fairBlock_eastWord]

/-- If the walk remains in the box for one more full block, that block cannot
consist entirely of eastward steps. -/
lemma stays_succBlock_subset (a : Point) (R q : ℕ) :
    staysInCoordinateBoxThrough a R (escapeBlockLength R * (q + 1)) ⊆
      staysInCoordinateBoxThrough a R (escapeBlockLength R * q) ∩
        (eastBlock (escapeBlockLength R * q) (escapeBlockLength R))ᶜ := by
  intro omega homega
  let L := escapeBlockLength R
  let n := L * q
  have hprefix : omega ∈ staysInCoordinateBoxThrough a R n := by
    intro k hk
    have hnle : n ≤ escapeBlockLength R * (q + 1) := by
      dsimp [n, L]
      exact Nat.mul_le_mul_left _ (Nat.le_succ q)
    exact homega k (hk.trans hnle)
  refine ⟨hprefix, ?_⟩
  intro heast
  have heast' : stepBlock n L omega = eastWord L := heast
  have hdisp : trajectory omega (n + L) - trajectory omega n = ((L : ℤ), 0) := by
    rw [trajectory_add_sub_trajectory]
    unfold trajectory shiftSteps
    calc
      (∑ j ∈ Finset.range L, directionVector (omega (n + j))) =
          ∑ _j ∈ Finset.range L, ((1, 0) : Point) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjL : j < L := Finset.mem_range.mp hj
        have hjzero : omega (n + j) = 0 := by
          have := congrFun heast' ⟨j, hjL⟩
          simpa [stepBlock, eastWord] using this
        simp [hjzero, directionVector]
      _ = ((L : ℤ), 0) := by simp
  have hnmem : a + trajectory omega n ∈ coordinateBox R := hprefix n le_rfl
  have hendmem : a + trajectory omega (n + L) ∈ coordinateBox R := by
    apply homega
    have heq : n + L = escapeBlockLength R * (q + 1) := by
      simp [n, L, Nat.mul_succ]
    exact heq.le
  rw [mem_coordinateBox] at hnmem hendmem
  have hcoord : (a + trajectory omega (n + L)).1 =
      (a + trajectory omega n).1 + (L : ℤ) := by
    have htraj : trajectory omega (n + L) = trajectory omega n + ((L : ℤ), 0) := by
      calc
        trajectory omega (n + L) =
            (trajectory omega (n + L) - trajectory omega n) + trajectory omega n := by
          rw [sub_add_cancel]
        _ = ((L : ℤ), 0) + trajectory omega n := by rw [hdisp]
        _ = trajectory omega n + ((L : ℤ), 0) := add_comm _ _
    rw [htraj]
    simp [add_assoc]
  have hxlow : -(R : ℤ) ≤ (a + trajectory omega n).1 := hnmem.1
  have hxupp : (a + trajectory omega (n + L)).1 ≤ (R : ℤ) := hendmem.2.1
  rw [hcoord] at hxupp
  have hL : (L : ℤ) = 2 * (R : ℤ) + 1 := by
    dsimp [L, escapeBlockLength]
  rw [hL] at hxupp
  omega

/-- The survival event through `q` blocks is independent of the next block,
and excluding the all-east word contributes the factor `1 - 4^-L`. -/
lemma fairSteps_stays_inter_not_eastBlock (a : Point) (R q : ℕ) :
    fairSteps
        (staysInCoordinateBoxThrough a R (escapeBlockLength R * q) ∩
          (eastBlock (escapeBlockLength R * q) (escapeBlockLength R))ᶜ) =
      fairSteps (staysInCoordinateBoxThrough a R (escapeBlockLength R * q)) *
        (1 - (4 : ℝ≥0∞)⁻¹ ^ escapeBlockLength R) := by
  let n := escapeBlockLength R * q
  let L := escapeBlockLength R
  have hind := (indepFun_stepPrefix_stepBlock n L).measure_inter_preimage_eq_mul
    (survivalPrefixSet a R n) ({eastWord L} : Set (Fin L → Direction))ᶜ
    (Set.to_countable _).measurableSet (MeasurableSet.singleton _).compl
  rw [staysInCoordinateBoxThrough_eq_preimage]
  change fairSteps
      (stepPrefix n ⁻¹' survivalPrefixSet a R n ∩
        stepBlock n L ⁻¹' ({eastWord L} : Set (Fin L → Direction))ᶜ) = _
  rw [hind]
  have hblock : fairSteps
      (stepBlock n L ⁻¹' ({eastWord L} : Set (Fin L → Direction))ᶜ) =
      fairBlock L ({eastWord L} : Set (Fin L → Direction))ᶜ := by
    rw [← fairSteps_map_stepBlock n L,
      Measure.map_apply (measurable_stepBlock n L) (MeasurableSet.singleton _).compl]
  rw [hblock, fairBlock_not_eastWord]

/-- **Uniform geometric exit tail.**  The bound is uniform in the starting
point `a`; if `a` is outside the box, the left side is simply zero. -/
theorem fairSteps_staysInCoordinateBoxThrough_le_geometric
    (a : Point) (R q : ℕ) :
    fairSteps
        (staysInCoordinateBoxThrough a R (escapeBlockLength R * q)) ≤
      (1 - (4 : ℝ≥0∞)⁻¹ ^ escapeBlockLength R) ^ q := by
  induction q with
  | zero =>
      have h := measure_mono (μ := fairSteps)
        (show staysInCoordinateBoxThrough a R (escapeBlockLength R * 0) ⊆ Set.univ from
          Set.subset_univ _)
      simpa using h
  | succ q ih =>
      calc
        fairSteps
            (staysInCoordinateBoxThrough a R (escapeBlockLength R * (q + 1))) ≤
            fairSteps
              (staysInCoordinateBoxThrough a R (escapeBlockLength R * q) ∩
                (eastBlock (escapeBlockLength R * q) (escapeBlockLength R))ᶜ) :=
          measure_mono (stays_succBlock_subset a R q)
        _ = fairSteps
              (staysInCoordinateBoxThrough a R (escapeBlockLength R * q)) *
                (1 - (4 : ℝ≥0∞)⁻¹ ^ escapeBlockLength R) :=
          fairSteps_stays_inter_not_eastBlock a R q
        _ ≤ (1 - (4 : ℝ≥0∞)⁻¹ ^ escapeBlockLength R) ^ q *
                (1 - (4 : ℝ≥0∞)⁻¹ ^ escapeBlockLength R) := by
          gcongr
        _ = (1 - (4 : ℝ≥0∞)⁻¹ ^ escapeBlockLength R) ^ (q + 1) := by
          rw [pow_succ]

/-- Real-valued form of the geometric tail. -/
theorem measureReal_staysInCoordinateBoxThrough_le_geometric
    (a : Point) (R q : ℕ) :
    fairSteps.real
        (staysInCoordinateBoxThrough a R (escapeBlockLength R * q)) ≤
      (1 - (4 : ℝ)⁻¹ ^ escapeBlockLength R) ^ q := by
  have h := ENNReal.toReal_mono (by finiteness)
    (fairSteps_staysInCoordinateBoxThrough_le_geometric a R q)
  have hp : (4 : ℝ≥0∞)⁻¹ ^ escapeBlockLength R ≤ 1 := by
    exact pow_le_one₀ (by positivity) (by norm_num)
  simpa [Measure.real, ENNReal.toReal_pow, ENNReal.toReal_sub_of_le hp (by simp)] using h

/-- **Uniform exponential exit tail.**  This is the form consumed by block
amplification arguments. -/
theorem measureReal_staysInCoordinateBoxThrough_le_exp
    (a : Point) (R q : ℕ) :
    fairSteps.real
        (staysInCoordinateBoxThrough a R (escapeBlockLength R * q)) ≤
      Real.exp (-(q : ℝ) * ((4 : ℝ)⁻¹ ^ escapeBlockLength R)) := by
  let p : ℝ := (4 : ℝ)⁻¹ ^ escapeBlockLength R
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    exact pow_le_one₀ (by positivity) (by norm_num)
  calc
    fairSteps.real
        (staysInCoordinateBoxThrough a R (escapeBlockLength R * q)) ≤
        (1 - p) ^ q := by
      simpa [p] using measureReal_staysInCoordinateBoxThrough_le_geometric a R q
    _ ≤ (Real.exp (-p)) ^ q := by
      exact pow_le_pow_left₀ (sub_nonneg.mpr hp1) (Real.one_sub_le_exp_neg p) q
    _ = Real.exp (-(q : ℝ) * p) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ = Real.exp (-(q : ℝ) * ((4 : ℝ)⁻¹ ^ escapeBlockLength R)) := by rfl

/-- The geometric tail at an arbitrary deterministic horizon, with the number
of complete escape blocks given by integer division. -/
theorem fairSteps_staysInCoordinateBoxThrough_le_geometric_div
    (a : Point) (R N : ℕ) :
    fairSteps (staysInCoordinateBoxThrough a R N) ≤
      (1 - (4 : ℝ≥0∞)⁻¹ ^ escapeBlockLength R) ^
        (N / escapeBlockLength R) := by
  have htime : escapeBlockLength R * (N / escapeBlockLength R) ≤ N := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self N (escapeBlockLength R)
  calc
    fairSteps (staysInCoordinateBoxThrough a R N) ≤
        fairSteps (staysInCoordinateBoxThrough a R
          (escapeBlockLength R * (N / escapeBlockLength R))) := by
      apply measure_mono
      intro omega homega k hk
      exact homega k (hk.trans htime)
    _ ≤ (1 - (4 : ℝ≥0∞)⁻¹ ^ escapeBlockLength R) ^
          (N / escapeBlockLength R) :=
      fairSteps_staysInCoordinateBoxThrough_le_geometric a R _

/-- Arbitrary-horizon real exponential form of the box exit tail. -/
theorem measureReal_staysInCoordinateBoxThrough_le_exp_div
    (a : Point) (R N : ℕ) :
    fairSteps.real (staysInCoordinateBoxThrough a R N) ≤
      Real.exp (-(N / escapeBlockLength R : ℕ) *
        ((4 : ℝ)⁻¹ ^ escapeBlockLength R)) := by
  have htime : escapeBlockLength R * (N / escapeBlockLength R) ≤ N := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self N (escapeBlockLength R)
  calc
    fairSteps.real (staysInCoordinateBoxThrough a R N) ≤
        fairSteps.real (staysInCoordinateBoxThrough a R
          (escapeBlockLength R * (N / escapeBlockLength R))) := by
      exact measureReal_mono (fun omega homega k hk =>
        homega k (hk.trans htime)) (by finiteness)
    _ ≤ Real.exp (-(N / escapeBlockLength R : ℕ) *
          ((4 : ℝ)⁻¹ ^ escapeBlockLength R)) :=
      measureReal_staysInCoordinateBoxThrough_le_exp a R _

/-- The corresponding survival event for the closed lattice disc. -/
def staysInClosedDiscThrough (a : Point) (R N : ℕ) : Set StepPath :=
  {omega | ∀ k ≤ N, a + trajectory omega k ∈ closedDisc R}

lemma staysInClosedDiscThrough_subset_box (a : Point) (R N : ℕ) :
    staysInClosedDiscThrough a R N ⊆ staysInCoordinateBoxThrough a R N := by
  intro omega homega k hk
  exact (mem_closedDisc R (a + trajectory omega k)).mp (homega k hk) |>.1

lemma measurableSet_staysInClosedDiscThrough (a : Point) (R N : ℕ) :
    MeasurableSet (staysInClosedDiscThrough a R N) := by
  have hset : staysInClosedDiscThrough a R N = ⋂ k : Fin (N + 1),
      {omega | a + trajectory omega k ∈ closedDisc R} := by
    ext omega
    simp only [staysInClosedDiscThrough, mem_ofPred_eq, mem_iInter]
    constructor
    · intro h k
      exact h k (Nat.lt_succ_iff.mp k.isLt)
    · intro h k hk
      exact h ⟨k, Nat.lt_succ_iff.mpr hk⟩
  rw [hset]
  apply MeasurableSet.iInter
  intro k
  have hpos : Measurable (fun omega : StepPath => a + trajectory omega (k : ℕ)) :=
    measurable_const.add ((measurable_pi_apply (k : ℕ)).comp measurable_trajectory)
  exact hpos (Set.to_countable _).measurableSet

/-- Closed-disc survival inherits the same arbitrary-horizon geometric tail. -/
theorem fairSteps_staysInClosedDiscThrough_le_geometric_div
    (a : Point) (R N : ℕ) :
    fairSteps (staysInClosedDiscThrough a R N) ≤
      (1 - (4 : ℝ≥0∞)⁻¹ ^ escapeBlockLength R) ^
        (N / escapeBlockLength R) :=
  (measure_mono (staysInClosedDiscThrough_subset_box a R N)).trans
    (fairSteps_staysInCoordinateBoxThrough_le_geometric_div a R N)

/-- Closed-disc survival also has the explicit real exponential tail. -/
theorem measureReal_staysInClosedDiscThrough_le_exp_div
    (a : Point) (R N : ℕ) :
    fairSteps.real (staysInClosedDiscThrough a R N) ≤
      Real.exp (-(N / escapeBlockLength R : ℕ) *
        ((4 : ℝ)⁻¹ ^ escapeBlockLength R)) :=
  (measureReal_mono (staysInClosedDiscThrough_subset_box a R N)).trans
    (measureReal_staysInCoordinateBoxThrough_le_exp_div a R N)

end ExitTail
end Erdos1165
