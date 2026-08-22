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
# Finite annuli and exact stopped-walk identities

This file develops the finite-domain part of planar lattice potential theory
used in hitting estimates.  It does not postulate a potential kernel or an
asymptotic Harnack principle.  Instead it proves exact algebraic facts for the
four-neighbour averaging operator and its walk killed on leaving a finite
domain.

`stoppedExpectation D n f x` is the exact depth-`n` uniform four-ary tree
average of `f` at the walk started at `x` and frozen on its first exit from
`D`.  Thus `finite_optionalStopping` is the bounded optional-stopping identity
for a discrete harmonic function, proved directly without an appeal to a
general martingale theorem.  `finite_dynkin` is its inhomogeneous version.

The logarithmic potential-kernel asymptotics and the scale-uniform Harnack
estimates required by Hao--Li--Okada--Zheng are genuinely later inputs; none
of them is hidden in the definitions below.
-/

open MeasureTheory
open scoped BigOperators

namespace Erdos1165
namespace Annulus

/-! ## Lattice discs, annuli, and boundaries -/

/-- Squared Euclidean radius, kept integer-valued for exact lattice geometry. -/
def radiusSqInt (x : Point) : ℤ := x.1 ^ 2 + x.2 ^ 2

/-- The finite coordinate box `[-R,R]²`. -/
noncomputable def coordinateBox (R : ℕ) : Finset Point :=
  (Finset.Icc (-(R : ℤ)) (R : ℤ)).product
    (Finset.Icc (-(R : ℤ)) (R : ℤ))

@[simp] theorem mem_coordinateBox (R : ℕ) (x : Point) :
    x ∈ coordinateBox R ↔
      -(R : ℤ) ≤ x.1 ∧ x.1 ≤ R ∧ -(R : ℤ) ≤ x.2 ∧ x.2 ≤ R := by
  simp [coordinateBox, and_assoc]

/-- The closed lattice disc of squared radius at most `R²`.

The coordinate-box condition makes finiteness definitional.  It is redundant
mathematically, but retaining it avoids a nonconstructive finiteness argument.
-/
noncomputable def closedDisc (R : ℕ) : Finset Point :=
  (coordinateBox R).filter fun x ↦ radiusSqInt x ≤ (R : ℤ) ^ 2

/-- The open lattice disc of squared radius strictly below `R²`. -/
noncomputable def openDisc (R : ℕ) : Finset Point :=
  (coordinateBox R).filter fun x ↦ radiusSqInt x < (R : ℤ) ^ 2

@[simp] theorem mem_closedDisc (R : ℕ) (x : Point) :
    x ∈ closedDisc R ↔ x ∈ coordinateBox R ∧ radiusSqInt x ≤ (R : ℤ) ^ 2 := by
  simp [closedDisc]

@[simp] theorem mem_openDisc (R : ℕ) (x : Point) :
    x ∈ openDisc R ↔ x ∈ coordinateBox R ∧ radiusSqInt x < (R : ℤ) ^ 2 := by
  simp [openDisc]

/-- The auxiliary coordinate box in `closedDisc` is mathematically redundant. -/
theorem mem_closedDisc_iff_radiusSqInt_le (R : ℕ) (x : Point) :
    x ∈ closedDisc R ↔ radiusSqInt x ≤ (R : ℤ) ^ 2 := by
  rw [mem_closedDisc]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  have hR : (0 : ℤ) ≤ R := by exact_mod_cast Nat.zero_le R
  have h' : x.1 ^ 2 + x.2 ^ 2 ≤ (R : ℤ) ^ 2 := by
    simpa only [radiusSqInt] using h
  have hx1 : x.1 ^ 2 ≤ (R : ℤ) ^ 2 := by
    have hx2nonneg : (0 : ℤ) ≤ x.2 ^ 2 := sq_nonneg x.2
    nlinarith
  have hx2 : x.2 ^ 2 ≤ (R : ℤ) ^ 2 := by
    have hx1nonneg : (0 : ℤ) ≤ x.1 ^ 2 := sq_nonneg x.1
    nlinarith
  rw [mem_coordinateBox]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The auxiliary coordinate box in `openDisc` is mathematically redundant. -/
theorem mem_openDisc_iff_radiusSqInt_lt (R : ℕ) (x : Point) :
    x ∈ openDisc R ↔ radiusSqInt x < (R : ℤ) ^ 2 := by
  rw [mem_openDisc]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  have hR : (0 : ℤ) ≤ R := by exact_mod_cast Nat.zero_le R
  have h' : x.1 ^ 2 + x.2 ^ 2 < (R : ℤ) ^ 2 := by
    simpa only [radiusSqInt] using h
  have hx1 : x.1 ^ 2 < (R : ℤ) ^ 2 := by
    have hx2nonneg : (0 : ℤ) ≤ x.2 ^ 2 := sq_nonneg x.2
    nlinarith
  have hx2 : x.2 ^ 2 < (R : ℤ) ^ 2 := by
    have hx1nonneg : (0 : ℤ) ≤ x.1 ^ 2 := sq_nonneg x.1
    nlinarith
  rw [mem_coordinateBox]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem openDisc_subset_closedDisc (R : ℕ) : openDisc R ⊆ closedDisc R := by
  intro x hx
  rw [mem_openDisc] at hx
  rw [mem_closedDisc]
  exact ⟨hx.1, hx.2.le⟩

/-- The lattice annulus with inner radius `r` and outer radius `R`. -/
noncomputable def latticeAnnulus (r R : ℕ) : Finset Point := closedDisc R \ openDisc r

@[simp] theorem mem_latticeAnnulus (r R : ℕ) (x : Point) :
    x ∈ latticeAnnulus r R ↔ x ∈ closedDisc R ∧ x ∉ openDisc r := by
  simp [latticeAnnulus]

theorem mem_latticeAnnulus_iff_radiusSqInt (r R : ℕ) (x : Point) :
    x ∈ latticeAnnulus r R ↔
      (r : ℤ) ^ 2 ≤ radiusSqInt x ∧ radiusSqInt x ≤ (R : ℤ) ^ 2 := by
  rw [mem_latticeAnnulus, mem_closedDisc_iff_radiusSqInt_le,
    mem_openDisc_iff_radiusSqInt_lt]
  omega

/-- The neighbour reached using direction `d`. -/
def neighbor (x : Point) (d : Direction) : Point := x + directionVector d

/-- All sites one nearest-neighbour step from a member of `D`. -/
def neighborCloud (D : Finset Point) : Finset Point :=
  D.biUnion fun x ↦ Finset.univ.image (neighbor x)

@[simp] theorem mem_neighborCloud (D : Finset Point) (y : Point) :
    y ∈ neighborCloud D ↔ ∃ x ∈ D, ∃ d : Direction, neighbor x d = y := by
  simp [neighborCloud]

/-- Sites outside `D` which can be reached from `D` in one step. -/
def outerBoundary (D : Finset Point) : Finset Point := neighborCloud D \ D

/-- Sites in `D` which have a neighbour outside `D`. -/
def innerBoundary (D : Finset Point) : Finset Point :=
  D.filter fun x ↦ ∃ d : Direction, neighbor x d ∉ D

@[simp] theorem mem_outerBoundary (D : Finset Point) (y : Point) :
    y ∈ outerBoundary D ↔
      y ∉ D ∧ ∃ x ∈ D, ∃ d : Direction, neighbor x d = y := by
  rw [outerBoundary, Finset.mem_sdiff, mem_neighborCloud]
  tauto

@[simp] theorem mem_innerBoundary (D : Finset Point) (x : Point) :
    x ∈ innerBoundary D ↔ x ∈ D ∧ ∃ d : Direction, neighbor x d ∉ D := by
  simp [innerBoundary]

theorem neighbor_mem_outerBoundary (D : Finset Point) {x : Point} (hx : x ∈ D)
    {d : Direction} (hxd : neighbor x d ∉ D) : neighbor x d ∈ outerBoundary D := by
  rw [mem_outerBoundary]
  exact ⟨hxd, x, hx, d, rfl⟩

/-! ## The four-neighbour operator and discrete harmonicity -/

/-- Uniform average over the four nearest neighbours. -/
noncomputable def neighborAverage (f : Point → ℝ) (x : Point) : ℝ :=
  (∑ d : Direction, f (neighbor x d)) / 4

/-- Integration against the uniform increment law is the four-point average. -/
theorem integral_fairStep (g : Direction → ℝ) :
    ∫ d, g d ∂fairStep = (∑ d : Direction, g d) / 4 := by
  have hg : Integrable g fairStep := by
    refine Integrable.of_bound (measurable_of_countable g).aestronglyMeasurable
      (∑ d : Direction, ‖g d‖) (ae_of_all _ fun d ↦ ?_)
    exact Finset.single_le_sum (fun i _ ↦ norm_nonneg (g i)) (Finset.mem_univ d)
  rw [integral_fintype hg]
  simp_rw [measureReal_def, fairStep_singleton]
  simp only [ENNReal.toReal_ofNat, ENNReal.toReal_div, ENNReal.toReal_one,
    smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

theorem neighborAverage_eq_integral (f : Point → ℝ) (x : Point) :
    neighborAverage f x = ∫ d, f (neighbor x d) ∂fairStep := by
  rw [integral_fairStep]
  rfl

/-- The unnormalised nearest-neighbour Laplacian. -/
def laplacian (f : Point → ℝ) (x : Point) : ℝ :=
  ∑ d : Direction, (f (neighbor x d) - f x)

/-- A function is harmonic on `D` when it has the four-neighbour mean-value property there. -/
def HarmonicOn (D : Finset Point) (f : Point → ℝ) : Prop :=
  ∀ x ∈ D, neighborAverage f x = f x

/-- The one-step drift of `f`. -/
noncomputable def drift (f : Point → ℝ) (x : Point) : ℝ := neighborAverage f x - f x

theorem laplacian_eq_four_mul_drift (f : Point → ℝ) (x : Point) :
    laplacian f x = 4 * drift f x := by
  simp only [laplacian, drift, neighborAverage, Finset.sum_sub_distrib]
  simp
  ring

theorem harmonicAt_iff_laplacian_eq_zero (f : Point → ℝ) (x : Point) :
    neighborAverage f x = f x ↔ laplacian f x = 0 := by
  rw [laplacian_eq_four_mul_drift]
  constructor <;> intro h
  · simp [drift, h]
  · have : drift f x = 0 := by linarith
    exact sub_eq_zero.mp this

theorem harmonicOn_iff_laplacian (D : Finset Point) (f : Point → ℝ) :
    HarmonicOn D f ↔ ∀ x ∈ D, laplacian f x = 0 := by
  simp only [HarmonicOn, harmonicAt_iff_laplacian_eq_zero]

theorem harmonicOn_const (D : Finset Point) (c : ℝ) : HarmonicOn D (fun _ ↦ c) := by
  intro x hx
  simp [neighborAverage]

/-! ## The exit-frozen walk and its exact finite expectation -/

/-- Make one ordinary step inside `D`, and freeze forever after leaving `D`. -/
def absorbedStep (D : Finset Point) (x : Point) (d : Direction) : Point :=
  if x ∈ D then neighbor x d else x

@[simp] theorem absorbedStep_of_mem (D : Finset Point) {x : Point} (hx : x ∈ D)
    (d : Direction) : absorbedStep D x d = neighbor x d := by
  simp [absorbedStep, hx]

@[simp] theorem absorbedStep_of_notMem (D : Finset Point) {x : Point} (hx : x ∉ D)
    (d : Direction) : absorbedStep D x d = x := by
  simp [absorbedStep, hx]

/-- A concrete walk driven by increments and frozen at its first exit from `D`. -/
def absorbedPosition (D : Finset Point) (a : Point) (omega : StepPath) : ℕ → Point
  | 0 => a
  | n + 1 => absorbedStep D (absorbedPosition D a omega n) (omega n)

@[simp] theorem absorbedPosition_zero (D : Finset Point) (a : Point) (omega : StepPath) :
    absorbedPosition D a omega 0 = a := rfl

@[simp] theorem absorbedPosition_succ (D : Finset Point) (a : Point) (omega : StepPath)
    (n : ℕ) : absorbedPosition D a omega (n + 1) =
      absorbedStep D (absorbedPosition D a omega n) (omega n) := rfl

theorem absorbedPosition_eq_of_start_notMem (D : Finset Point) {a : Point} (ha : a ∉ D)
    (omega : StepPath) (n : ℕ) : absorbedPosition D a omega n = a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ih, absorbedStep, ha]

/-- Once the absorbed path has left `D`, it remains at that exit site. -/
theorem absorbedPosition_stable_after_exit (D : Finset Point) (a : Point) (omega : StepPath)
    {n : ℕ} (hn : absorbedPosition D a omega n ∉ D) (k : ℕ) :
    absorbedPosition D a omega (n + k) = absorbedPosition D a omega n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, absorbedPosition_succ, ih]
      exact absorbedStep_of_notMem D hn (omega (n + k))

/-- A first step out of a finite domain lands on its outer vertex boundary. -/
theorem absorbedPosition_exit_mem_outerBoundary (D : Finset Point) (a : Point)
    (omega : StepPath) {n : ℕ} (hn : absorbedPosition D a omega n ∈ D)
    (hout : absorbedPosition D a omega (n + 1) ∉ D) :
    absorbedPosition D a omega (n + 1) ∈ outerBoundary D := by
  rw [absorbedPosition_succ, absorbedStep_of_mem D hn] at hout ⊢
  exact neighbor_mem_outerBoundary D hn hout

/-- Exact finite-horizon expectation for the exit-frozen walk.

The recursion averages over all four choices at every node of the finite
increment tree, so it is an exact finite sum (not a limiting definition).
-/
noncomputable def stoppedExpectation (D : Finset Point) : ℕ → (Point → ℝ) → Point → ℝ
  | 0, f, x => f x
  | n + 1, f, x =>
      (∑ d : Direction, stoppedExpectation D n f (absorbedStep D x d)) / 4

@[simp] theorem stoppedExpectation_zero (D : Finset Point) (f : Point → ℝ) (x : Point) :
    stoppedExpectation D 0 f x = f x := rfl

theorem stoppedExpectation_succ (D : Finset Point) (n : ℕ) (f : Point → ℝ)
    (x : Point) : stoppedExpectation D (n + 1) f x =
      (∑ d : Direction, stoppedExpectation D n f (absorbedStep D x d)) / 4 := rfl

/-- Integral form of the exact one-step recursion. -/
theorem stoppedExpectation_succ_integral (D : Finset Point) (n : ℕ)
    (f : Point → ℝ) (x : Point) : stoppedExpectation D (n + 1) f x =
      ∫ d, stoppedExpectation D n f (absorbedStep D x d) ∂fairStep := by
  rw [stoppedExpectation_succ, integral_fairStep]

theorem stoppedExpectation_one (D : Finset Point) (f : Point → ℝ) (x : Point) :
    stoppedExpectation D 1 f x = if x ∈ D then neighborAverage f x else f x := by
  by_cases hx : x ∈ D <;> simp [stoppedExpectation, neighborAverage, absorbedStep, hx]

theorem stoppedExpectation_of_notMem (D : Finset Point) {x : Point} (hx : x ∉ D)
    (n : ℕ) (f : Point → ℝ) : stoppedExpectation D n f x = f x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [stoppedExpectation, absorbedStep, hx, ih]

/-- Exact bounded optional stopping for the walk frozen on exiting `D`. -/
theorem finite_optionalStopping (D : Finset Point) {f : Point → ℝ}
    (hf : HarmonicOn D f) (n : ℕ) (x : Point) :
    stoppedExpectation D n f x = f x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      by_cases hx : x ∈ D
      · rw [stoppedExpectation_succ]
        simp_rw [absorbedStep_of_mem D hx, ih]
        exact hf x hx
      · exact stoppedExpectation_of_notMem D hx (n + 1) f

/-! ## A finite Dynkin identity -/

/-- Expected accumulated value of `g` before exit, through at most `n` steps. -/
noncomputable def stoppedOccupation (D : Finset Point) : ℕ → (Point → ℝ) → Point → ℝ
  | 0, _g, _x => 0
  | n + 1, g, x =>
      if x ∈ D then g x + (∑ d : Direction,
        stoppedOccupation D n g (neighbor x d)) / 4 else 0

@[simp] theorem stoppedOccupation_zero (D : Finset Point) (g : Point → ℝ) (x : Point) :
    stoppedOccupation D 0 g x = 0 := rfl

theorem stoppedOccupation_succ_of_mem (D : Finset Point) {x : Point} (hx : x ∈ D)
    (n : ℕ) (g : Point → ℝ) : stoppedOccupation D (n + 1) g x =
      g x + (∑ d : Direction, stoppedOccupation D n g (neighbor x d)) / 4 := by
  simp [stoppedOccupation, hx]

theorem stoppedOccupation_of_notMem (D : Finset Point) {x : Point} (hx : x ∉ D)
    (n : ℕ) (g : Point → ℝ) : stoppedOccupation D n g x = 0 := by
  cases n <;> simp [stoppedOccupation, hx]

/-- Finite Dynkin formula: expected terminal value equals initial value plus
the expected accumulated one-step drift before exit. -/
theorem finite_dynkin (D : Finset Point) (f : Point → ℝ) (n : ℕ) (x : Point) :
    stoppedExpectation D n f x = f x + stoppedOccupation D n (drift f) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      by_cases hx : x ∈ D
      · rw [stoppedExpectation_succ, stoppedOccupation_succ_of_mem D hx]
        simp_rw [absorbedStep_of_mem D hx, ih]
        simp only [Finset.sum_add_distrib, drift, neighborAverage]
        ring
      · rw [stoppedExpectation_of_notMem D hx, stoppedOccupation_of_notMem D hx]
        simp

/-! ## The squared-radius martingale -/

/-- Squared Euclidean radius as a real-valued test function. -/
def radiusSq (x : Point) : ℝ := (x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2

theorem radiusSq_nonneg (x : Point) : 0 ≤ radiusSq x := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- One planar simple-random-walk step increases squared radius by one in expectation. -/
theorem neighborAverage_radiusSq (x : Point) :
    neighborAverage radiusSq x = radiusSq x + 1 := by
  rw [neighborAverage, Fin.sum_univ_four]
  norm_num [neighbor, radiusSq, directionVector]
  ring

@[simp] theorem drift_radiusSq (x : Point) : drift radiusSq x = 1 := by
  rw [drift, neighborAverage_radiusSq]
  ring

/-- Exact stopped squared-radius identity.  The occupation term on the right
is the expected number of pre-exit steps, truncated at `n`. -/
theorem stopped_radiusSq_identity (D : Finset Point) (n : ℕ) (x : Point) :
    stoppedExpectation D n radiusSq x =
      radiusSq x + stoppedOccupation D n (fun _ ↦ 1) x := by
  have hfun : drift radiusSq = fun _ ↦ 1 := by
    funext y
    exact drift_radiusSq y
  rw [← hfun]
  exact finite_dynkin D radiusSq n x

/-- Space-time form of the squared-radius martingale for one unstopped step. -/
theorem radiusSq_sub_time_oneStep (x : Point) (n : ℕ) :
    (∑ d : Direction, (radiusSq (neighbor x d) - ((n + 1 : ℕ) : ℝ))) / 4 =
      radiusSq x - (n : ℝ) := by
  rw [Finset.sum_sub_distrib]
  have h := neighborAverage_radiusSq x
  simp only [neighborAverage] at h
  have hc : (∑ _d : Direction, ((n + 1 : ℕ) : ℝ)) =
      4 * ((n + 1 : ℕ) : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  rw [hc]
  calc
    ((∑ d : Direction, radiusSq (neighbor x d)) -
          4 * ((n + 1 : ℕ) : ℝ)) / 4 =
        (∑ d : Direction, radiusSq (neighbor x d)) / 4 - ((n + 1 : ℕ) : ℝ) := by ring
    _ = (radiusSq x + 1) - ((n + 1 : ℕ) : ℝ) := by rw [h]
    _ = radiusSq x - (n : ℝ) := by push_cast; ring

end Annulus
end Erdos1165
