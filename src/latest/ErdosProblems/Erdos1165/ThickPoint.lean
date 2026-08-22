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
# The deterministic thick-point setup for Erdős Problem 1165

This file formalizes the definitions at the start of the appendix of
Hao--Li--Okada--Zheng (HLOZ), where Proposition 1.3 is proved.  In their
notation

* `Kₙ = 16 exp(n) n⁹`;
* `rₙ,ₖ = exp(n-k) n⁹` for `0 ≤ k ≤ n`, and `rₙ,ₙ₊₁ = n⁶`;
* `Uₙ = [2 rₙ,₀, 3 rₙ,₀]² ∩ ℤ²`;
* `N⁽ˣ⁾ₙ,ₖ` counts completed excursions from the boundary at scale `k-1`
  to the boundary at scale `k` before the outer exit time;
* an `(n, δ)`-successful point satisfies the three excursion-count
  restrictions displayed just before HLOZ (A.3).

The analytic and probabilistic estimates in HLOZ Proposition A.3 are not
asserted here.  Everything below is deterministic: finite hitting-time
recursions, finite excursion counts, the successful-point predicates, and the
finite combinatorics which turns a positive successful-point count into a
thick point and hence a lower bound for maximal local time.
-/

open scoped BigOperators ENNReal NNReal

namespace Erdos1165.ThickPoint

abbrev Point := ℤ × ℤ
abbrev WalkPath := ℕ → Point

/-! ## The exact HLOZ scales -/

/-- HLOZ's outer scale `Kₙ = 16 exp(n) n⁹`. -/
noncomputable def outerScale (n : ℕ) : ℝ :=
  16 * Real.exp (n : ℝ) * (n : ℝ) ^ 9

/-- The regular radii `rₙ,ₖ = exp(n-k) n⁹`, before the terminal scale. -/
noncomputable def regularRadius (n k : ℕ) : ℝ :=
  Real.exp ((n : ℝ) - (k : ℝ)) * (n : ℝ) ^ 9

/-- HLOZ's complete radius array, including `rₙ,ₙ₊₁ = n⁶`.  Only indices
`k ≤ n+1` are used. -/
noncomputable def scaleRadius (n k : ℕ) : ℝ :=
  if k ≤ n then regularRadius n k else (n : ℝ) ^ 6

@[simp] lemma scaleRadius_of_le {n k : ℕ} (hk : k ≤ n) :
    scaleRadius n k = regularRadius n k := by
  simp [scaleRadius, hk]

@[simp] lemma scaleRadius_succ_self (n : ℕ) :
    scaleRadius n (n + 1) = (n : ℝ) ^ 6 := by
  simp [scaleRadius]

lemma regularRadius_zero (n : ℕ) : regularRadius n 0 = outerScale n / 16 := by
  simp [regularRadius, outerScale, mul_assoc]

lemma outerScale_eq_sixteen_mul_radius_zero (n : ℕ) :
    outerScale n = 16 * scaleRadius n 0 := by
  simp [scaleRadius, regularRadius, outerScale, mul_assoc]

lemma regularRadius_succ (n k : ℕ) :
    regularRadius n (k + 1) = regularRadius n k / Real.exp 1 := by
  rw [regularRadius, regularRadius]
  rw [show (n : ℝ) - ((k + 1 : ℕ) : ℝ) = ((n : ℝ) - (k : ℝ)) - 1 by
    push_cast
    ring]
  rw [Real.exp_sub]
  ring

@[simp] lemma regularRadius_self (n : ℕ) : regularRadius n n = (n : ℝ) ^ 9 := by
  simp [regularRadius]

lemma terminalRadius_le_regularRadius_self (n : ℕ) (hn : 1 ≤ n) :
    scaleRadius n (n + 1) ≤ scaleRadius n n := by
  simp only [scaleRadius_succ_self, scaleRadius_of_le (le_refl n), regularRadius_self]
  exact pow_le_pow_right₀ (by exact_mod_cast hn : (1 : ℝ) ≤ n) (by norm_num)

/-! ## Lattice discs, boundaries, and the finite candidate square -/

/-- Squared Euclidean distance, represented in `ℝ` to match HLOZ's real radii. -/
def squaredDistance (x y : Point) : ℝ :=
  ((x.1 - y.1 : ℤ) : ℝ) ^ 2 + ((x.2 - y.2 : ℤ) : ℝ) ^ 2

/-- Euclidean distance on the embedded lattice. -/
noncomputable def latticeDistance (x y : Point) : ℝ :=
  Real.sqrt (squaredDistance x y)

/-- The discrete Euclidean disc `D(x,r)`. -/
def disc (x : Point) (r : ℝ) : Set Point :=
  {y | latticeDistance x y ≤ r}

/-- Nearest-neighbor adjacency on `ℤ²`. -/
def Adjacent (x y : Point) : Prop :=
  (x.1 - y.1).natAbs + (x.2 - y.2).natAbs = 1

/-- The inner vertex boundary of a lattice set.  This is the boundary hit by a
nearest-neighbor path when leaving the set. -/
def innerBoundary (A : Set Point) : Set Point :=
  {x | x ∈ A ∧ ∃ y, y ∉ A ∧ Adjacent x y}

/-- The lattice boundary of `D(x,r)`. -/
def discBoundary (x : Point) (r : ℝ) : Set Point :=
  innerBoundary (disc x r)

/-- The annular region between two real radii. -/
def annulus (x : Point) (rInner rOuter : ℝ) : Set Point :=
  disc x rOuter \ disc x rInner

/-- `horizon` is the first hit of HLOZ's outer boundary `∂D(0,Kₙ)`.
Keeping this as a predicate avoids assigning an artificial finite value when a
general path never reaches that boundary. -/
def IsOuterExitTime (s : WalkPath) (n horizon : ℕ) : Prop :=
  s horizon ∈ discBoundary (0, 0) (outerScale n) ∧
    ∀ t < horizon, s t ∉ discBoundary (0, 0) (outerScale n)

/-- Integer interval underlying `Uₙ`. -/
noncomputable def candidateInterval (n : ℕ) : Finset ℤ :=
  Finset.Icc ⌈2 * regularRadius n 0⌉ ⌊3 * regularRadius n 0⌋

/-- HLOZ's finite square `Uₙ = [2rₙ,₀,3rₙ,₀]² ∩ ℤ²`. -/
noncomputable def candidateBox (n : ℕ) : Finset Point :=
  (candidateInterval n).product (candidateInterval n)

@[simp] lemma mem_candidateInterval {n : ℕ} {z : ℤ} :
    z ∈ candidateInterval n ↔
      ⌈2 * regularRadius n 0⌉ ≤ z ∧ z ≤ ⌊3 * regularRadius n 0⌋ := by
  simp [candidateInterval]

@[simp] lemma mem_candidateBox {n : ℕ} {x : Point} :
    x ∈ candidateBox n ↔ x.1 ∈ candidateInterval n ∧ x.2 ∈ candidateInterval n := by
  simp [candidateBox]

lemma card_candidateBox (n : ℕ) :
    (candidateBox n).card = (candidateInterval n).card ^ 2 := by
  simp [candidateBox, pow_two]

/-! ## A finite, pathwise definition of completed excursions -/

/-- Times in `[start, horizon]` at which the path lies in `A`. -/
def hitTimesThrough (s : WalkPath) (A : Set Point) [DecidablePred (· ∈ A)]
    (start horizon : ℕ) : Finset ℕ :=
  (Finset.Icc start horizon).filter fun t ↦ s t ∈ A

/-- First hit of `A` between `start` and `horizon`, with the sentinel
`horizon+1` if no such hit exists. -/
def firstHitThrough (s : WalkPath) (A : Set Point) [DecidablePred (· ∈ A)]
    (start horizon : ℕ) : ℕ :=
  if h : (hitTimesThrough s A start horizon).Nonempty then
    (hitTimesThrough s A start horizon).min' h
  else
    horizon + 1

lemma firstHitThrough_eq_sentinel_of_empty (s : WalkPath) (A : Set Point)
    [DecidablePred (· ∈ A)] (start horizon : ℕ)
    (h : ¬(hitTimesThrough s A start horizon).Nonempty) :
    firstHitThrough s A start horizon = horizon + 1 := by
  simp [firstHitThrough, h]

lemma firstHitThrough_mem_of_nonempty (s : WalkPath) (A : Set Point)
    [DecidablePred (· ∈ A)] (start horizon : ℕ)
    (h : (hitTimesThrough s A start horizon).Nonempty) :
    firstHitThrough s A start horizon ∈ hitTimesThrough s A start horizon := by
  simp only [firstHitThrough, dif_pos h]
  exact Finset.min'_mem _ h

lemma firstHitThrough_le_horizon_iff (s : WalkPath) (A : Set Point)
    [DecidablePred (· ∈ A)] (start horizon : ℕ) :
    firstHitThrough s A start horizon ≤ horizon ↔
      (hitTimesThrough s A start horizon).Nonempty := by
  by_cases h : (hitTimesThrough s A start horizon).Nonempty
  · refine ⟨fun _ ↦ h, fun _ ↦ ?_⟩
    have hm := firstHitThrough_mem_of_nonempty s A start horizon h
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
  · simp [firstHitThrough_eq_sentinel_of_empty s A start horizon h, h]

lemma firstHitThrough_mem_set_of_le (s : WalkPath) (A : Set Point)
    [DecidablePred (· ∈ A)] (start horizon : ℕ)
    (h : firstHitThrough s A start horizon ≤ horizon) :
    s (firstHitThrough s A start horizon) ∈ A := by
  have hn := (firstHitThrough_le_horizon_iff s A start horizon).mp h
  exact (Finset.mem_filter.mp (firstHitThrough_mem_of_nonempty s A start horizon hn)).2

/-- One alternating `outer → inner` search, truncated at `horizon`. -/
def excursionStep (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon start : ℕ) : ℕ :=
  firstHitThrough s inner (firstHitThrough s outer start horizon) horizon

/-- Start time of the `j`-th successive `outer → inner` excursion search. -/
def excursionStart (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon j : ℕ) : ℕ :=
  firstHitThrough s outer ((excursionStep s outer inner horizon)^[j] 0) horizon

/-- Completion time of the `j`-th successive `outer → inner` excursion search. -/
def excursionFinish (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon j : ℕ) : ℕ :=
  firstHitThrough s inner (excursionStart s outer inner horizon j) horizon

/-- Number of completed successive `outer → inner` excursions by `horizon`.
There are at most `horizon+1` completed searches, so this is a finite count. -/
def completedExcursionCount (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)]
    (horizon : ℕ) : ℕ :=
  ((Finset.range (horizon + 1)).filter fun j ↦
    excursionFinish s outer inner horizon j ≤ horizon).card

lemma completedExcursionCount_le (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)] (horizon : ℕ) :
    completedExcursionCount s outer inner horizon ≤ horizon + 1 := by
  unfold completedExcursionCount
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)

lemma completedExcursionCount_pos_iff (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)] (horizon : ℕ) :
    0 < completedExcursionCount s outer inner horizon ↔
      ∃ j ≤ horizon, excursionFinish s outer inner horizon j ≤ horizon := by
  rw [completedExcursionCount, Finset.card_pos]
  constructor
  · rintro ⟨j, hj⟩
    have hj' := Finset.mem_filter.mp hj
    exact ⟨j, by simpa using hj'.1, hj'.2⟩
  · rintro ⟨j, hj, hfinish⟩
    exact ⟨j, Finset.mem_filter.mpr ⟨by simpa using hj, hfinish⟩⟩

lemma excursionFinish_mem_inner_of_le (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)] (horizon j : ℕ)
    (hfinish : excursionFinish s outer inner horizon j ≤ horizon) :
    s (excursionFinish s outer inner horizon j) ∈ inner := by
  exact firstHitThrough_mem_set_of_le s inner
    (excursionStart s outer inner horizon j) horizon hfinish

lemma excursionStart_mem_outer_of_finish_le (s : WalkPath) (outer inner : Set Point)
    [DecidablePred (· ∈ outer)] [DecidablePred (· ∈ inner)] (horizon j : ℕ)
    (hfinish : excursionFinish s outer inner horizon j ≤ horizon) :
    s (excursionStart s outer inner horizon j) ∈ outer := by
  have hnonempty := (firstHitThrough_le_horizon_iff s inner
    (excursionStart s outer inner horizon j) horizon).mp hfinish
  have hmem := firstHitThrough_mem_of_nonempty s inner
    (excursionStart s outer inner horizon j) horizon hnonempty
  have hstartFinish : excursionStart s outer inner horizon j ≤
      excursionFinish s outer inner horizon j :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1).1
  have hstart : excursionStart s outer inner horizon j ≤ horizon :=
    hstartFinish.trans hfinish
  exact firstHitThrough_mem_set_of_le s outer
    ((excursionStep s outer inner horizon)^[j] 0) horizon hstart

/-- The actual pathwise array `N⁽ˣ⁾ₙ,ₖ`, with a dummy zero entry at scale
zero.  For positive `k`, it counts excursions from `∂D(x,rₙ,ₖ₋₁)` to
`∂D(x,rₙ,ₖ)` completed by `horizon`. -/
noncomputable def excursionProfile (s : WalkPath) (n horizon : ℕ) (x : Point) :
    Fin (n + 2) → ℕ := fun k ↦ by
  classical
  exact if hk : k.1 = 0 then 0 else
      completedExcursionCount s
        (discBoundary x (scaleRadius n (k.1 - 1)))
        (discBoundary x (scaleRadius n k.1)) horizon

/-! ## The exact successful and thick-successful predicates -/

/-- Lower endpoint of HLOZ's terminal excursion-count window. -/
noncomputable def terminalLower (n : ℕ) (δ : ℝ) : ℝ :=
  (2 * (n : ℝ) ^ 2 - (n : ℝ) ^ (1 + δ)) / (3 * Real.log n)

/-- The local-time level used in the definition of `Y'` in HLOZ (A.3). -/
noncomputable def thickThreshold (n : ℕ) (δ' : ℝ) : ℝ :=
  4 / Real.pi * (Real.log (outerScale n)) ^ 2 -
    (Real.log (outerScale n)) ^ (1 + δ')

/-- Exact excursion-count conditions for an `(n,δ)`-successful point.  The
profile is indexed by `0,...,n+1`; entry zero is unused. -/
def SuccessfulProfile (n : ℕ) (δ : ℝ) (N : Fin (n + 2) → ℕ) : Prop :=
  N ⟨1, by omega⟩ = 1 ∧
  (∀ k : Fin (n + 2), 2 ≤ k.1 → k.1 ≤ n →
    |(N k : ℝ) - 2 * (k.1 : ℝ) ^ 2| ≤ (k.1 : ℝ) ^ (1 + δ)) ∧
  terminalLower n δ ≤ (N ⟨n + 1, by omega⟩ : ℝ) ∧
  N ⟨n + 1, by omega⟩ ≤ n ^ 3

/-- Pathwise `(n,δ)`-success using the actual annular excursion profile. -/
noncomputable def SuccessfulPoint (s : WalkPath) (n horizon : ℕ) (δ : ℝ)
    (x : Point) : Prop :=
  x ∈ candidateBox n ∧ SuccessfulProfile n δ (excursionProfile s n horizon x)

/-- Local time through a finite horizon, including both endpoints. -/
def localTimeThrough (s : WalkPath) (horizon : ℕ) (x : Point) : ℕ :=
  ((Finset.range (horizon + 1)).filter fun t ↦ s t = x).card

/-- Finite-horizon maximal local time, computed on the finite range. -/
def maxLocalTimeThrough (s : WalkPath) (horizon : ℕ) : ℕ :=
  (Finset.range (horizon + 1)).sup fun t ↦ localTimeThrough s horizon (s t)

/-- The event represented by the indicator `Y'(n,x)`: successful excursion
counts together with the required thick-point local time. -/
noncomputable def ThickSuccessfulPoint (s : WalkPath) (n horizon : ℕ)
    (δ δ' : ℝ) (x : Point) : Prop :=
  SuccessfulPoint s n horizon δ x ∧
    thickThreshold n δ' ≤ (localTimeThrough s horizon x : ℝ)

noncomputable def thickSuccessfulPoints (s : WalkPath) (n horizon : ℕ)
    (δ δ' : ℝ) : Finset Point := by
  classical
  exact (candidateBox n).filter fun x ↦ ThickSuccessfulPoint s n horizon δ δ' x

noncomputable def thickSuccessfulCount (s : WalkPath) (n horizon : ℕ)
    (δ δ' : ℝ) : ℕ :=
  (thickSuccessfulPoints s n horizon δ δ').card

/-- The `0/1` indicator denoted by `Y'(n,x)` in HLOZ. -/
noncomputable def thickSuccessfulIndicator (s : WalkPath) (n horizon : ℕ)
    (δ δ' : ℝ) (x : Point) : ℕ := by
  classical
  exact if ThickSuccessfulPoint s n horizon δ δ' x then 1 else 0

@[simp] lemma mem_thickSuccessfulPoints {s : WalkPath} {n horizon : ℕ}
    {δ δ' : ℝ} {x : Point} :
    x ∈ thickSuccessfulPoints s n horizon δ δ' ↔
      ThickSuccessfulPoint s n horizon δ δ' x := by
  classical
  rw [thickSuccessfulPoints, Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h.1.1, h⟩⟩

lemma thickSuccessfulPoint_successful {s : WalkPath} {n horizon : ℕ}
    {δ δ' : ℝ} {x : Point} (hx : ThickSuccessfulPoint s n horizon δ δ' x) :
    SuccessfulPoint s n horizon δ x := hx.1

lemma localTimeThrough_le_maxLocalTimeThrough (s : WalkPath) (horizon : ℕ)
    {x : Point} (hx : x ∈ (Finset.range (horizon + 1)).image s) :
    localTimeThrough s horizon x ≤ maxLocalTimeThrough s horizon := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.le_sup (f := fun t ↦ localTimeThrough s horizon (s t)) ht

lemma mem_range_of_localTimeThrough_pos {s : WalkPath} {horizon : ℕ} {x : Point}
    (hx : 0 < localTimeThrough s horizon x) :
    x ∈ (Finset.range (horizon + 1)).image s := by
  rw [localTimeThrough, Finset.card_pos] at hx
  obtain ⟨t, ht⟩ := hx
  exact Finset.mem_image.mpr ⟨t, (Finset.mem_filter.mp ht).1,
    (Finset.mem_filter.mp ht).2⟩

lemma maxLocalTimeThrough_ge_of_thickSuccessfulPoint
    {s : WalkPath} {n horizon : ℕ} {δ δ' : ℝ} {x : Point}
    (hx : ThickSuccessfulPoint s n horizon δ δ' x)
    (hthreshold : 0 < thickThreshold n δ') :
    thickThreshold n δ' ≤ (maxLocalTimeThrough s horizon : ℝ) := by
  have hlocalReal : thickThreshold n δ' ≤ (localTimeThrough s horizon x : ℝ) := hx.2
  have hlocalPos : 0 < localTimeThrough s horizon x := by
    exact_mod_cast lt_of_lt_of_le hthreshold hlocalReal
  have hle := localTimeThrough_le_maxLocalTimeThrough s horizon
    (mem_range_of_localTimeThrough_pos hlocalPos)
  exact hlocalReal.trans (by exact_mod_cast hle)

lemma thickSuccessfulCount_pos_iff {s : WalkPath} {n horizon : ℕ} {δ δ' : ℝ} :
    0 < thickSuccessfulCount s n horizon δ δ' ↔
      ∃ x, ThickSuccessfulPoint s n horizon δ δ' x := by
  constructor
  · intro h
    rw [thickSuccessfulCount, Finset.card_pos] at h
    obtain ⟨x, hx⟩ := h
    exact ⟨x, mem_thickSuccessfulPoints.mp hx⟩
  · rintro ⟨x, hx⟩
    rw [thickSuccessfulCount, Finset.card_pos]
    exact ⟨x, mem_thickSuccessfulPoints.mpr hx⟩

lemma sum_thickSuccessfulIndicator (s : WalkPath) (n horizon : ℕ) (δ δ' : ℝ) :
    ∑ x ∈ candidateBox n, thickSuccessfulIndicator s n horizon δ δ' x =
      thickSuccessfulCount s n horizon δ δ' := by
  classical
  unfold thickSuccessfulIndicator thickSuccessfulCount thickSuccessfulPoints
  exact (Finset.card_filter _ _).symm

lemma sum_thickSuccessfulIndicator_pos_iff
    {s : WalkPath} {n horizon : ℕ} {δ δ' : ℝ} :
    0 < ∑ x ∈ candidateBox n, thickSuccessfulIndicator s n horizon δ δ' x ↔
      ∃ x, ThickSuccessfulPoint s n horizon δ δ' x := by
  rw [sum_thickSuccessfulIndicator, thickSuccessfulCount_pos_iff]

/-- Deterministic implication used immediately before HLOZ (A.3): if the
finite sum of `Y'` indicators is positive, the maximal local time reaches the
thick-point threshold. -/
theorem maxLocalTimeThrough_ge_of_thickSuccessfulCount_pos
    {s : WalkPath} {n horizon : ℕ} {δ δ' : ℝ}
    (hcount : 0 < thickSuccessfulCount s n horizon δ δ')
    (hthreshold : 0 < thickThreshold n δ') :
    thickThreshold n δ' ≤ (maxLocalTimeThrough s horizon : ℝ) := by
  obtain ⟨x, hx⟩ := thickSuccessfulCount_pos_iff.mp hcount
  exact maxLocalTimeThrough_ge_of_thickSuccessfulPoint hx hthreshold

lemma thickSuccessfulCount_le_candidateBox (s : WalkPath) (n horizon : ℕ)
    (δ δ' : ℝ) :
    thickSuccessfulCount s n horizon δ δ' ≤ (candidateBox n).card := by
  classical
  unfold thickSuccessfulCount thickSuccessfulPoints
  exact Finset.card_le_card (Finset.filter_subset _ _)

end Erdos1165.ThickPoint
