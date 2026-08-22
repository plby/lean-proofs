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

import ErdosProblems.Erdos1165.AppendixDecoupling
import ErdosProblems.Erdos1165.SecondMoment

/-!
# Separation levels and the two-point decomposition in HLOZ Appendix A

This file formalizes the non-asymptotic skeleton of Proposition A.3(2) in
Hao--Li--Okada--Zheng.  Their separation level is

`l(x,y) = min {m >= 1 | D(x,r[n,m]) ∩ D(y,r[n,m]) = ∅}`.

For total definitions we search the scales `1, ..., n+1` and use the sentinel
`n+2` when no separation occurs there.  The sentinel is important: it keeps
the level decomposition an equality, including diagonal and very close pairs.

The file proves three pieces which do not use the missing planar Harnack
estimate:

* exact properties and symmetry of the separation level;
* a genuine partition of every finite double sum by separation level, together
  with the geometric reduction of a level-`l` partner count to overlap at
  scale `l-1`;
* the conditional-expectation identity and finite count-fibre decomposition
  used in HLOZ (A.16).

The analytic estimate which bounds the conditional probability after this
decomposition is deliberately not postulated here.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos1165.AppendixPair

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev Point := ThickPoint.Point

/-! ## The exact separation level -/

/-- The two HLOZ discs at scale `k` are disjoint. -/
def SeparatedAt (n k : ℕ) (x y : Point) : Prop :=
  Disjoint (ThickPoint.disc x (ThickPoint.scaleRadius n k))
    (ThickPoint.disc y (ThickPoint.scaleRadius n k))

/-- The finite set of scales on which the Appendix-A construction is defined. -/
def scaleIndices (n : ℕ) : Finset ℕ := Finset.Icc 1 (n + 1)

/-- Scales in `1, ..., n+1` at which the two discs are disjoint. -/
def separatingIndices (n : ℕ) (x y : Point) : Finset ℕ :=
  (scaleIndices n).filter fun k => SeparatedAt n k x y

/-- HLOZ's first separation scale, with the sentinel `n+2` if the two discs do
not separate by scale `n+1`. -/
def separationLevel (n : ℕ) (x y : Point) : ℕ :=
  if h : (separatingIndices n x y).Nonempty then
    (separatingIndices n x y).min' h
  else
    n + 2

/-- Predicate form of "`l` is the first separating scale". -/
def FirstSeparatedAt (n : ℕ) (x y : Point) (l : ℕ) : Prop :=
  l ∈ separatingIndices n x y ∧
    ∀ k ∈ scaleIndices n, k < l → ¬ SeparatedAt n k x y

@[simp] lemma separatedAt_comm (n k : ℕ) (x y : Point) :
    SeparatedAt n k x y ↔ SeparatedAt n k y x := by
  simp only [SeparatedAt, disjoint_comm]

lemma separatingIndices_comm (n : ℕ) (x y : Point) :
    separatingIndices n x y = separatingIndices n y x := by
  ext k
  simp [separatingIndices, separatedAt_comm]

lemma separationLevel_comm (n : ℕ) (x y : Point) :
    separationLevel n x y = separationLevel n y x := by
  simp only [separationLevel, separatingIndices_comm n x y]

lemma separationLevel_ne_zero (n : ℕ) (x y : Point) :
    separationLevel n x y ≠ 0 := by
  unfold separationLevel
  split_ifs with h
  · have hm := Finset.min'_mem (separatingIndices n x y) h
    have hscale := (Finset.mem_filter.mp hm).1
    exact Nat.ne_of_gt (Finset.mem_Icc.mp hscale).1
  · omega

lemma separationLevel_le_sentinel (n : ℕ) (x y : Point) :
    separationLevel n x y ≤ n + 2 := by
  unfold separationLevel
  split_ifs with h
  · have hm := Finset.min'_mem (separatingIndices n x y) h
    have hscale := (Finset.mem_filter.mp hm).1
    simp only [scaleIndices, Finset.mem_Icc] at hscale
    omega
  · exact le_rfl

lemma separationLevel_mem_scaleIndices
    {n : ℕ} {x y : Point} (h : (separatingIndices n x y).Nonempty) :
    separationLevel n x y ∈ scaleIndices n := by
  rw [separationLevel, dif_pos h]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).1

lemma separationLevel_isSeparated
    {n : ℕ} {x y : Point} (h : (separatingIndices n x y).Nonempty) :
    SeparatedAt n (separationLevel n x y) x y := by
  rw [separationLevel, dif_pos h]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).2

lemma separationLevel_not_separated_before
    {n : ℕ} {x y : Point} (h : (separatingIndices n x y).Nonempty)
    {k : ℕ} (hk : k ∈ scaleIndices n) (hkl : k < separationLevel n x y) :
    ¬ SeparatedAt n k x y := by
  intro hsep
  have hmem : k ∈ separatingIndices n x y :=
    Finset.mem_filter.mpr ⟨hk, hsep⟩
  have hmin : separationLevel n x y ≤ k := by
    rw [separationLevel, dif_pos h]
    exact Finset.min'_le _ _ hmem
  omega

lemma firstSeparatedAt_separationLevel
    {n : ℕ} {x y : Point} (h : (separatingIndices n x y).Nonempty) :
    FirstSeparatedAt n x y (separationLevel n x y) := by
  exact ⟨Finset.mem_filter.mpr
      ⟨separationLevel_mem_scaleIndices h, separationLevel_isSeparated h⟩,
    fun _ hk hlt => separationLevel_not_separated_before h hk hlt⟩

lemma firstSeparatedAt_unique {n l : ℕ} {x y : Point}
    (hl : FirstSeparatedAt n x y l) : separationLevel n x y = l := by
  have hnonempty : (separatingIndices n x y).Nonempty := ⟨l, hl.1⟩
  apply le_antisymm
  · rw [separationLevel, dif_pos hnonempty]
    exact Finset.min'_le _ _ hl.1
  · by_contra hnot
    have hlt : separationLevel n x y < l := Nat.lt_of_not_ge hnot
    exact hl.2 _ (separationLevel_mem_scaleIndices hnonempty) hlt
      (separationLevel_isSeparated hnonempty)

lemma firstSeparatedAt_iff {n l : ℕ} {x y : Point} :
    FirstSeparatedAt n x y l ↔
      separationLevel n x y = l ∧ l ≤ n + 1 := by
  constructor
  · intro hl
    exact ⟨firstSeparatedAt_unique hl,
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hl.1).1).2⟩
  · rintro ⟨heq, hle⟩
    have hne : separationLevel n x y ≠ n + 2 := by omega
    have hnonempty : (separatingIndices n x y).Nonempty := by
      by_contra hempty
      rw [separationLevel, dif_neg hempty] at hne
      exact hne rfl
    rw [← heq]
    exact firstSeparatedAt_separationLevel hnonempty

@[simp] lemma separationLevel_eq_sentinel_iff {n : ℕ} {x y : Point} :
    separationLevel n x y = n + 2 ↔
      ¬(separatingIndices n x y).Nonempty := by
  constructor
  · intro heq hnonempty
    have hmem := separationLevel_mem_scaleIndices hnonempty
    have hle := (Finset.mem_Icc.mp hmem).2
    omega
  · intro hempty
    simp [separationLevel, hempty]

/-! ## Finite partner strata and pair counting -/

/-- Points of `U` whose first separation from `x` has level `l`. -/
def levelPartners (U : Finset Point) (n : ℕ) (x : Point) (l : ℕ) : Finset Point :=
  U.filter fun y => separationLevel n x y = l

/-- Ordered-pair count in the separation stratum `l`. -/
def pairCountAtLevel (U : Finset Point) (n l : ℕ) : ℕ :=
  ∑ x ∈ U, (levelPartners U n x l).card

/-- Weighted ordered-pair sum in the separation stratum `l`. -/
def pairSumAtLevel {M : Type*} [AddCommMonoid M]
    (U : Finset Point) (n l : ℕ) (w : Point → Point → M) : M :=
  ∑ x ∈ U, ∑ y ∈ levelPartners U n x l, w x y

@[simp] lemma mem_levelPartners {U : Finset Point} {n l : ℕ} {x y : Point} :
    y ∈ levelPartners U n x l ↔ y ∈ U ∧ separationLevel n x y = l := by
  simp [levelPartners]

lemma levelPartners_subset (U : Finset Point) (n : ℕ) (x : Point) (l : ℕ) :
    levelPartners U n x l ⊆ U := by
  exact Finset.filter_subset _ _

lemma card_levelPartners_le (U : Finset Point) (n : ℕ) (x : Point) (l : ℕ) :
    (levelPartners U n x l).card ≤ U.card :=
  Finset.card_le_card (levelPartners_subset U n x l)

lemma pairCountAtLevel_le_square (U : Finset Point) (n l : ℕ) :
    pairCountAtLevel U n l ≤ U.card ^ 2 := by
  calc
    pairCountAtLevel U n l
        ≤ ∑ _x ∈ U, U.card :=
      Finset.sum_le_sum fun x hx => card_levelPartners_le U n x l
    _ = U.card ^ 2 := by simp [pow_two]

/-- Every ordered pair lies in exactly one level, including the sentinel. -/
theorem pairSum_eq_sum_separationLevels {M : Type*} [AddCommMonoid M]
    (U : Finset Point) (n : ℕ) (w : Point → Point → M) :
    (∑ x ∈ U, ∑ y ∈ U, w x y) =
      ∑ l ∈ Finset.Icc 1 (n + 2), pairSumAtLevel U n l w := by
  classical
  calc
    (∑ x ∈ U, ∑ y ∈ U, w x y) =
        ∑ x ∈ U, ∑ l ∈ Finset.Icc 1 (n + 2),
          ∑ y ∈ U with separationLevel n x y = l, w x y := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (Finset.sum_fiberwise_of_maps_to
        (s := U) (t := Finset.Icc 1 (n + 2))
        (g := separationLevel n x)
        (fun y hy => Finset.mem_Icc.mpr
          ⟨Nat.one_le_iff_ne_zero.mpr (separationLevel_ne_zero n x y),
            separationLevel_le_sentinel n x y⟩)
        (fun y => w x y)).symm
    _ = ∑ l ∈ Finset.Icc 1 (n + 2), pairSumAtLevel U n l w := by
      rw [Finset.sum_comm]
      simp only [pairSumAtLevel, levelPartners, Finset.sum_filter]

/-- Points which overlap `x` at scale `l-1`.  HLOZ bounds this finite set by
the lattice area of `D(x, 2 r[n,l-1])`. -/
def previousOverlapPartners (U : Finset Point) (n : ℕ) (x : Point) (l : ℕ) : Finset Point :=
  U.filter fun y =>
    ∃ z, z ∈ ThickPoint.disc x (ThickPoint.scaleRadius n (l - 1)) ∧
      z ∈ ThickPoint.disc y (ThickPoint.scaleRadius n (l - 1))

/-- A finite coordinate square centered at `x`, used to count lattice points
in a Euclidean neighbourhood without any asymptotic notation. -/
def coordinateSquare (x : Point) (q : ℕ) : Finset Point :=
  (Finset.Icc (x.1 - (q : ℤ)) (x.1 + (q : ℤ))).product
    (Finset.Icc (x.2 - (q : ℤ)) (x.2 + (q : ℤ)))

@[simp] lemma mem_coordinateSquare {x y : Point} {q : ℕ} :
    y ∈ coordinateSquare x q ↔
      x.1 - (q : ℤ) ≤ y.1 ∧ y.1 ≤ x.1 + (q : ℤ) ∧
      x.2 - (q : ℤ) ≤ y.2 ∧ y.2 ≤ x.2 + (q : ℤ) := by
  simp [coordinateSquare, and_assoc]

lemma card_int_centeredInterval (a : ℤ) (q : ℕ) :
    (Finset.Icc (a - (q : ℤ)) (a + (q : ℤ))).card = 2 * q + 1 := by
  rw [Int.card_Icc]
  have heq : a + (q : ℤ) + 1 - (a - (q : ℤ)) = ((2 * q + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [heq]
  omega

lemma card_coordinateSquare (x : Point) (q : ℕ) :
    (coordinateSquare x q).card = (2 * q + 1) ^ 2 := by
  let A := Finset.Icc (x.1 - (q : ℤ)) (x.1 + (q : ℤ))
  let B := Finset.Icc (x.2 - (q : ℤ)) (x.2 + (q : ℤ))
  calc
    (coordinateSquare x q).card = (A.product B).card := by rfl
    _ = A.card * B.card := Finset.card_product A B
    _ = (2 * q + 1) * (2 * q + 1) := by
      rw [show A.card = 2 * q + 1 by exact card_int_centeredInterval x.1 q,
        show B.card = 2 * q + 1 by exact card_int_centeredInterval x.2 q]
    _ = (2 * q + 1) ^ 2 := by ring

lemma scaleRadius_nonneg (n k : ℕ) : 0 ≤ ThickPoint.scaleRadius n k := by
  simp only [ThickPoint.scaleRadius]
  split_ifs
  · exact mul_nonneg (Real.exp_nonneg _) (by positivity)
  · positivity

/-- Each coordinate displacement is bounded by Euclidean lattice distance. -/
lemma abs_first_sub_le_latticeDistance (x y : Point) :
    |(((x.1 - y.1 : ℤ) : ℝ))| ≤ ThickPoint.latticeDistance x y := by
  apply Real.abs_le_sqrt
  simp only [ThickPoint.squaredDistance]
  exact le_add_of_nonneg_right (sq_nonneg _)

lemma abs_second_sub_le_latticeDistance (x y : Point) :
    |(((x.2 - y.2 : ℤ) : ℝ))| ≤ ThickPoint.latticeDistance x y := by
  apply Real.abs_le_sqrt
  simp only [ThickPoint.squaredDistance]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- If the radius-`r` discs around `x` and `y` overlap, the centers lie in a
coordinate square of radius `ceil(2r)`. -/
lemma mem_coordinateSquare_of_common_disc_point
    {x y z : Point} {r : ℝ}
    (hzx : z ∈ ThickPoint.disc x r) (hzy : z ∈ ThickPoint.disc y r) :
    y ∈ coordinateSquare x ⌈2 * r⌉₊ := by
  have hzx' : ThickPoint.latticeDistance x z ≤ r := hzx
  have hzy' : ThickPoint.latticeDistance y z ≤ r := hzy
  have h1xz : |(((x.1 - z.1 : ℤ) : ℝ))| ≤ r :=
    (abs_first_sub_le_latticeDistance x z).trans hzx'
  have h1yz : |(((y.1 - z.1 : ℤ) : ℝ))| ≤ r :=
    (abs_first_sub_le_latticeDistance y z).trans hzy'
  have h2xz : |(((x.2 - z.2 : ℤ) : ℝ))| ≤ r :=
    (abs_second_sub_le_latticeDistance x z).trans hzx'
  have h2yz : |(((y.2 - z.2 : ℤ) : ℝ))| ≤ r :=
    (abs_second_sub_le_latticeDistance y z).trans hzy'
  have hceil : 2 * r ≤ (⌈2 * r⌉₊ : ℝ) := Nat.le_ceil (2 * r)
  have h1 : |(((x.1 - y.1 : ℤ) : ℝ))| ≤ (⌈2 * r⌉₊ : ℝ) := by
    calc
      |(((x.1 - y.1 : ℤ) : ℝ))| =
          |(((x.1 - z.1 : ℤ) : ℝ) + ((z.1 - y.1 : ℤ) : ℝ))| := by
            congr 1
            push_cast
            ring
      _ ≤ |(((x.1 - z.1 : ℤ) : ℝ))| + |(((z.1 - y.1 : ℤ) : ℝ))| := abs_add_le _ _
      _ = |(((x.1 - z.1 : ℤ) : ℝ))| + |(((y.1 - z.1 : ℤ) : ℝ))| := by
            rw [show (((z.1 - y.1 : ℤ) : ℝ)) = -(((y.1 - z.1 : ℤ) : ℝ)) by
              push_cast
              ring, abs_neg]
      _ ≤ r + r := add_le_add h1xz h1yz
      _ = 2 * r := by ring
      _ ≤ (⌈2 * r⌉₊ : ℝ) := hceil
  have h2 : |(((x.2 - y.2 : ℤ) : ℝ))| ≤ (⌈2 * r⌉₊ : ℝ) := by
    calc
      |(((x.2 - y.2 : ℤ) : ℝ))| =
          |(((x.2 - z.2 : ℤ) : ℝ) + ((z.2 - y.2 : ℤ) : ℝ))| := by
            congr 1
            push_cast
            ring
      _ ≤ |(((x.2 - z.2 : ℤ) : ℝ))| + |(((z.2 - y.2 : ℤ) : ℝ))| := abs_add_le _ _
      _ = |(((x.2 - z.2 : ℤ) : ℝ))| + |(((y.2 - z.2 : ℤ) : ℝ))| := by
            rw [show (((z.2 - y.2 : ℤ) : ℝ)) = -(((y.2 - z.2 : ℤ) : ℝ)) by
              push_cast
              ring, abs_neg]
      _ ≤ r + r := add_le_add h2xz h2yz
      _ = 2 * r := by ring
      _ ≤ (⌈2 * r⌉₊ : ℝ) := hceil
  rw [mem_coordinateSquare]
  have h1bounds := abs_le.mp h1
  have h2bounds := abs_le.mp h2
  have h1upper : x.1 - y.1 ≤ (⌈2 * r⌉₊ : ℤ) := by
    exact_mod_cast h1bounds.2
  have h1lower : -(⌈2 * r⌉₊ : ℤ) ≤ x.1 - y.1 := by
    exact_mod_cast h1bounds.1
  have h2upper : x.2 - y.2 ≤ (⌈2 * r⌉₊ : ℤ) := by
    exact_mod_cast h2bounds.2
  have h2lower : -(⌈2 * r⌉₊ : ℤ) ≤ x.2 - y.2 := by
    exact_mod_cast h2bounds.1
  omega

lemma previousOverlapPartners_subset_coordinateSquare
    (U : Finset Point) (n : ℕ) (x : Point) (l : ℕ) :
    previousOverlapPartners U n x l ⊆
      coordinateSquare x ⌈2 * ThickPoint.scaleRadius n (l - 1)⌉₊ := by
  intro y hy
  obtain ⟨_, z, hzx, hzy⟩ := Finset.mem_filter.mp hy
  exact mem_coordinateSquare_of_common_disc_point
    hzx hzy

/-- Exact `O(r²)` lattice count for the overlap neighbourhood. -/
lemma card_previousOverlapPartners_le
    (U : Finset Point) (n : ℕ) (x : Point) (l : ℕ) :
    (previousOverlapPartners U n x l).card ≤
      (2 * ⌈2 * ThickPoint.scaleRadius n (l - 1)⌉₊ + 1) ^ 2 := by
  exact (Finset.card_le_card
    (previousOverlapPartners_subset_coordinateSquare U n x l)).trans_eq
      (card_coordinateSquare x _)

lemma not_separated_iff_exists_common_point (n k : ℕ) (x y : Point) :
    ¬ SeparatedAt n k x y ↔
      ∃ z, z ∈ ThickPoint.disc x (ThickPoint.scaleRadius n k) ∧
        z ∈ ThickPoint.disc y (ThickPoint.scaleRadius n k) := by
  simp [SeparatedAt, Set.not_disjoint_iff]

/-- Except for the outermost level `1`, first separation at `l` forces overlap
at the preceding scale.  This is the exact geometric input behind the pair
count in HLOZ (A.5). -/
lemma levelPartners_subset_previousOverlap
    (U : Finset Point) (n : ℕ) (x : Point) {l : ℕ}
    (hlower : 2 ≤ l) (hupper : l ≤ n + 1) :
    levelPartners U n x l ⊆ previousOverlapPartners U n x l := by
  intro y hy
  have hlevel := (mem_levelPartners.mp hy).2
  have hfirst : FirstSeparatedAt n x y l :=
    firstSeparatedAt_iff.mpr ⟨hlevel, hupper⟩
  have hindex : l - 1 ∈ scaleIndices n := by
    simp only [scaleIndices, Finset.mem_Icc]
    omega
  have hnot := hfirst.2 (l - 1) hindex (by omega)
  exact Finset.mem_filter.mpr
    ⟨(mem_levelPartners.mp hy).1,
      (not_separated_iff_exists_common_point n (l - 1) x y).mp hnot⟩

lemma card_levelPartners_le_previousOverlap
    (U : Finset Point) (n : ℕ) (x : Point) {l : ℕ}
    (hlower : 2 ≤ l) (hupper : l ≤ n + 1) :
    (levelPartners U n x l).card ≤ (previousOverlapPartners U n x l).card :=
  Finset.card_le_card (levelPartners_subset_previousOverlap U n x hlower hupper)

/-- The finite counting step after a uniform bound on overlap neighborhoods:
the number of ordered level-`l` pairs is at most `|U| B`. -/
theorem pairCountAtLevel_le_mul
    (U : Finset Point) (n : ℕ) {l B : ℕ}
    (hlower : 2 ≤ l) (hupper : l ≤ n + 1)
    (hB : ∀ x ∈ U, (previousOverlapPartners U n x l).card ≤ B) :
    pairCountAtLevel U n l ≤ U.card * B := by
  calc
    pairCountAtLevel U n l
        ≤ ∑ _x ∈ U, B := by
      apply Finset.sum_le_sum
      intro x hx
      exact (card_levelPartners_le_previousOverlap U n x hlower hupper).trans (hB x hx)
    _ = U.card * B := by simp

/-- The paper's finite pair-count bound, with all constants explicit: for a
fixed first coordinate there are at most `(2 ceil(2r)+1)^2` partners, hence
at most `|U|` times this quantity ordered pairs at level `l`. -/
theorem pairCountAtLevel_le_latticeArea
    (U : Finset Point) (n : ℕ) {l : ℕ}
    (hlower : 2 ≤ l) (hupper : l ≤ n + 1) :
    pairCountAtLevel U n l ≤ U.card *
      (2 * ⌈2 * ThickPoint.scaleRadius n (l - 1)⌉₊ + 1) ^ 2 := by
  apply pairCountAtLevel_le_mul U n hlower hupper
  intro x hx
  exact card_previousOverlapPartners_le U n x l

/-- A sentinel-level partner still overlaps at the terminal scale `n+1`.
This is the close-pair input used for HLOZ (A.6), and avoids the much weaker
quadratic bound by `U.card ^ 2`. -/
lemma levelPartners_sentinel_subset_previousOverlap
    (U : Finset Point) (n : ℕ) (x : Point) :
    levelPartners U n x (n + 2) ⊆
      previousOverlapPartners U n x (n + 2) := by
  intro y hy
  have hlevel := (mem_levelPartners.mp hy).2
  have hempty : ¬(separatingIndices n x y).Nonempty :=
    separationLevel_eq_sentinel_iff.mp hlevel
  have hindex : n + 1 ∈ scaleIndices n := by
    simp [scaleIndices]
  have hnot : ¬SeparatedAt n (n + 1) x y := by
    intro hsep
    exact hempty ⟨n + 1, Finset.mem_filter.mpr ⟨hindex, hsep⟩⟩
  exact Finset.mem_filter.mpr
    ⟨(mem_levelPartners.mp hy).1,
      (not_separated_iff_exists_common_point n (n + 1) x y).mp hnot⟩

lemma card_levelPartners_sentinel_le
    (U : Finset Point) (n : ℕ) (x : Point) :
    (levelPartners U n x (n + 2)).card ≤
      (2 * ⌈2 * ThickPoint.scaleRadius n (n + 1)⌉₊ + 1) ^ 2 := by
  exact (Finset.card_le_card
    (levelPartners_sentinel_subset_previousOverlap U n x)).trans
      (card_previousOverlapPartners_le U n x (n + 2))

/-- Exact close-pair count at the sentinel level. -/
theorem pairCountAtSentinel_le_latticeArea (U : Finset Point) (n : ℕ) :
    pairCountAtLevel U n (n + 2) ≤ U.card *
      (2 * ⌈2 * ThickPoint.scaleRadius n (n + 1)⌉₊ + 1) ^ 2 := by
  calc
    pairCountAtLevel U n (n + 2) ≤
        ∑ _x ∈ U,
          (2 * ⌈2 * ThickPoint.scaleRadius n (n + 1)⌉₊ + 1) ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      exact card_levelPartners_sentinel_le U n x
    _ = U.card *
        (2 * ⌈2 * ThickPoint.scaleRadius n (n + 1)⌉₊ + 1) ^ 2 := by
      simp

/-! ## A fully explicit finite separation-envelope sum -/

/-- The exact lattice-count envelope used at each separation level.  Level
`1` has no preceding overlap restriction; levels `2,...,n+1` use the
preceding regular radius; the sentinel uses the terminal radius. -/
def levelPairCountBound (U : Finset Point) (n l : ℕ) : ℕ :=
  if l = 1 then U.card ^ 2
  else if l = n + 2 then
    U.card * (2 * ⌈2 * ThickPoint.scaleRadius n (n + 1)⌉₊ + 1) ^ 2
  else
    U.card * (2 * ⌈2 * ThickPoint.scaleRadius n (l - 1)⌉₊ + 1) ^ 2

lemma pairCountAtLevel_le_levelPairCountBound
    (U : Finset Point) (n l : ℕ) (hl : l ∈ Finset.Icc 1 (n + 2)) :
    pairCountAtLevel U n l ≤ levelPairCountBound U n l := by
  by_cases h1 : l = 1
  · subst l
    simpa [levelPairCountBound] using pairCountAtLevel_le_square U n 1
  by_cases hs : l = n + 2
  · subst l
    simpa [levelPairCountBound, h1] using pairCountAtSentinel_le_latticeArea U n
  · have hlower : 2 ≤ l := by
      have := (Finset.mem_Icc.mp hl).1
      omega
    have hupper : l ≤ n + 1 := by
      have := (Finset.mem_Icc.mp hl).2
      omega
    simpa [levelPairCountBound, h1, hs] using
      pairCountAtLevel_le_latticeArea U n hlower hupper

/-- A pointwise upper bound on a separation stratum sums to its ordered-pair
count times that upper bound. -/
lemma pairSumAtLevel_le_count_mul
    (U : Finset Point) (n l : ℕ) (w : Point → Point → ℝ) (B : ℝ)
    (hB : ∀ x ∈ U, ∀ y ∈ levelPartners U n x l, w x y ≤ B) :
    pairSumAtLevel U n l w ≤ (pairCountAtLevel U n l : ℝ) * B := by
  calc
    pairSumAtLevel U n l w ≤
        ∑ x ∈ U, ∑ _y ∈ levelPartners U n x l, B := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      exact hB x hx y hy
    _ = (pairCountAtLevel U n l : ℝ) * B := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_sum,
        pairCountAtLevel]
      rw [← Finset.sum_mul, mul_comm]

/-- Exact finite HLOZ separation summation.  Once the walk-specific annular
comparison supplies a nonnegative envelope `B l` for every pair first
separating at `l`, the complete double sum is bounded by the displayed,
fully explicit lattice-count sum. -/
theorem pairSum_le_explicit_separationEnvelope
    (U : Finset Point) (n : ℕ) (w : Point → Point → ℝ)
    (B : ℕ → ℝ) (hB0 : ∀ l ∈ Finset.Icc 1 (n + 2), 0 ≤ B l)
    (hw : ∀ x ∈ U, ∀ y ∈ U, w x y ≤ B (separationLevel n x y)) :
    (∑ x ∈ U, ∑ y ∈ U, w x y) ≤
      ∑ l ∈ Finset.Icc 1 (n + 2),
        (levelPairCountBound U n l : ℝ) * B l := by
  rw [pairSum_eq_sum_separationLevels U n w]
  apply Finset.sum_le_sum
  intro l hl
  calc
    pairSumAtLevel U n l w ≤
        (pairCountAtLevel U n l : ℝ) * B l := by
      apply pairSumAtLevel_le_count_mul
      intro x hx y hy
      exact hw x hx y (mem_levelPartners.mp hy).1 |>.trans_eq (by
        rw [(mem_levelPartners.mp hy).2])
    _ ≤ (levelPairCountBound U n l : ℝ) * B l := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast pairCountAtLevel_le_levelPairCountBound U n l hl)
        (hB0 l hl)

/-! ## Far/near decomposition at the HLOZ decorrelation cutoff -/

/-- Partners whose first separation occurs strictly after `k`.  This is the
entire close band, not merely the diagonal. -/
def nearPartners (U : Finset Point) (n : ℕ) (x : Point) (k : ℕ) : Finset Point :=
  U.filter fun y => k < separationLevel n x y

/-- Weighted contribution from all pairs which have not separated by `k`. -/
def nearPairSum {M : Type*} [AddCommMonoid M]
    (U : Finset Point) (n k : ℕ) (w : Point → Point → M) : M :=
  ∑ x ∈ U, ∑ y ∈ nearPartners U n x k, w x y

/-- Weighted contribution from pairs whose first separation is at most `k`. -/
def farPairSum {M : Type*} [AddCommMonoid M]
    (U : Finset Point) (n k : ℕ) (w : Point → Point → M) : M :=
  ∑ x ∈ U, ∑ y ∈ U with separationLevel n x y ≤ k, w x y

@[simp] lemma mem_nearPartners {U : Finset Point} {n k : ℕ} {x y : Point} :
    y ∈ nearPartners U n x k ↔ y ∈ U ∧ k < separationLevel n x y := by
  simp [nearPartners]

/-- The literal double sum splits into the separated and close bands. -/
theorem pairSum_eq_far_add_near {M : Type*} [AddCommMonoid M]
    (U : Finset Point) (n k : ℕ) (w : Point → Point → M) :
    (∑ x ∈ U, ∑ y ∈ U, w x y) =
      farPairSum U n k w + nearPairSum U n k w := by
  classical
  unfold farPairSum nearPairSum nearPartners
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := U) (p := fun y => separationLevel n x y ≤ k) (f := fun y => w x y)]
  apply congrArg (fun s =>
    (∑ y ∈ U with separationLevel n x y ≤ k, w x y) + s)
  apply Finset.sum_congr
  · ext y
    simp only [Finset.mem_filter, not_le]
  · intro y hy
    rfl

/-- A level larger than `k` means that the discs still overlap at `k`. -/
lemma not_separated_of_lt_separationLevel
    {n k : ℕ} {x y : Point} (hk : k ∈ scaleIndices n)
    (hkl : k < separationLevel n x y) :
    ¬ SeparatedAt n k x y := by
  by_cases hnonempty : (separatingIndices n x y).Nonempty
  · exact separationLevel_not_separated_before hnonempty hk hkl
  · intro hsep
    exact hnonempty ⟨k, Finset.mem_filter.mpr ⟨hk, hsep⟩⟩

/-- The complete close band is contained in one overlap neighbourhood at the
cutoff scale.  This is the counting observation behind HLOZ (A.6). -/
lemma nearPartners_subset_previousOverlap
    (U : Finset Point) (n : ℕ) (x : Point) {k : ℕ}
    (hk : k ∈ scaleIndices n) :
    nearPartners U n x k ⊆ previousOverlapPartners U n x (k + 1) := by
  intro y hy
  have hymem := (mem_nearPartners.mp hy).1
  have hnot := not_separated_of_lt_separationLevel hk (mem_nearPartners.mp hy).2
  have hoverlap := (not_separated_iff_exists_common_point n k x y).mp hnot
  simpa [previousOverlapPartners, hymem] using hoverlap

lemma card_nearPartners_le
    (U : Finset Point) (n : ℕ) (x : Point) {k : ℕ}
    (hk : k ∈ scaleIndices n) :
    (nearPartners U n x k).card ≤
      (2 * ⌈2 * ThickPoint.scaleRadius n k⌉₊ + 1) ^ 2 := by
  have hsubset := nearPartners_subset_previousOverlap U n x hk
  have hcard := Finset.card_le_card hsubset
  have harea := card_previousOverlapPartners_le U n x (k + 1)
  simpa using hcard.trans harea

/-- A convenient explicit polynomial envelope for the cutoff lattice area.
The constant `256` safely absorbs both ceiling operations and the factor two
in the overlap radius. -/
lemma latticeArea_le_256_mul_pow24
    {n k : ℕ}
    (hR : ThickPoint.scaleRadius n k ≤ 3 * (n + 1 : ℝ) ^ (12 : ℕ)) :
    (2 * ⌈2 * ThickPoint.scaleRadius n k⌉₊ + 1) ^ 2 ≤
      256 * (n + 1) ^ (24 : ℕ) := by
  let r := ThickPoint.scaleRadius n k
  let c := ⌈2 * r⌉₊
  have hr0 : 0 ≤ r := by dsimp [r]; exact scaleRadius_nonneg n k
  have hc : (c : ℝ) < 2 * r + 1 := by
    dsimp [c]
    exact Nat.ceil_lt_add_one (by positivity)
  have hbase : (1 : ℝ) ≤ (n + 1 : ℝ) ^ (12 : ℕ) := by
    have hn : (1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    exact one_le_pow₀ hn
  have hside : ((2 * c + 1 : ℕ) : ℝ) ≤
      16 * (n + 1 : ℝ) ^ (12 : ℕ) := by
    push_cast
    calc
      2 * (c : ℝ) + 1 ≤ 4 * r + 3 := by linarith
      _ ≤ 12 * (n + 1 : ℝ) ^ (12 : ℕ) + 3 := by linarith
      _ ≤ 16 * (n + 1 : ℝ) ^ (12 : ℕ) := by linarith
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (2 * c + 1 : ℕ))
    hside 2
  have hsq' : (((2 * c + 1 : ℕ) ^ 2 : ℕ) : ℝ) ≤
      ((256 * (n + 1) ^ (24 : ℕ) : ℕ) : ℝ) := by
    push_cast
    calc
      ((2 * (c : ℝ) + 1) ^ 2 : ℝ) ≤
          (16 * (n + 1 : ℝ) ^ (12 : ℕ)) ^ 2 := by
        simpa using hsq
      _ = 256 * (n + 1 : ℝ) ^ (24 : ℕ) := by ring
  exact_mod_cast hsq'

/-! ## Candidate-square normalization for the far strata -/

/-- The integer interval defining `U_n` retains at least half of its natural
side length.  This is the rounding estimate needed to compare an overlap
disc with the whole HLOZ candidate square. -/
lemma regularRadius_zero_le_two_mul_candidateInterval_card
    {n : ℕ} (hn : 2 ≤ n) :
    ThickPoint.regularRadius n 0 ≤
      2 * (ThickPoint.candidateInterval n).card := by
  let r : ℝ := ThickPoint.regularRadius n 0
  let a : ℤ := ⌈2 * r⌉
  let b : ℤ := ⌊3 * r⌋
  have hnReal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : (1 : ℝ) ≤ Real.exp (n : ℝ) := Real.one_le_exp (by positivity)
  have hpow : (2 : ℝ) ≤ (n : ℝ) ^ (9 : ℕ) := by
    calc
      (2 : ℝ) ≤ 2 ^ (9 : ℕ) := by norm_num
      _ ≤ (n : ℝ) ^ (9 : ℕ) := pow_le_pow_left₀ (by norm_num) hnReal 9
  have hrEq : r = Real.exp (n : ℝ) * (n : ℝ) ^ (9 : ℕ) := by
    simp [r, ThickPoint.regularRadius]
  have hrTwo : 2 ≤ r := by rw [hrEq]; nlinarith [Real.exp_pos (n : ℝ)]
  have hab : a ≤ b := by
    rw [← Int.cast_le (R := ℝ)]
    dsimp [a, b]
    push_cast
    linarith [Int.ceil_lt_add_one (2 * r), Int.lt_floor_add_one (3 * r)]
  have hcardZ : ((ThickPoint.candidateInterval n).card : ℤ) = b + 1 - a := by
    unfold ThickPoint.candidateInterval
    change ((Finset.Icc a b).card : ℤ) = b + 1 - a
    exact Int.card_Icc_of_le a b (by omega)
  have hround : r - 1 < ((ThickPoint.candidateInterval n).card : ℝ) := by
    rw [show ((ThickPoint.candidateInterval n).card : ℝ) =
        ((b + 1 - a : ℤ) : ℝ) by exact_mod_cast hcardZ]
    dsimp [a, b]
    push_cast
    linarith [Int.ceil_lt_add_one (2 * r), Int.lt_floor_add_one (3 * r)]
  dsimp [r] at hround hrTwo ⊢
  linarith

/-- All close levels are counted once, giving one lattice-area factor rather
than an additional factor equal to the number of close levels. -/
theorem nearPairSum_le_latticeArea_mul
    (U : Finset Point) (n : ℕ) {k : ℕ} (w : Point → Point → ℝ) (Q : ℝ)
    (hk : k ∈ scaleIndices n) (hQ : 0 ≤ Q)
    (hw : ∀ x ∈ U, ∀ y ∈ nearPartners U n x k, w x y ≤ Q) :
    nearPairSum U n k w ≤
      (U.card : ℝ) *
        ((2 * ⌈2 * ThickPoint.scaleRadius n k⌉₊ + 1) ^ 2 : ℕ) * Q := by
  unfold nearPairSum
  calc
    (∑ x ∈ U, ∑ y ∈ nearPartners U n x k, w x y) ≤
        ∑ x ∈ U, ∑ _y ∈ nearPartners U n x k, Q := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      exact hw x hx y hy
    _ = ∑ x ∈ U, ((nearPartners U n x k).card : ℝ) * Q := by
      simp
    _ ≤ ∑ _x ∈ U,
        (((2 * ⌈2 * ThickPoint.scaleRadius n k⌉₊ + 1) ^ 2 : ℕ) : ℝ) * Q := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_nearPartners_le U n x hk) hQ
    _ = (U.card : ℝ) *
        ((2 * ⌈2 * ThickPoint.scaleRadius n k⌉₊ + 1) ^ 2 : ℕ) * Q := by
      simp [mul_assoc]

/-- The far band is exactly the sum of separation strata `1,...,k`. -/
theorem farPairSum_eq_sum_separationLevels
    {M : Type*} [AddCommMonoid M]
    (U : Finset Point) (n k : ℕ) (w : Point → Point → M) :
    farPairSum U n k w =
      ∑ l ∈ Finset.Icc 1 k, pairSumAtLevel U n l w := by
  classical
  unfold farPairSum
  calc
    (∑ x ∈ U, ∑ y ∈ U with separationLevel n x y ≤ k, w x y) =
        ∑ x ∈ U, ∑ l ∈ Finset.Icc 1 k,
          ∑ y ∈ U with separationLevel n x y = l, w x y := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (Finset.sum_fiberwise_of_maps_to
        (s := U.filter fun y => separationLevel n x y ≤ k)
        (t := Finset.Icc 1 k)
        (g := separationLevel n x)
        (fun y hy => Finset.mem_Icc.mpr
          ⟨Nat.one_le_iff_ne_zero.mpr (separationLevel_ne_zero n x y),
            (Finset.mem_filter.mp hy).2⟩)
        (fun y => w x y)).symm.trans (by
          apply Finset.sum_congr rfl
          intro l hl
          apply Finset.sum_congr
          · ext y
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨⟨hy, _⟩, hlevel⟩
              exact ⟨hy, hlevel⟩
            · rintro ⟨hy, hlevel⟩
              exact ⟨⟨hy, by simpa [hlevel] using (Finset.mem_Icc.mp hl).2⟩,
                hlevel⟩
          · intro y hy
            rfl)
    _ = ∑ l ∈ Finset.Icc 1 k, pairSumAtLevel U n l w := by
      rw [Finset.sum_comm]
      simp only [pairSumAtLevel, levelPartners, Finset.sum_filter]

/-- Complete non-asymptotic HLOZ (A.5)--(A.6) counting reduction: the far
levels retain their explicit separation envelope, while the whole close band
is paid for by one cutoff-scale lattice area. -/
theorem pairSum_le_farEnvelope_add_nearArea
    (U : Finset Point) (n : ℕ) {k : ℕ} (w : Point → Point → ℝ)
    (B : ℕ → ℝ) (Q : ℝ) (hk : k ∈ scaleIndices n)
    (hB0 : ∀ l ∈ Finset.Icc 1 k, 0 ≤ B l) (hQ : 0 ≤ Q)
    (hfar : ∀ x ∈ U, ∀ y ∈ U, separationLevel n x y ≤ k →
      w x y ≤ B (separationLevel n x y))
    (hnear : ∀ x ∈ U, ∀ y ∈ nearPartners U n x k, w x y ≤ Q) :
    (∑ x ∈ U, ∑ y ∈ U, w x y) ≤
      (∑ l ∈ Finset.Icc 1 k,
        (levelPairCountBound U n l : ℝ) * B l) +
      (U.card : ℝ) *
        ((2 * ⌈2 * ThickPoint.scaleRadius n k⌉₊ + 1) ^ 2 : ℕ) * Q := by
  rw [pairSum_eq_far_add_near U n k w,
    farPairSum_eq_sum_separationLevels U n k w]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro l hl
    calc
      pairSumAtLevel U n l w ≤ (pairCountAtLevel U n l : ℝ) * B l := by
        apply pairSumAtLevel_le_count_mul
        intro x hx y hy
        have hlevel := (mem_levelPartners.mp hy).2
        have hxy := hfar x hx y (mem_levelPartners.mp hy).1 (by
          simpa [hlevel] using (Finset.mem_Icc.mp hl).2)
        simpa only [hlevel] using hxy
      _ ≤ (levelPairCountBound U n l : ℝ) * B l := by
        apply mul_le_mul_of_nonneg_right _ (hB0 l hl)
        have hlUpper := (Finset.mem_Icc.mp hl).2
        have hkUpper := (Finset.mem_Icc.mp hk).2
        have hsentinel : l ≤ n + 2 := by omega
        exact_mod_cast pairCountAtLevel_le_levelPairCountBound U n l
          (Finset.mem_Icc.mpr
            ⟨(Finset.mem_Icc.mp hl).1, hsentinel⟩)
  · exact nearPairSum_le_latticeArea_mul U n w Q hk hQ hnear

/-! ## Combining pair counts with the exact finite Harnack reduction -/

/-- If every pair carries a mixture of the same product kernel, Condition
`(∗)` from `AppendixDecoupling` bounds the entire separation stratum by its
cardinality times the reference-kernel upper bound. -/
theorem pairSumAtLevel_mix_productKernel_le
    {ι : Type*} [Fintype ι] {m : ℕ}
    (U : Finset Point) (n l : ℕ)
    (ν : Point → Point → AppendixDecoupling.EntranceDistribution (Fin m → ι))
    {ε : ℝ} (hεnonneg : 0 ≤ ε) (hε : ε ≤ 1)
    (q : Fin m → ι → ℝ)
    (hqnonneg : ∀ j y, 0 ≤ q j y)
    (hqstar : ∀ j, AppendixDecoupling.ConditionStar ε (q j))
    (reference : Fin m → ι)
    (hsmall : (1 + ε) ^ m ≤ 2) :
    pairSumAtLevel U n l
        (fun x y => (ν x y).mix (AppendixDecoupling.productKernel q)) ≤
      (pairCountAtLevel U n l : ℝ) *
        ((1 + 2 * (m : ℝ) * ε) * AppendixDecoupling.productKernel q reference) := by
  let upper :=
    (1 + 2 * (m : ℝ) * ε) * AppendixDecoupling.productKernel q reference
  have hmix : ∀ x y,
      (ν x y).mix (AppendixDecoupling.productKernel q) ≤ upper := by
    intro x y
    exact (AppendixDecoupling.mix_productKernel_conditionStar_linear
      (ν x y) hεnonneg hε q hqnonneg hqstar reference hsmall).2
  calc
    pairSumAtLevel U n l
        (fun x y => (ν x y).mix (AppendixDecoupling.productKernel q))
        ≤ ∑ x ∈ U, ∑ _y ∈ levelPartners U n x l, upper := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      exact hmix x y
    _ = (pairCountAtLevel U n l : ℝ) * upper := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_sum,
        pairCountAtLevel]
      rw [← Finset.sum_mul, mul_comm]
    _ = (pairCountAtLevel U n l : ℝ) *
        ((1 + 2 * (m : ℝ) * ε) * AppendixDecoupling.productKernel q reference) := rfl

/-- The same bound after inserting the exact lattice-area estimate for a
non-outermost separation level. -/
theorem pairSumAtLevel_mix_productKernel_le_latticeArea
    {ι : Type*} [Fintype ι] {m : ℕ}
    (U : Finset Point) (n : ℕ) {l : ℕ}
    (hlower : 2 ≤ l) (hupper : l ≤ n + 1)
    (ν : Point → Point → AppendixDecoupling.EntranceDistribution (Fin m → ι))
    {ε : ℝ} (hεnonneg : 0 ≤ ε) (hε : ε ≤ 1)
    (q : Fin m → ι → ℝ)
    (hqnonneg : ∀ j y, 0 ≤ q j y)
    (hqstar : ∀ j, AppendixDecoupling.ConditionStar ε (q j))
    (reference : Fin m → ι)
    (hsmall : (1 + ε) ^ m ≤ 2) :
    pairSumAtLevel U n l
        (fun x y => (ν x y).mix (AppendixDecoupling.productKernel q)) ≤
      (U.card * (2 * ⌈2 * ThickPoint.scaleRadius n (l - 1)⌉₊ + 1) ^ 2 : ℕ) *
        ((1 + 2 * (m : ℝ) * ε) * AppendixDecoupling.productKernel q reference) := by
  have hkernel : 0 ≤
      (1 + 2 * (m : ℝ) * ε) * AppendixDecoupling.productKernel q reference := by
    exact mul_nonneg (by positivity) (AppendixDecoupling.productKernel_nonneg hqnonneg reference)
  refine (pairSumAtLevel_mix_productKernel_le U n l ν hεnonneg hε q
    hqnonneg hqstar reference hsmall).trans ?_
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast pairCountAtLevel_le_latticeArea U n hlower hupper) hkernel

/-! ## Conditional decomposition, corresponding to HLOZ (A.16) -/

variable {Omega : Type*} [mOmega : MeasurableSpace Omega]

/-- Conditional probability of `B`, represented by the conditional
expectation of its real indicator. -/
def conditionalEventProbability (mu : Measure Omega) (m : MeasurableSpace Omega)
    (B : Set Omega) : Omega → ℝ :=
  mu[SecondMoment.eventIndicator B | m]

/-- Conditioning on the excursion sigma-algebra is an exact identity whenever
`A` is measurable in that sigma-algebra.  This is the abstract equality used
in the first line of HLOZ (A.16). -/
theorem measureReal_inter_eq_setIntegral_conditionalEventProbability
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    [SigmaFinite (mu.trim hm)]
    {A B : Set Omega} (hA : @MeasurableSet Omega m A)
    (hB : @MeasurableSet Omega mOmega B) :
    mu.real (B ∩ A) =
      ∫ omega in A, @conditionalEventProbability Omega mOmega mu m B omega ∂mu := by
  let _ : MeasurableSpace Omega := mOmega
  have hBint : Integrable (SecondMoment.eventIndicator B) mu := by
    apply Integrable.of_bound
      (SecondMoment.measurable_eventIndicator hB).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun omega => by
      by_cases h : omega ∈ B <;> simp [SecondMoment.eventIndicator, h]
  rw [conditionalEventProbability, setIntegral_condExp hm hBint hA]
  have hindicator := SecondMoment.integral_eventIndicator
    (mu := mu.restrict A) hB
  rw [measureReal_restrict_apply hB] at hindicator
  exact hindicator.symm

/-- A finite-valued count decomposes a truncated pair event into disjoint
count fibres.  Unlike a union bound, this is an equality. -/
theorem measureReal_inter_eq_sum_countFibers
    (mu : Measure Omega) [IsFiniteMeasure mu]
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (N : Omega → ι)
    {A B : Set Omega}
    (hN : ∀ i ∈ I, MeasurableSet (N ⁻¹' {i}))
    (hcover : ∀ omega ∈ B ∩ A, N omega ∈ I) :
    mu.real (B ∩ A) =
      ∑ i ∈ I, mu.real ((N ⁻¹' {i}) ∩ (B ∩ A)) := by
  classical
  have hNI : MeasurableSet (N ⁻¹' (I : Set ι)) := by
    have hset : N ⁻¹' (I : Set ι) = ⋃ i ∈ I, N ⁻¹' {i} := by
      ext omega
      simp
    rw [hset]
    exact I.measurableSet_biUnion hN
  have hsum := MeasureTheory.sum_measureReal_preimage_singleton
    (μ := mu.restrict (B ∩ A)) I (f := N) hN
  have hpreimage : N ⁻¹' (I : Set ι) ∩ (B ∩ A) = B ∩ A := by
    ext omega
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨hcover omega h, h⟩
  calc
    mu.real (B ∩ A) = mu.real (N ⁻¹' (I : Set ι) ∩ (B ∩ A)) := by rw [hpreimage]
    _ = (mu.restrict (B ∩ A)).real (N ⁻¹' (I : Set ι)) :=
      (measureReal_restrict_apply hNI).symm
    _ = ∑ i ∈ I, (mu.restrict (B ∩ A)).real (N ⁻¹' {i}) := hsum.symm
    _ = ∑ i ∈ I, mu.real ((N ⁻¹' {i}) ∩ (B ∩ A)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact measureReal_restrict_apply (hN i hi)

/-- The full finite conditional decomposition.  It first partitions by the
count `N`, then replaces the future event on each fibre by its conditional
probability.  This is the formal measure-theoretic content of HLOZ (A.16),
before any Harnack or Markov-chain estimate is applied. -/
theorem measureReal_inter_eq_sum_countFiber_conditionalIntegrals
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    [SigmaFinite (mu.trim hm)]
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (N : Omega → ι)
    {A B : Set Omega}
    (hA : @MeasurableSet Omega m A) (hB : @MeasurableSet Omega mOmega B)
    (hN : ∀ i ∈ I, @MeasurableSet Omega m (N ⁻¹' {i}))
    (hcover : ∀ omega ∈ B ∩ A, N omega ∈ I) :
    mu.real (B ∩ A) =
      ∑ i ∈ I, ∫ omega in A ∩ (N ⁻¹' {i}),
        @conditionalEventProbability Omega mOmega mu m B omega ∂mu := by
  let _ : MeasurableSpace Omega := mOmega
  rw [measureReal_inter_eq_sum_countFibers mu I N
    (fun i hi => hm _ (hN i hi)) hcover]
  apply Finset.sum_congr rfl
  intro i hi
  have hAi : MeasurableSet[m] (A ∩ (N ⁻¹' {i})) := hA.inter (hN i hi)
  have hcond := measureReal_inter_eq_setIntegral_conditionalEventProbability
    mu m hm hAi hB
  simpa [inter_assoc, inter_left_comm, inter_comm] using hcond

end

end Erdos1165.AppendixPair
