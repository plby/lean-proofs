/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 957: finite-distance definitions

This module isolates the exact finite metric and graph-theoretic API
needed to state Problem 957.  A distance is *determined* only by two distinct
points, and `multiplicity A r` counts unordered pairs at distance `r`.
-/

open Metric
open scoped EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos957

/-- The Euclidean plane. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The finite set of distances determined by distinct pairs of points of `A`.

The product contains ordered pairs, but `Finset.image` removes both the
orientation duplication and repetitions of the same numerical distance. -/
noncomputable def distanceSet (A : Finset Point) : Finset ℝ := by
  classical
  exact ((A.product A).filter fun p ↦ p.1 ≠ p.2).image fun p ↦ dist p.1 p.2

/-- Membership in `distanceSet` is the expected distinct-pair condition. -/
@[simp]
theorem mem_distanceSet {A : Finset Point} {r : ℝ} :
    r ∈ distanceSet A ↔
      ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ dist x y = r := by
  classical
  constructor
  · intro hr
    obtain ⟨p, hp, hdist⟩ := Finset.mem_image.mp hr
    obtain ⟨hpA, hpne⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hpA
    exact ⟨p.1, hx, p.2, hy, hpne, hdist⟩
  · rintro ⟨x, hx, y, hy, hxy, hdist⟩
    apply Finset.mem_image.mpr
    exact ⟨(x, y), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩, hdist⟩

/-- Two points in `A` determine a member of `distanceSet A`. -/
theorem dist_mem_distanceSet {A : Finset Point} {x y : Point}
    (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) :
    dist x y ∈ distanceSet A :=
  mem_distanceSet.mpr ⟨x, hx, y, hy, hxy, rfl⟩

/-- A point set with at least two elements determines at least one distance. -/
theorem distanceSet_nonempty {A : Finset Point} (hA : 2 ≤ A.card) :
    (distanceSet A).Nonempty := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  exact ⟨dist x y, dist_mem_distanceSet hx hy hxy⟩

/-- A finite set determines a distance exactly when it has at least two
points. -/
theorem distanceSet_nonempty_iff {A : Finset Point} :
    (distanceSet A).Nonempty ↔ 2 ≤ A.card := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨x, hx, y, hy, hxy, -⟩ := mem_distanceSet.mp hr
    have hcard : 1 < A.card :=
      Finset.one_lt_card.mpr ⟨x, hx, y, hy, hxy⟩
    omega
  · exact distanceSet_nonempty

/-- The least distance determined by a set of at least two points. -/
noncomputable def minDist (A : Finset Point) (hA : 2 ≤ A.card) : ℝ :=
  (distanceSet A).min' (distanceSet_nonempty hA)

/-- The greatest distance determined by a set of at least two points. -/
noncomputable def maxDist (A : Finset Point) (hA : 2 ≤ A.card) : ℝ :=
  (distanceSet A).max' (distanceSet_nonempty hA)

@[simp]
theorem minDist_mem_distanceSet (A : Finset Point) (hA : 2 ≤ A.card) :
    minDist A hA ∈ distanceSet A :=
  Finset.min'_mem _ _

@[simp]
theorem maxDist_mem_distanceSet (A : Finset Point) (hA : 2 ≤ A.card) :
    maxDist A hA ∈ distanceSet A :=
  Finset.max'_mem _ _

/-- `minDist` is a lower bound for every determined distance. -/
theorem minDist_le_of_mem {A : Finset Point} (hA : 2 ≤ A.card)
    {r : ℝ} (hr : r ∈ distanceSet A) :
    minDist A hA ≤ r :=
  Finset.min'_le _ _ hr

/-- `maxDist` is an upper bound for every determined distance. -/
theorem le_maxDist_of_mem {A : Finset Point} (hA : 2 ≤ A.card)
    {r : ℝ} (hr : r ∈ distanceSet A) :
    r ≤ maxDist A hA :=
  Finset.le_max' _ _ hr

theorem minDist_le_dist {A : Finset Point} (hA : 2 ≤ A.card)
    {x y : Point} (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) :
    minDist A hA ≤ dist x y :=
  minDist_le_of_mem hA (dist_mem_distanceSet hx hy hxy)

theorem dist_le_maxDist {A : Finset Point} (hA : 2 ≤ A.card)
    {x y : Point} (hx : x ∈ A) (hy : y ∈ A) (hxy : x ≠ y) :
    dist x y ≤ maxDist A hA :=
  le_maxDist_of_mem hA (dist_mem_distanceSet hx hy hxy)

theorem minDist_le_maxDist (A : Finset Point) (hA : 2 ≤ A.card) :
    minDist A hA ≤ maxDist A hA :=
  minDist_le_of_mem hA (maxDist_mem_distanceSet A hA)

/-- Every determined distance is strictly positive. -/
theorem distance_pos_of_mem {A : Finset Point} {r : ℝ}
    (hr : r ∈ distanceSet A) : 0 < r := by
  obtain ⟨x, -, y, -, hxy, hdist⟩ := mem_distanceSet.mp hr
  rw [← hdist]
  exact dist_pos.mpr hxy

theorem minDist_pos (A : Finset Point) (hA : 2 ≤ A.card) :
    0 < minDist A hA :=
  distance_pos_of_mem (minDist_mem_distanceSet A hA)

theorem maxDist_pos (A : Finset Point) (hA : 2 ≤ A.card) :
    0 < maxDist A hA :=
  distance_pos_of_mem (maxDist_mem_distanceSet A hA)

/-- A proof-independent predicate saying that `r` is the least distance
determined by `A`. -/
def IsMinimumDistance (A : Finset Point) (r : ℝ) : Prop :=
  r ∈ distanceSet A ∧ ∀ s ∈ distanceSet A, r ≤ s

/-- A proof-independent predicate saying that `r` is the greatest distance
determined by `A`. -/
def IsMaximumDistance (A : Finset Point) (r : ℝ) : Prop :=
  r ∈ distanceSet A ∧ ∀ s ∈ distanceSet A, s ≤ r

theorem isMinimumDistance_minDist (A : Finset Point) (hA : 2 ≤ A.card) :
    IsMinimumDistance A (minDist A hA) := by
  refine ⟨minDist_mem_distanceSet A hA, ?_⟩
  exact fun _ hr ↦ minDist_le_of_mem hA hr

theorem isMaximumDistance_maxDist (A : Finset Point) (hA : 2 ≤ A.card) :
    IsMaximumDistance A (maxDist A hA) := by
  refine ⟨maxDist_mem_distanceSet A hA, ?_⟩
  exact fun _ hr ↦ le_maxDist_of_mem hA hr

/-- The least determined distance is unique. -/
theorem IsMinimumDistance.eq_minDist {A : Finset Point} {r : ℝ}
    (hr : IsMinimumDistance A r) (hA : 2 ≤ A.card) :
    r = minDist A hA := by
  apply le_antisymm
  · exact hr.2 _ (minDist_mem_distanceSet A hA)
  · exact minDist_le_of_mem hA hr.1

/-- The greatest determined distance is unique. -/
theorem IsMaximumDistance.eq_maxDist {A : Finset Point} {r : ℝ}
    (hr : IsMaximumDistance A r) (hA : 2 ≤ A.card) :
    r = maxDist A hA := by
  apply le_antisymm
  · exact le_maxDist_of_mem hA hr.1
  · exact hr.2 _ (maxDist_mem_distanceSet A hA)

theorem isMinimumDistance_iff_eq_minDist {A : Finset Point}
    (hA : 2 ≤ A.card) {r : ℝ} :
    IsMinimumDistance A r ↔ r = minDist A hA := by
  constructor
  · exact fun hr ↦ hr.eq_minDist hA
  · rintro rfl
    exact isMinimumDistance_minDist A hA

theorem isMaximumDistance_iff_eq_maxDist {A : Finset Point}
    (hA : 2 ≤ A.card) {r : ℝ} :
    IsMaximumDistance A r ↔ r = maxDist A hA := by
  constructor
  · exact fun hr ↦ hr.eq_maxDist hA
  · rintro rfl
    exact isMaximumDistance_maxDist A hA

theorem IsMinimumDistance.pos {A : Finset Point} {r : ℝ}
    (hr : IsMinimumDistance A r) : 0 < r :=
  distance_pos_of_mem hr.1

theorem IsMaximumDistance.pos {A : Finset Point} {r : ℝ}
    (hr : IsMaximumDistance A r) : 0 < r :=
  distance_pos_of_mem hr.1

/-- A pair of points realizes the least determined distance. -/
theorem exists_pair_dist_eq_minDist (A : Finset Point) (hA : 2 ≤ A.card) :
    ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ dist x y = minDist A hA :=
  mem_distanceSet.mp (minDist_mem_distanceSet A hA)

/-- A pair of points realizes the greatest determined distance. -/
theorem exists_pair_dist_eq_maxDist (A : Finset Point) (hA : 2 ≤ A.card) :
    ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ dist x y = maxDist A hA :=
  mem_distanceSet.mp (maxDist_mem_distanceSet A hA)

/-- The graph whose edges are the unordered pairs in `A` at distance `r`.

The explicit `x ≠ y` is essential: without it the relation need not be
loopless when `r = 0`. -/
noncomputable def distanceGraph (A : Finset Point) (r : ℝ) :
    SimpleGraph {x // x ∈ A} where
  Adj x y := x ≠ y ∧ dist (x : Point) (y : Point) = r
  symm.symm := by
    intro x y h
    exact ⟨h.1.symm, by simpa [dist_comm] using h.2⟩
  loopless.irrefl := by
    intro x h
    exact h.1 rfl

noncomputable instance distanceGraph.instDecidableRelAdj
    (A : Finset Point) (r : ℝ) : DecidableRel (distanceGraph A r).Adj :=
  Classical.decRel _

@[simp]
theorem distanceGraph_adj (A : Finset Point) (r : ℝ)
    (x y : {x // x ∈ A}) :
    (distanceGraph A r).Adj x y ↔
      x ≠ y ∧ dist (x : Point) (y : Point) = r :=
  Iff.rfl

/-- The number of unordered pairs of points of `A` at distance `r`. -/
noncomputable def multiplicity (A : Finset Point) (r : ℝ) : ℕ :=
  (distanceGraph A r).edgeFinset.card

/-- A distance multiplicity never exceeds the total number of unordered
pairs of points. -/
theorem multiplicity_le_choose (A : Finset Point) (r : ℝ) :
    multiplicity A r ≤ A.card.choose 2 := by
  classical
  simpa [multiplicity] using
    (distanceGraph A r).card_edgeFinset_le_card_choose_two

/-- A numerical distance is determined exactly when its distance graph has
at least one edge. -/
theorem multiplicity_pos_iff_mem_distanceSet {A : Finset Point} {r : ℝ} :
    0 < multiplicity A r ↔ r ∈ distanceSet A := by
  classical
  constructor
  · intro h
    obtain ⟨e, he⟩ : (distanceGraph A r).edgeFinset.Nonempty :=
      Finset.card_pos.mp h
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hadj : (distanceGraph A r).Adj x y := by
          simpa [SimpleGraph.mem_edgeSet] using he
        obtain ⟨hxy, hdist⟩ := hadj
        exact mem_distanceSet.mpr
          ⟨x.1, x.2, y.1, y.2, fun h ↦ hxy (Subtype.ext h), hdist⟩
  · intro hr
    obtain ⟨x, hx, y, hy, hxy, hdist⟩ := mem_distanceSet.mp hr
    let xs : {z // z ∈ A} := ⟨x, hx⟩
    let ys : {z // z ∈ A} := ⟨y, hy⟩
    have hxys : xs ≠ ys := by
      intro h
      exact hxy (congrArg Subtype.val h)
    have hadj : (distanceGraph A r).Adj xs ys := ⟨hxys, hdist⟩
    rw [multiplicity, Finset.card_pos]
    refine ⟨s(xs, ys), ?_⟩
    simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hadj

theorem one_le_multiplicity_of_mem {A : Finset Point} {r : ℝ}
    (hr : r ∈ distanceSet A) : 1 ≤ multiplicity A r :=
  (multiplicity_pos_iff_mem_distanceSet.mpr hr)

theorem minDist_multiplicity_pos (A : Finset Point) (hA : 2 ≤ A.card) :
    0 < multiplicity A (minDist A hA) :=
  multiplicity_pos_iff_mem_distanceSet.mpr (minDist_mem_distanceSet A hA)

theorem maxDist_multiplicity_pos (A : Finset Point) (hA : 2 ≤ A.card) :
    0 < multiplicity A (maxDist A hA) :=
  multiplicity_pos_iff_mem_distanceSet.mpr (maxDist_mem_distanceSet A hA)

end Erdos957
