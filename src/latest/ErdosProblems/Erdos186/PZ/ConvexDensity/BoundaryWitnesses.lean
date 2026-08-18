/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.SeparatedCells
import ErdosProblems.Erdos186.PZ.ConvexDensity.BoundaryGraph

/-!
# Boundary witnesses supplied by separated heavy cells

This file turns the supporting separator for a heavy cell into a genuine
boundary witness.  The separator controls the distinguished threefold
thickening and all the *original* other cells.  Accordingly, the natural
set whose boundary it exposes is the convex hull of their union.  Separation
from the convex hull of all other *thickened* cells would require an
additional hypothesis controlling those thickenings.

The final part packages pointwise witnesses over a finite index set and gives
both injective and bounded-multiplicity counting interfaces.  It also proves
the geometric bridge used by the boundary-graph argument: a sufficiently
high frontier point over the interior of an inner ball is the upper endpoint
of its vertical fiber.
-/

open Set Filter
open scoped Topology
open scoped Topology

namespace Erdos186.PZ.ConvexDensity

open ConvexGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable {ι : Type*} [DecidableEq ι]

/-- The local source consisting of the distinguished threefold thickening
and all the other original cells. -/
def localThickenedSource (I : Finset ι) (C : ι → Set E)
    (center : ι → E) (r : ℝ) (i : ι) : Set E :=
  Metric.closedBall (center i) (3 * r) ∪ otherCells I C i

/-- The convex body locally exposed by the heavy-cell separator. -/
def localThickenedHull (I : Finset ι) (C : ι → Set E)
    (center : ι → E) (r : ℝ) (i : ι) : Set E :=
  convexHull ℝ (localThickenedSource I C center r i)

/-- Union of all original cells whose labels were retained. -/
def retainedCells (I : Finset ι) (C : ι → Set E) : Set E :=
  ⋃ j : {j // j ∈ I}, C j.1

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [DecidableEq ι] in
@[simp] theorem mem_retainedCells_iff
    {I : Finset ι} {C : ι → Set E} {z : E} :
    z ∈ retainedCells I C ↔ ∃ j ∈ I, z ∈ C j := by
  classical
  simp [retainedCells]

/-- The one common hull of all original retained cells. -/
def commonCellHull (I : Finset ι) (C : ι → Set E) : Set E :=
  convexHull ℝ (retainedCells I C)

omit [CompleteSpace E] [DecidableEq ι] in
theorem convex_commonCellHull (I : Finset ι) (C : ι → Set E) :
    Convex ℝ (commonCellHull I C) :=
  convex_convexHull ℝ _

omit [CompleteSpace E] in
theorem convex_localThickenedHull (I : Finset ι) (C : ι → Set E)
    (center : ι → E) (r : ℝ) (i : ι) :
    Convex ℝ (localThickenedHull I C center r i) :=
  convex_convexHull ℝ _

omit [CompleteSpace E] in
theorem closedBall_subset_localThickenedHull (I : Finset ι) (C : ι → Set E)
    (center : ι → E) (r : ℝ) (i : ι) :
    Metric.closedBall (center i) (3 * r) ⊆
      localThickenedHull I C center r i := by
  intro z hz
  exact subset_convexHull ℝ (localThickenedSource I C center r i) (Or.inl hz)

/-- A maximizer of a nonzero continuous linear functional on a set is not an
interior point of that set.  Membership therefore makes it a frontier point.
-/
theorem mem_frontier_of_isMaxOn_continuousLinearMap
    {S : Set E} {z : E} (ell : E →L[ℝ] ℝ)
    (hell : ell ≠ 0) (hz : z ∈ S)
    (hmax : ∀ w ∈ S, ell w ≤ ell z) :
    z ∈ frontier S := by
  rw [mem_frontier_iff_notMem_interior hz]
  intro hzint
  obtain ⟨u, hunorm, hellu⟩ := exists_unit_normal ell hell
  have hellnorm : 0 < ‖ell‖ := norm_pos_iff.mpr hell
  have hnhds : S ∈ 𝓝 z := mem_interior_iff_mem_nhds.mp hzint
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let q : E := z + (ε / 2) • u
  have hqdist : dist q z < ε := by
    rw [dist_eq_norm]
    simp only [q, add_sub_cancel_left, norm_smul, hunorm, mul_one]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ε / 2)]
    linarith
  have hqS : q ∈ S := hball (Metric.mem_ball.mpr hqdist)
  have hqapply : ell q = ell z + (ε / 2) * ‖ell‖ := by
    simp [q, hellu]
  nlinarith [hmax q hqS]

/-- The supporting separator of a heavy cell can be realized at the extremal
point of its threefold ball.  This point is outside the hull of the other
original cells and is an exposed frontier point of the local thickened hull.
-/
theorem exists_localExposedBoundaryWitness_of_heavy_cells
    {X : Finset E} {delta r : ℝ} {I : Finset ι}
    {C : ι → Set E} {Y : ι → Finset E}
    {center a : ι → E} {i : ι}
    (hr : 0 ≤ r)
    (hi : i ∈ I)
    (hX : IsDeltaConvexPosition delta X)
    (haX : ∀ j ∈ I, a j ∈ X)
    (haC : ∀ j ∈ I, a j ∈ C j)
    (hYX : ∀ j ∈ I, Y j ⊆ X)
    (hYC : ∀ j ∈ I, (Y j : Set E) ⊆ C j)
    (hheavy : ∀ j ∈ I, delta * X.card < (Y j).card)
    (hcell : ∀ j ∈ I, C j ⊆ Metric.closedBall (center j) r) :
    ∃ (ell : E →L[ℝ] ℝ) (z : E),
      ell ≠ 0 ∧
      z ∈ Metric.closedBall (center i) (3 * r) ∧
      z ∉ convexHull ℝ (otherCells I C i) ∧
      z ∈ frontier (localThickenedHull I C center r i) ∧
      ∀ w ∈ localThickenedHull I C center r i, ell w ≤ ell z := by
  obtain ⟨ell, level, z₀, hell, _hlevel, hother, hz₀ball, hz₀level⟩ :=
    exists_supporting_separator_of_heavy_cells
      hr hi hX haX haC hYX hYC hheavy hcell
  obtain ⟨u, hunorm, hellu⟩ := exists_unit_normal ell hell
  let z : E := center i + (3 * r) • u
  have hzball : z ∈ Metric.closedBall (center i) (3 * r) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp [z, norm_smul, hunorm, abs_of_nonneg hr]
  have hzapply : ell z = ell (center i) + ‖ell‖ * (3 * r) := by
    simp [z, hellu]
    ring
  have hballMax : ∀ w ∈ Metric.closedBall (center i) (3 * r), ell w ≤ ell z := by
    intro w hw
    rw [hzapply]
    exact apply_le_center_add_opNorm_mul ell hw
  have hzlevel : level ≤ ell z := hz₀level.trans (hballMax z₀ hz₀ball)
  have hsourceMax : ∀ w ∈ localThickenedSource I C center r i, ell w ≤ ell z := by
    intro w hw
    rcases hw with hw | hw
    · exact hballMax w hw
    · exact (le_of_lt (hother w hw)).trans hzlevel
  have hhullMax : ∀ w ∈ localThickenedHull I C center r i, ell w ≤ ell z := by
    intro w hw
    exact convexHull_min hsourceMax (convex_halfSpace_le ell.isLinear (ell z)) hw
  have hzHull : z ∈ localThickenedHull I C center r i :=
    closedBall_subset_localThickenedHull I C center r i hzball
  have hzOutside : z ∉ convexHull ℝ (otherCells I C i) := by
    have hotherSub : otherCells I C i ⊆ strictLowerHalfspace ell level := hother
    have hhullBelow : convexHull ℝ (otherCells I C i) ⊆
        strictLowerHalfspace ell level :=
      convexHull_min hotherSub (convex_strictLowerHalfspace ell level)
    intro hzOtherHull
    exact (not_lt_of_ge hzlevel) (hhullBelow hzOtherHull)
  exact ⟨ell, z, hell, hzball, hzOutside,
    mem_frontier_of_isMaxOn_continuousLinearMap ell hell hzHull hhullMax,
    hhullMax⟩

omit [DecidableEq ι] in
/-- A heavy cell supplies a localized boundary point of the **single common
hull** of all original retained cells.

The strict radius assumption makes the extremal point of the threefold ball
strictly higher than every point of the distinguished radius-`r` cell; the
separator already puts every other cell below it.  Thus this extremal point
is outside the common hull.  Starting from `a i` inside that hull, closedness
gives the first visible point on the segment to the exterior point.  The
whole segment remains in the threefold ball, so the frontier point is still
localized at cell `i`.
-/
theorem exists_commonHullBoundaryWitness_of_heavy_cells
    {X : Finset E} {delta r : ℝ} {I : Finset ι}
    {C : ι → Set E} {Y : ι → Finset E}
    {center a : ι → E} {i : ι}
    (hr : 0 < r)
    (hi : i ∈ I)
    (hX : IsDeltaConvexPosition delta X)
    (haX : ∀ j ∈ I, a j ∈ X)
    (haC : ∀ j ∈ I, a j ∈ C j)
    (hYX : ∀ j ∈ I, Y j ⊆ X)
    (hYC : ∀ j ∈ I, (Y j : Set E) ⊆ C j)
    (hheavy : ∀ j ∈ I, delta * X.card < (Y j).card)
    (hcell : ∀ j ∈ I, C j ⊆ Metric.closedBall (center j) r)
    (hclosed : IsClosed (commonCellHull I C)) :
    ∃ z ∈ Metric.closedBall (center i) (3 * r),
      z ∈ frontier (commonCellHull I C) := by
  classical
  obtain ⟨ell, level, z₀, hell, _hlevel, hother, hz₀ball, hz₀level⟩ :=
    exists_supporting_separator_of_heavy_cells
      hr.le hi hX haX haC hYX hYC hheavy hcell
  obtain ⟨u, hunorm, hellu⟩ := exists_unit_normal ell hell
  let zₑ : E := center i + (3 * r) • u
  have hellnorm : 0 < ‖ell‖ := norm_pos_iff.mpr hell
  have hzₑball : zₑ ∈ Metric.closedBall (center i) (3 * r) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp [zₑ, norm_smul, hunorm, abs_of_nonneg hr.le]
  have hzₑapply : ell zₑ = ell (center i) + ‖ell‖ * (3 * r) := by
    simp [zₑ, hellu]
    ring
  have hballMax : ∀ w ∈ Metric.closedBall (center i) (3 * r),
      ell w ≤ ell zₑ := by
    intro w hw
    rw [hzₑapply]
    exact apply_le_center_add_opNorm_mul ell hw
  have hzₑlevel : level ≤ ell zₑ := hz₀level.trans (hballMax z₀ hz₀ball)
  have hallBelow : retainedCells I C ⊆ strictLowerHalfspace ell (ell zₑ) := by
    intro w hw
    obtain ⟨j, hjI, hwC⟩ := mem_retainedCells_iff.mp hw
    by_cases hji : j = i
    · subst j
      have hwball : w ∈ Metric.closedBall (center i) r := hcell i hi hwC
      have hwupper : ell w ≤ ell (center i) + ‖ell‖ * r :=
        apply_le_center_add_opNorm_mul ell hwball
      calc
        ell w ≤ ell (center i) + ‖ell‖ * r := hwupper
        _ < ell (center i) + ‖ell‖ * (3 * r) := by
          simpa [add_comm] using
            (add_lt_add_left
              (mul_lt_mul_of_pos_left (show r < 3 * r by nlinarith) hellnorm)
              (ell (center i)))
        _ = ell zₑ := hzₑapply.symm
    · exact (hother w (mem_otherCells_iff.mpr ⟨j, hjI, hji, hwC⟩)).trans_le
        hzₑlevel
  have hzₑOutside : zₑ ∉ commonCellHull I C := by
    have hhullBelow : commonCellHull I C ⊆
        strictLowerHalfspace ell (ell zₑ) :=
      convexHull_min hallBelow (convex_strictLowerHalfspace ell (ell zₑ))
    intro hzHull
    exact (lt_irrefl (ell zₑ)) (hhullBelow hzHull)
  have haiHull : a i ∈ commonCellHull I C := by
    apply subset_convexHull ℝ (retainedCells I C)
    exact mem_retainedCells_iff.mpr ⟨i, hi, haC i hi⟩
  obtain ⟨z, hzHull, hzBetween, hzVisible⟩ :=
    hclosed.exists_wbtw_isVisible haiHull zₑ
  have haiBall : a i ∈ Metric.closedBall (center i) (3 * r) := by
    apply Metric.closedBall_subset_closedBall (show r ≤ 3 * r by nlinarith)
    exact hcell i hi (haC i hi)
  have hzball : z ∈ Metric.closedBall (center i) (3 * r) :=
    (convex_closedBall (center i) (3 * r)).segment_subset
      hzₑball haiBall hzBetween.mem_segment
  have hzFrontier : z ∈ frontier (commonCellHull I C) := by
    rw [mem_frontier_iff_notMem_interior hzHull]
    intro hzInterior
    have hzEq : zₑ = z := hzVisible.eq_of_mem_interior hzInterior
    apply hzₑOutside
    rw [hzEq]
    exact hzHull
  exact ⟨z, hzball, hzFrontier⟩

/-- The literal equation-(3) witness, obtained from the named non-containment
theorem.  This interface retains the pairwise-disjoint cell hypothesis used
in the decomposition. -/
theorem exists_outsideWitness_of_heavy_cells
    {X : Finset E} {delta r : ℝ} {I : Finset ι}
    {C : ι → Set E} {Y : ι → Finset E}
    {center a : ι → E} {i : ι}
    (hr : 0 ≤ r)
    (hi : i ∈ I)
    (hdisjoint : PairwiseDisjointCellsOn I C)
    (hX : IsDeltaConvexPosition delta X)
    (haX : ∀ j ∈ I, a j ∈ X)
    (haC : ∀ j ∈ I, a j ∈ C j)
    (hYX : ∀ j ∈ I, Y j ⊆ X)
    (hYC : ∀ j ∈ I, (Y j : Set E) ⊆ C j)
    (hheavy : ∀ j ∈ I, delta * X.card < (Y j).card)
    (hcell : ∀ j ∈ I, C j ⊆ Metric.closedBall (center j) r) :
    ∃ z ∈ Metric.closedBall (center i) (3 * r),
      z ∉ convexHull ℝ (otherCells I C i) := by
  exact not_subset.mp
    (thickenedCell_not_subset_convexHull_others
      hr hi hdisjoint hX haX haC hYX hYC hheavy hcell)

/-- Simultaneous choice of one local boundary witness for every retained
heavy cell.  The subtype domain keeps the labels even when two geometric
witnesses happen to coincide. -/
theorem exists_indexed_localBoundaryWitnesses_of_heavy_cells
    {X : Finset E} {delta r : ℝ} {I : Finset ι}
    {C : ι → Set E} {Y : ι → Finset E}
    {center a : ι → E}
    (hr : 0 ≤ r)
    (hX : IsDeltaConvexPosition delta X)
    (haX : ∀ j ∈ I, a j ∈ X)
    (haC : ∀ j ∈ I, a j ∈ C j)
    (hYX : ∀ j ∈ I, Y j ⊆ X)
    (hYC : ∀ j ∈ I, (Y j : Set E) ⊆ C j)
    (hheavy : ∀ j ∈ I, delta * X.card < (Y j).card)
    (hcell : ∀ j ∈ I, C j ⊆ Metric.closedBall (center j) r) :
    ∃ witness : {j // j ∈ I} → E, ∀ (j : {j // j ∈ I}),
      witness j ∈ Metric.closedBall (center j.1) (3 * r) ∧
      witness j ∉ convexHull ℝ (otherCells I C j.1) ∧
      witness j ∈ frontier (localThickenedHull I C center r j.1) := by
  classical
  have hexists : ∀ j : {j // j ∈ I}, ∃ z : E,
      z ∈ Metric.closedBall (center j.1) (3 * r) ∧
      z ∉ convexHull ℝ (otherCells I C j.1) ∧
      z ∈ frontier (localThickenedHull I C center r j.1) := by
    intro j
    obtain ⟨ell, z, _hell, hzball, hzoutside, hzfrontier, _hmax⟩ :=
      exists_localExposedBoundaryWitness_of_heavy_cells
        hr j.property hX haX haC hYX hYC hheavy hcell
    exact ⟨z, hzball, hzoutside, hzfrontier⟩
  choose witness hwitness using hexists
  exact ⟨witness, hwitness⟩

omit [DecidableEq ι] in
/-- Simultaneous, label-preserving choice of localized witnesses on the
frontier of one common compact hull.  Keeping the subtype labels means that
no geometric deduplication, and hence no multiplicity estimate, is needed in
later pigeonhole arguments. -/
theorem exists_indexed_commonHullBoundaryWitnesses_of_heavy_cells
    {X : Finset E} {delta r : ℝ} {I : Finset ι}
    {C : ι → Set E} {Y : ι → Finset E}
    {center a : ι → E}
    (hr : 0 < r)
    (hX : IsDeltaConvexPosition delta X)
    (haX : ∀ j ∈ I, a j ∈ X)
    (haC : ∀ j ∈ I, a j ∈ C j)
    (hYX : ∀ j ∈ I, Y j ⊆ X)
    (hYC : ∀ j ∈ I, (Y j : Set E) ⊆ C j)
    (hheavy : ∀ j ∈ I, delta * X.card < (Y j).card)
    (hcell : ∀ j ∈ I, C j ⊆ Metric.closedBall (center j) r)
    (hcompact : IsCompact (commonCellHull I C)) :
    ∃ witness : {j // j ∈ I} → E, ∀ (j : {j // j ∈ I}),
      witness j ∈ Metric.closedBall (center j.1) (3 * r) ∧
      witness j ∈ frontier (commonCellHull I C) := by
  classical
  have hexists : ∀ j : {j // j ∈ I}, ∃ z : E,
      z ∈ Metric.closedBall (center j.1) (3 * r) ∧
      z ∈ frontier (commonCellHull I C) := by
    intro j
    exact exists_commonHullBoundaryWitness_of_heavy_cells
      hr j.property hX haX haC hYX hYC hheavy hcell hcompact.isClosed
  choose witness hwitness using hexists
  exact ⟨witness, hwitness⟩

/-- The finite set of geometric values of a subtype-indexed family of
witnesses. -/
noncomputable def indexedWitnessSet
    (I : Finset ι) (witness : {j // j ∈ I} → E) : Finset E := by
  classical
  exact I.attach.image witness

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [DecidableEq ι] in
@[simp] theorem mem_indexedWitnessSet_iff
    {I : Finset ι} {witness : {j // j ∈ I} → E} {z : E} :
    z ∈ indexedWitnessSet I witness ↔ ∃ j, witness j = z := by
  classical
  simp [indexedWitnessSet]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [DecidableEq ι] in
/-- Membership in pairwise disjoint labelled regions forces the geometric
witness map to be injective. -/
theorem injective_of_mem_pairwiseDisjoint_regions
    {I : Finset ι} {T : ι → Set E}
    {witness : {j // j ∈ I} → E}
    (hw : ∀ (j : {j // j ∈ I}), witness j ∈ T j.1)
    (hdisjoint : (I : Set ι).PairwiseDisjoint T) :
    Function.Injective witness := by
  classical
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have hd : Disjoint (T i.1) (T j.1) := hdisjoint i.property j.property hne
  have hwj : witness i ∈ T j.1 := by
    rw [hij]
    exact hw j
  exact Set.disjoint_left.mp hd (hw i) hwj

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [DecidableEq ι] in
/-- Under disjoint labelled regions, no witness is lost when labels are
forgotten. -/
theorem card_indexedWitnessSet_eq_of_pairwiseDisjoint_regions
    {I : Finset ι} {T : ι → Set E}
    {witness : {j // j ∈ I} → E}
    (hw : ∀ (j : {j // j ∈ I}), witness j ∈ T j.1)
    (hdisjoint : (I : Set ι).PairwiseDisjoint T) :
    (indexedWitnessSet I witness).card = I.card := by
  classical
  have hinj := injective_of_mem_pairwiseDisjoint_regions hw hdisjoint
  simpa [indexedWitnessSet] using
    (Finset.card_image_of_injOn (s := I.attach) hinj.injOn)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [DecidableEq ι] in
/-- Ball-specialized injective counting interface for the heavy-cell
witnesses. -/
theorem card_indexedWitnessSet_eq_of_pairwiseDisjoint_thickenedBalls
    {I : Finset ι} {center : ι → E} {r : ℝ}
    {witness : {j // j ∈ I} → E}
    (hw : ∀ (j : {j // j ∈ I}),
      witness j ∈ Metric.closedBall (center j.1) (3 * r))
    (hdisjoint : (I : Set ι).PairwiseDisjoint
      fun j ↦ Metric.closedBall (center j) (3 * r)) :
    (indexedWitnessSet I witness).card = I.card :=
  card_indexedWitnessSet_eq_of_pairwiseDisjoint_regions hw hdisjoint

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [DecidableEq ι] in
/-- Number of labelled regions containing a point. -/
noncomputable def indexedRegionOverlapCount
    (I : Finset ι) (T : ι → Set E) (z : E) : ℕ := by
  classical
  exact (I.attach.filter fun j ↦ z ∈ T j.1).card

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [DecidableEq ι] in
/-- Explicit bounded multiplicity is enough for counting even when the
thickened cells overlap.  This is the form used when disjointness is only
available for the original cells. -/
theorem card_le_mul_card_indexedWitnessSet_of_overlap
    {I : Finset ι} {T : ι → Set E}
    {witness : {j // j ∈ I} → E} {M : ℕ}
    (hw : ∀ (j : {j // j ∈ I}), witness j ∈ T j.1)
    (hoverlap : ∀ z : E, indexedRegionOverlapCount I T z ≤ M) :
    I.card ≤ M * (indexedWitnessSet I witness).card := by
  classical
  have hfiber : ∀ z ∈ I.attach.image witness,
      (I.attach.filter fun j ↦ witness j = z).card ≤ M := by
    intro z hz
    have hsub : (I.attach.filter fun j ↦ witness j = z) ⊆
        I.attach.filter fun j ↦ z ∈ T j.1 := by
      intro j hj
      rw [Finset.mem_filter] at hj ⊢
      refine ⟨hj.1, ?_⟩
      rw [← hj.2]
      exact hw j
    exact (Finset.card_le_card hsub).trans (by
      simpa [indexedRegionOverlapCount] using hoverlap z)
  simpa [indexedWitnessSet] using
    (Finset.card_le_mul_card_image (s := I.attach) M hfiber)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [DecidableEq ι] in
/-- Ball-specialized bounded-overlap counting interface for the heavy-cell
witnesses. -/
theorem card_le_mul_card_indexedWitnessSet_of_thickenedBall_overlap
    {I : Finset ι} {center : ι → E} {r : ℝ}
    {witness : {j // j ∈ I} → E} {M : ℕ}
    (hw : ∀ (j : {j // j ∈ I}),
      witness j ∈ Metric.closedBall (center j.1) (3 * r))
    (hoverlap : ∀ z : E,
      indexedRegionOverlapCount I
        (fun j ↦ Metric.closedBall (center j) (3 * r)) z ≤ M) :
    I.card ≤ M * (indexedWitnessSet I witness).card :=
  card_le_mul_card_indexedWitnessSet_of_overlap hw hoverlap

/-! ## From an inner-ball cap to the upper boundary graph -/

/-- An affine combination of two points on the same vertical line stays on
that line, with the corresponding affine combination of heights. -/
theorem affineCombination_appendCoordinate_sameBase {n : ℕ}
    (x : EuclideanPoint n) (s t a b : ℝ) (hab : a + b = 1) :
    a • appendCoordinate x s + b • appendCoordinate x t =
      appendCoordinate x (a * s + b * t) := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [smul_eq_mul]
  · simp [smul_eq_mul, ← add_mul, hab]

/-- A positive-height frontier point whose base lies in the open base ball
of an inner ball is the upper endpoint of its vertical fibre.  The reason is
that a strictly higher endpoint would express the frontier point as a strict
convex combination of an interior point of the inner ball and a point of
`P`. -/
theorem eq_upperBoundaryPoint_of_frontier_of_positiveHeight
    {n : ℕ} {P : Set (EuclideanPoint (n + 1))}
    (hcompact : IsCompact P) (hconvex : Convex ℝ P)
    {rho : ℝ} (hinner : Metric.closedBall 0 rho ⊆ P)
    {z : EuclideanPoint (n + 1)} (hzfront : z ∈ frontier P)
    (hbase : ‖baseCoordinates z‖ < rho)
    (hheight : 0 < lastCoordinate z) :
    z = upperBoundaryPoint P hcompact (baseCoordinates z) := by
  have hzP : z ∈ P := by
    rw [← hcompact.isClosed.closure_eq]
    exact frontier_subset_closure hzfront
  let x : EuclideanPoint n := baseCoordinates z
  let t : ℝ := lastCoordinate z
  let h : ℝ := upperBoundaryValue P hcompact x
  have hxbase : x ∈ projectedBase P := ⟨z, hzP, rfl⟩
  have hupperP : upperBoundaryPoint P hcompact x ∈ P :=
    upperBoundaryPoint_mem hcompact hxbase
  have htle : t ≤ h := by
    exact le_upperBoundaryValue hcompact hzP rfl
  have hge : h ≤ t := by
    by_contra hnot
    have hlt : t < h := lt_of_not_ge hnot
    have hhpos : 0 < h := hheight.trans hlt
    let q : EuclideanPoint (n + 1) := appendCoordinate x 0
    have hqball : q ∈ Metric.ball (0 : EuclideanPoint (n + 1)) rho := by
      simpa [q, x, Metric.mem_ball, dist_zero_right] using hbase
    have hqinterior : q ∈ interior P :=
      interior_mono hinner (Metric.ball_subset_interior_closedBall hqball)
    let a : ℝ := 1 - t / h
    let b : ℝ := t / h
    have ha : 0 < a := by
      dsimp [a]
      have : t / h < 1 := (div_lt_one hhpos).mpr hlt
      linarith
    have hb : 0 ≤ b := by
      exact div_nonneg hheight.le hhpos.le
    have hab : a + b = 1 := by
      dsimp [a, b]
      ring
    have hcombo :
        a • q + b • upperBoundaryPoint P hcompact x ∈ interior P :=
      hconvex.combo_interior_self_mem_interior
        hqinterior hupperP ha hb hab
    have hcomboEq :
        a • q + b • upperBoundaryPoint P hcompact x = z := by
      rw [show q = appendCoordinate x 0 by rfl,
        ← appendCoordinate_upperBoundaryValue P hcompact x,
        affineCombination_appendCoordinate_sameBase x 0 h a b hab]
      have hlast : a * 0 + b * h = t := by
        simp [b, hhpos.ne']
      rw [hlast]
      change appendCoordinate (baseCoordinates z) (lastCoordinate z) = z
      exact appendCoordinate_baseCoordinates_lastCoordinate z
    have hznotInterior : z ∉ interior P :=
      (mem_frontier_iff_notMem_interior hzP).mp hzfront
    exact hznotInterior (hcomboEq ▸ hcombo)
  exact eq_upperBoundaryPoint_of_mem_of_height_eq hcompact hzP rfl
    (le_antisymm htle hge)

/-- A convenient cap form of the previous theorem.  Height at least half the
inner radius is positive, while an open base-ball hypothesis supplies the
interior anchor. -/
theorem eq_upperBoundaryPoint_of_frontier_of_innerBall
    {n : ℕ} {P : Set (EuclideanPoint (n + 1))}
    (hcompact : IsCompact P) (hconvex : Convex ℝ P)
    {rho : ℝ} (hrho : 0 < rho)
    (hinner : Metric.closedBall 0 rho ⊆ P)
    {z : EuclideanPoint (n + 1)} (hzfront : z ∈ frontier P)
    (hbase : ‖baseCoordinates z‖ < rho)
    (hheight : rho / 2 ≤ lastCoordinate z) :
    z = upperBoundaryPoint P hcompact (baseCoordinates z) := by
  apply eq_upperBoundaryPoint_of_frontier_of_positiveHeight
    hcompact hconvex hinner hzfront hbase
  exact (half_pos hrho).trans_le hheight

/-- Height version of `eq_upperBoundaryPoint_of_frontier_of_innerBall`, ready
for rewriting cap-selected points as values of the concave roof function. -/
theorem lastCoordinate_eq_upperBoundaryValue_of_frontier_of_innerBall
    {n : ℕ} {P : Set (EuclideanPoint (n + 1))}
    (hcompact : IsCompact P) (hconvex : Convex ℝ P)
    {rho : ℝ} (hrho : 0 < rho)
    (hinner : Metric.closedBall 0 rho ⊆ P)
    {z : EuclideanPoint (n + 1)} (hzfront : z ∈ frontier P)
    (hbase : ‖baseCoordinates z‖ < rho)
    (hheight : rho / 2 ≤ lastCoordinate z) :
    lastCoordinate z =
      upperBoundaryValue P hcompact (baseCoordinates z) := by
  have hzEq := eq_upperBoundaryPoint_of_frontier_of_innerBall
    hcompact hconvex hrho hinner hzfront hbase hheight
  calc
    lastCoordinate z =
        lastCoordinate (upperBoundaryPoint P hcompact (baseCoordinates z)) :=
      congrArg lastCoordinate hzEq
    _ = upperBoundaryValue P hcompact (baseCoordinates z) := rfl

end

end Erdos186.PZ.ConvexDensity
