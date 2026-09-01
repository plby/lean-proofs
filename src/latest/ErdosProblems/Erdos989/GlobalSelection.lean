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

import ErdosProblems.Erdos989.Core
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order
import Mathlib.Tactic.Linarith

/-!
# Compactness for global finite-alphabet selections

This file proves an abstract globalization step that can be used once a finite
construction has supplied the necessary finite-family estimates. A local
condition consists of a finite support and
an arbitrary predicate on assignments to that support.  Since the candidate alphabet is finite
and discrete, its satisfaction set in the full product space is closed.  Tychonoff compactness
then turns finite satisfiability into one assignment satisfying every local condition.

The result is deliberately stated independently of any probabilistic or discrepancy estimate.
For a possible application to Erdős problem 989, the cell type is `PlaneCell`, the candidate
alphabet is a finite grid in the unit square, and the constraints are finite-support disk-count
conditions.  The compactness theorem does not prove that those conditions are finitely
satisfiable.
-/

open Set

namespace Erdos989
namespace GlobalSelection

universe u v w

/-- A condition on a global assignment which reads only finitely many coordinates. -/
structure LocalConstraint (Cell : Type u) (Candidate : Type v) where
  /-- Coordinates read by the condition. -/
  support : Finset Cell
  /-- The predicate imposed on the restriction of the assignment to `support`. -/
  accepts : (support → Candidate) → Prop

namespace LocalConstraint

variable {Cell : Type u} {Candidate : Type v}

/-- A global assignment satisfies a local constraint when its restriction to the finite support
is accepted. -/
def Satisfied (c : LocalConstraint Cell Candidate) (x : Cell → Candidate) : Prop :=
  c.accepts (fun i ↦ x i)

/-- The set of global assignments satisfying a local constraint. -/
def satisfyingSet (c : LocalConstraint Cell Candidate) : Set (Cell → Candidate) :=
  {x | c.Satisfied x}

variable [TopologicalSpace Candidate] [DiscreteTopology Candidate]

/-- A finite-support condition over a discrete alphabet is closed in the product topology. -/
theorem isClosed_satisfyingSet (c : LocalConstraint Cell Candidate) :
    IsClosed c.satisfyingSet := by
  let restrict : (Cell → Candidate) → (c.support → Candidate) :=
    fun x i ↦ x i
  have hrestrict : Continuous restrict := by
    apply continuous_pi
    intro i
    simpa [restrict] using
      (continuous_apply (i : Cell) : Continuous fun x : Cell → Candidate ↦ x i)
  simpa [satisfyingSet, Satisfied, restrict] using
    (isClosed_discrete {y : c.support → Candidate | c.accepts y}).preimage hrestrict

end LocalConstraint

/-- Finite satisfiability of finite-support constraints over a finite discrete alphabet implies
simultaneous satisfiability of the whole family.

This is a compactness bridge from a separately proved finite-family theorem. -/
theorem exists_global_assignment_of_finitely_satisfiable
    {Cell : Type u} {Candidate : Type v} {Constraint : Type w}
    [TopologicalSpace Candidate] [DiscreteTopology Candidate] [Finite Candidate]
    (c : Constraint → LocalConstraint Cell Candidate)
    (hfinite : ∀ s : Finset Constraint, ∃ x : Cell → Candidate,
      ∀ k ∈ s, (c k).Satisfied x) :
    ∃ x : Cell → Candidate, ∀ k, (c k).Satisfied x := by
  let good : Constraint → Set (Cell → Candidate) :=
    fun k ↦ (c k).satisfyingSet
  have hclosed : ∀ k, IsClosed (good k) := by
    intro k
    exact (c k).isClosed_satisfyingSet
  have hfip : ∀ s : Finset Constraint,
      (Set.univ ∩ ⋂ k ∈ s, good k).Nonempty := by
    intro s
    obtain ⟨x, hx⟩ := hfinite s
    refine ⟨x, ⟨Set.mem_univ x, ?_⟩⟩
    simp only [Set.mem_iInter]
    intro k hk
    exact hx k hk
  obtain ⟨x, -, hx⟩ :=
    isCompact_univ.inter_iInter_nonempty good hclosed hfip
  refine ⟨x, fun k ↦ ?_⟩
  exact Set.mem_iInter.mp hx k

/-! ## Planar jittered selections -/

/-- The unit-square cells of the integer grid in the plane. -/
abbrev PlaneCell := ℤ × ℤ

/-- A jittered selection with a finite candidate alphabet chooses one candidate in every
integer-grid cell.  The interpretation of a candidate as an offset in the unit square is kept
separate from the compactness argument. -/
abbrev JitteredSelection (Candidate : Type v) := PlaneCell → Candidate

/-- The planar specialization of `exists_global_assignment_of_finitely_satisfiable`. -/
theorem exists_jitteredSelection_of_finitely_satisfiable
    {Candidate : Type v} {Constraint : Type w}
    [TopologicalSpace Candidate] [DiscreteTopology Candidate] [Finite Candidate]
    (c : Constraint → LocalConstraint PlaneCell Candidate)
    (hfinite : ∀ s : Finset Constraint, ∃ x : JitteredSelection Candidate,
      ∀ k ∈ s, (c k).Satisfied x) :
    ∃ x : JitteredSelection Candidate, ∀ k, (c k).Satisfied x :=
  exists_global_assignment_of_finitely_satisfiable c hfinite

/-- Convert a selected candidate into the corresponding point of its integer-grid cell. -/
def pointAt {Candidate : Type v} (offset : Candidate → ℝ × ℝ)
    (x : JitteredSelection Candidate) (cell : PlaneCell) : ℝ × ℝ :=
  ((cell.1 : ℝ) + (offset (x cell)).1,
    (cell.2 : ℝ) + (offset (x cell)).2)

/-- Every selected point lies in its closed unit cell when all candidate offsets lie in the
closed unit square. -/
theorem pointAt_mem_unitCell {Candidate : Type v} (offset : Candidate → ℝ × ℝ)
    (hoffset : ∀ q, offset q ∈ Set.Icc (0, 0) (1, 1))
    (x : JitteredSelection Candidate) (cell : PlaneCell) :
    pointAt offset x cell ∈
      Set.Icc ((cell.1 : ℝ), (cell.2 : ℝ))
        ((cell.1 : ℝ) + 1, (cell.2 : ℝ) + 1) := by
  rcases hoffset (x cell) with ⟨hlo, hhi⟩
  have hxlo : 0 ≤ (offset (x cell)).1 := hlo.1
  have hylo : 0 ≤ (offset (x cell)).2 := hlo.2
  have hxhi : (offset (x cell)).1 ≤ 1 := hhi.1
  have hyhi : (offset (x cell)).2 ≤ 1 := hhi.2
  constructor
  · exact ⟨by dsimp [pointAt]; linarith, by dsimp [pointAt]; linarith⟩
  · exact ⟨by dsimp [pointAt]; linarith, by dsimp [pointAt]; linarith⟩

/-! ## Finite-support Euclidean disk constraints

The rest of this file records the precise interface between a finite probabilistic argument
and the compactness theorem above.  We deliberately allow an arbitrary finite set of candidate
locations in each cell.  This makes the statements apply both to a literal jittered grid and to
the successively finer finite alphabets used in a multiscale construction.
-/

/-- The Euclidean plane used by the discrepancy problem. -/
abbrev EuclideanPlane := EuclideanSpace ℝ (Fin 2)

/-- The standard identification of a pair of real coordinates with the Euclidean plane. -/
def pairToEuclideanPlane (p : ℝ × ℝ) : EuclideanPlane :=
  WithLp.toLp 2 ![p.1, p.2]

@[simp] theorem pairToEuclideanPlane_apply_zero (p : ℝ × ℝ) :
    pairToEuclideanPlane p 0 = p.1 := by
  rfl

@[simp] theorem pairToEuclideanPlane_apply_one (p : ℝ × ℝ) :
    pairToEuclideanPlane p 1 = p.2 := by
  rfl

/-- The point selected by an assignment, for an arbitrary table of candidate locations. -/
def selectedPoint {Candidate : Type v}
    (location : PlaneCell → Candidate → EuclideanPlane)
    (x : JitteredSelection Candidate) (cell : PlaneCell) : EuclideanPlane :=
  location cell (x cell)

/-- Indices of the selected points which lie in a specified closed Euclidean disk. -/
def selectedIndicesInClosedBall {Candidate : Type v}
    (location : PlaneCell → Candidate → EuclideanPlane)
    (x : JitteredSelection Candidate) (center : EuclideanPlane) (radius : ℝ) :
    Set PlaneCell :=
  {cell | selectedPoint location x cell ∈ Metric.closedBall center radius}

/-- Number of selected indices in a closed disk.  The covering hypotheses below ensure that
this set is finite in every application. -/
noncomputable def selectedDiskCount {Candidate : Type v}
    (location : PlaneCell → Candidate → EuclideanPlane)
    (x : JitteredSelection Candidate) (center : EuclideanPlane) (radius : ℝ) : ℕ :=
  (selectedIndicesInClosedBall location x center radius).ncard

/-- Discrepancy of the index count in a closed Euclidean disk from its area. -/
noncomputable def selectedDiskError {Candidate : Type v}
    (location : PlaneCell → Candidate → EuclideanPlane)
    (x : JitteredSelection Candidate) (center : EuclideanPlane) (radius : ℝ) : ℝ :=
  |(selectedDiskCount location x center radius : ℝ) - Real.pi * radius ^ 2|

/-- A finite collection of cells supports a disk condition if it contains every cell having
at least one candidate location in the disk.  The quantification over all candidates, rather
than only a particular assignment, is what makes the resulting condition local. -/
def CoversClosedBall {Candidate : Type v}
    (location : PlaneCell → Candidate → EuclideanPlane)
    (center : EuclideanPlane) (radius : ℝ) (support : Finset PlaneCell) : Prop :=
  ∀ cell q, location cell q ∈ Metric.closedBall center radius → cell ∈ support

/-- The count seen by a local disk constraint. -/
noncomputable def localDiskCount {Candidate : Type v} (support : Finset PlaneCell)
    (location : PlaneCell → Candidate → EuclideanPlane)
    (center : EuclideanPlane) (radius : ℝ) (y : support → Candidate) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : support ↦
    location i.1 (y i) ∈ Metric.closedBall center radius).card

/-- A finite-radius disk-discrepancy condition, expressed as a `LocalConstraint`. -/
noncomputable def radiusSensitiveDiskConstraint {Candidate : Type v}
    (location : PlaneCell → Candidate → EuclideanPlane)
    (center : EuclideanPlane) (radius allowance : ℝ) (support : Finset PlaneCell) :
    LocalConstraint PlaneCell Candidate where
  support := support
  accepts := fun y ↦
    |(localDiskCount support location center radius y : ℝ) - Real.pi * radius ^ 2| ≤
      allowance

/-- A supporting finset contains the selected indices in the corresponding disk. -/
theorem selectedIndicesInClosedBall_subset {Candidate : Type v}
    {location : PlaneCell → Candidate → EuclideanPlane}
    {x : JitteredSelection Candidate} {center : EuclideanPlane} {radius : ℝ}
    {support : Finset PlaneCell}
    (hcover : CoversClosedBall location center radius support) :
    selectedIndicesInClosedBall location x center radius ⊆ ↑support := by
  intro cell hcell
  exact hcover cell (x cell) hcell

/-- Consequently, every disk count controlled by a finite support really is finite. -/
theorem selectedIndicesInClosedBall_finite {Candidate : Type v}
    {location : PlaneCell → Candidate → EuclideanPlane}
    {x : JitteredSelection Candidate} {center : EuclideanPlane} {radius : ℝ}
    {support : Finset PlaneCell}
    (hcover : CoversClosedBall location center radius support) :
    (selectedIndicesInClosedBall location x center radius).Finite :=
  support.finite_toSet.subset (selectedIndicesInClosedBall_subset hcover)

/-- Under the covering hypothesis, the local finite count is exactly the global selected-index
count. -/
theorem selectedDiskCount_eq_localDiskCount {Candidate : Type v}
    {location : PlaneCell → Candidate → EuclideanPlane}
    {x : JitteredSelection Candidate} {center : EuclideanPlane} {radius : ℝ}
    {support : Finset PlaneCell}
    (hcover : CoversClosedBall location center radius support) :
    selectedDiskCount location x center radius =
      localDiskCount support location center radius (fun i ↦ x i) := by
  classical
  let indices := selectedIndicesInClosedBall location x center radius
  let localFinset : Finset support := Finset.univ.filter fun i : support ↦
    location i.1 (x i) ∈ Metric.closedBall center radius
  have himage : ((fun i : support ↦ i.1) '' (↑localFinset : Set support)) = indices := by
    ext cell
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact (Finset.mem_filter.mp hi).2
    · intro hcell
      have hs : cell ∈ support := hcover cell (x cell) hcell
      refine ⟨⟨cell, hs⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcell⟩
  rw [selectedDiskCount]
  change indices.ncard = _
  rw [← himage]
  rw [Set.ncard_image_of_injective _ Subtype.val_injective]
  rw [Set.ncard_coe_finset]
  rfl

/-- Satisfaction of the local radius-sensitive constraint is equivalent to the actual selected
disk-error bound whenever its support covers the disk. -/
theorem radiusSensitiveDiskConstraint_satisfied_iff {Candidate : Type v}
    {location : PlaneCell → Candidate → EuclideanPlane}
    {x : JitteredSelection Candidate} {center : EuclideanPlane} {radius allowance : ℝ}
    {support : Finset PlaneCell}
    (hcover : CoversClosedBall location center radius support) :
    (radiusSensitiveDiskConstraint location center radius allowance support).Satisfied x ↔
      selectedDiskError location x center radius ≤ allowance := by
  rw [LocalConstraint.Satisfied, radiusSensitiveDiskConstraint, selectedDiskError,
    selectedDiskCount_eq_localDiskCount hcover]

/-- The finite-family-to-global theorem for radius-sensitive Euclidean disk constraints.

The hypothesis `hfinite` is the exact output required from a finite construction:
for every finite collection of disks, one assignment obeys all of their local finite-count
bounds.  No independence or probability claim is hidden in this compactness theorem. -/
theorem exists_selection_with_all_disk_bounds_of_local_finite_satisfiability
    {Candidate : Type v} {Constraint : Type w}
    [TopologicalSpace Candidate] [DiscreteTopology Candidate] [Finite Candidate]
    (location : PlaneCell → Candidate → EuclideanPlane)
    (center : Constraint → EuclideanPlane) (radius allowance : Constraint → ℝ)
    (support : Constraint → Finset PlaneCell)
    (hcover : ∀ k, CoversClosedBall location (center k) (radius k) (support k))
    (hfinite : ∀ s : Finset Constraint, ∃ x : JitteredSelection Candidate,
      ∀ k ∈ s,
        |(localDiskCount (support k) location (center k) (radius k)
            (fun i ↦ x i) : ℝ) - Real.pi * (radius k) ^ 2| ≤ allowance k) :
    ∃ x : JitteredSelection Candidate, ∀ k,
      selectedDiskError location x (center k) (radius k) ≤ allowance k := by
  let c : Constraint → LocalConstraint PlaneCell Candidate := fun k ↦
    radiusSensitiveDiskConstraint location (center k) (radius k) (allowance k) (support k)
  have hcfinite : ∀ s : Finset Constraint, ∃ x : JitteredSelection Candidate,
      ∀ k ∈ s, (c k).Satisfied x := by
    intro s
    obtain ⟨x, hx⟩ := hfinite s
    refine ⟨x, ?_⟩
    intro k hk
    exact hx k hk
  obtain ⟨x, hx⟩ :=
    exists_jitteredSelection_of_finitely_satisfiable c hcfinite
  refine ⟨x, fun k ↦ ?_⟩
  exact (radiusSensitiveDiskConstraint_satisfied_iff (hcover k)).mp (hx k)

/-- Equivalent convenient version whose finite hypothesis is already phrased using the actual
selected disk errors. -/
theorem exists_selection_with_all_disk_bounds_of_finite_satisfiability
    {Candidate : Type v} {Constraint : Type w}
    [TopologicalSpace Candidate] [DiscreteTopology Candidate] [Finite Candidate]
    (location : PlaneCell → Candidate → EuclideanPlane)
    (center : Constraint → EuclideanPlane) (radius allowance : Constraint → ℝ)
    (support : Constraint → Finset PlaneCell)
    (hcover : ∀ k, CoversClosedBall location (center k) (radius k) (support k))
    (hfinite : ∀ s : Finset Constraint, ∃ x : JitteredSelection Candidate,
      ∀ k ∈ s, selectedDiskError location x (center k) (radius k) ≤ allowance k) :
    ∃ x : JitteredSelection Candidate, ∀ k,
      selectedDiskError location x (center k) (radius k) ≤ allowance k := by
  apply exists_selection_with_all_disk_bounds_of_local_finite_satisfiability
    location center radius allowance support hcover
  intro s
  obtain ⟨x, hx⟩ := hfinite s
  refine ⟨x, ?_⟩
  intro k hk
  simpa [selectedDiskError, selectedDiskCount_eq_localDiskCount (hcover k)] using hx k hk

/-- The range of a selection, intersected with a disk, is the image of the corresponding set
of selected indices. -/
theorem range_inter_closedBall_eq_image_selectedIndices {Candidate : Type v}
    (location : PlaneCell → Candidate → EuclideanPlane)
    (x : JitteredSelection Candidate) (center : EuclideanPlane) (radius : ℝ) :
    Set.range (selectedPoint location x) ∩ Metric.closedBall center radius =
      selectedPoint location x '' selectedIndicesInClosedBall location x center radius := by
  ext p
  constructor
  · rintro ⟨⟨cell, rfl⟩, hball⟩
    exact ⟨cell, hball, rfl⟩
  · rintro ⟨cell, hball, rfl⟩
    exact ⟨⟨cell, rfl⟩, hball⟩

/-- If candidate locations belonging to distinct cells never coincide, every assignment gives
an injective point selection. -/
theorem selectedPoint_injective_of_cell_separated {Candidate : Type v}
    {location : PlaneCell → Candidate → EuclideanPlane}
    (hseparate : ∀ ⦃cell cell' : PlaneCell⦄ ⦃q q' : Candidate⦄,
      location cell q = location cell' q' → cell = cell')
    (x : JitteredSelection Candidate) : Function.Injective (selectedPoint location x) := by
  intro cell cell' h
  exact hseparate h

/-- For an injective selection, index discrepancy is exactly the discrepancy of the actual
point set in every disk. -/
theorem range_disk_error_eq_selectedDiskError {Candidate : Type v}
    {location : PlaneCell → Candidate → EuclideanPlane}
    {x : JitteredSelection Candidate} (hinj : Function.Injective (selectedPoint location x))
    (center : EuclideanPlane) (radius : ℝ) :
    |(((Set.range (selectedPoint location x) ∩
        Metric.closedBall center radius).ncard : ℕ) : ℝ) -
        Real.pi * radius ^ 2| = selectedDiskError location x center radius := by
  rw [range_inter_closedBall_eq_image_selectedIndices]
  rw [Set.ncard_image_of_injective _ hinj]
  rfl

/-- Actual global point-set form of the compactness bridge.  From finite satisfiability of the
radius-sensitive local constraints it produces one injective selection whose range obeys every
specified Euclidean disk bound. -/
theorem exists_injective_point_selection_with_all_disk_bounds
    {Candidate : Type v} {Constraint : Type w}
    [TopologicalSpace Candidate] [DiscreteTopology Candidate] [Finite Candidate]
    (location : PlaneCell → Candidate → EuclideanPlane)
    (hseparate : ∀ ⦃cell cell' : PlaneCell⦄ ⦃q q' : Candidate⦄,
      location cell q = location cell' q' → cell = cell')
    (center : Constraint → EuclideanPlane) (radius allowance : Constraint → ℝ)
    (support : Constraint → Finset PlaneCell)
    (hcover : ∀ k, CoversClosedBall location (center k) (radius k) (support k))
    (hfinite : ∀ s : Finset Constraint, ∃ x : JitteredSelection Candidate,
      ∀ k ∈ s,
        |(localDiskCount (support k) location (center k) (radius k)
            (fun i ↦ x i) : ℝ) - Real.pi * (radius k) ^ 2| ≤ allowance k) :
    ∃ x : JitteredSelection Candidate,
      Function.Injective (selectedPoint location x) ∧
      ∀ k,
        |(((Set.range (selectedPoint location x) ∩
              Metric.closedBall (center k) (radius k)).ncard : ℕ) : ℝ) -
            Real.pi * (radius k) ^ 2| ≤ allowance k := by
  obtain ⟨x, hx⟩ :=
    exists_selection_with_all_disk_bounds_of_local_finite_satisfiability
      location center radius allowance support hcover hfinite
  have hinj := selectedPoint_injective_of_cell_separated hseparate x
  refine ⟨x, hinj, fun k ↦ ?_⟩
  rw [range_disk_error_eq_selectedDiskError hinj]
  exact hx k

/-! ## Canonical supports from a locally finite candidate table -/

/-- A table of candidate locations is locally finite if only finitely many cells have any
candidate in a given closed disk.  For a genuine jittered lattice this follows from the fact
that all candidates of a cell lie in its bounded unit square. -/
def CandidateTableLocallyFinite {Candidate : Type v}
    (location : PlaneCell → Candidate → EuclideanPlane) : Prop :=
  ∀ center radius,
    {cell | ∃ q, location cell q ∈ Metric.closedBall center radius}.Finite

/-- The canonical finite support consisting of all cells which have some candidate in a disk. -/
noncomputable def closedBallSupport {Candidate : Type v}
    (location : PlaneCell → Candidate → EuclideanPlane)
    (hloc : CandidateTableLocallyFinite location)
    (center : EuclideanPlane) (radius : ℝ) : Finset PlaneCell :=
  (hloc center radius).toFinset

/-- The canonical support covers every candidate location in its disk. -/
theorem closedBallSupport_covers {Candidate : Type v}
    (location : PlaneCell → Candidate → EuclideanPlane)
    (hloc : CandidateTableLocallyFinite location)
    (center : EuclideanPlane) (radius : ℝ) :
    CoversClosedBall location center radius
      (closedBallSupport location hloc center radius) := by
  intro cell q hq
  simp only [closedBallSupport, Set.Finite.mem_toFinset]
  exact ⟨q, hq⟩

/-- Any assignment drawn from a locally finite candidate table is locally finite on compact
sets. -/
theorem selectedPoint_compact_preimage_finite {Candidate : Type v}
    {location : PlaneCell → Candidate → EuclideanPlane}
    (hloc : CandidateTableLocallyFinite location)
    (x : JitteredSelection Candidate) (K : Set EuclideanPlane) (hK : IsCompact K) :
    {cell | selectedPoint location x cell ∈ K}.Finite := by
  obtain ⟨radius, hsubset⟩ := hK.isBounded.subset_closedBall (0 : EuclideanPlane)
  apply (hloc 0 radius).subset
  intro cell hcell
  exact ⟨x cell, hsubset hcell⟩

/-! ### The literal unit-cell jittered table -/

/-- Candidate locations obtained by translating offsets by the integer lattice cell. -/
def latticeLocation {Candidate : Type v} (offset : Candidate → ℝ × ℝ)
    (cell : PlaneCell) (q : Candidate) : EuclideanPlane :=
  pairToEuclideanPlane
    ((cell.1 : ℝ) + (offset q).1, (cell.2 : ℝ) + (offset q).2)

@[simp] theorem latticeLocation_apply_zero {Candidate : Type v}
    (offset : Candidate → ℝ × ℝ) (cell : PlaneCell) (q : Candidate) :
    latticeLocation offset cell q 0 = (cell.1 : ℝ) + (offset q).1 := by
  rfl

@[simp] theorem latticeLocation_apply_one {Candidate : Type v}
    (offset : Candidate → ℝ × ℝ) (cell : PlaneCell) (q : Candidate) :
    latticeLocation offset cell q 1 = (cell.2 : ℝ) + (offset q).2 := by
  rfl

/-- Coordinate form of the condition that all offsets belong to the half-open unit square. -/
def OffsetsInHalfOpenUnitSquare {Candidate : Type v} (offset : Candidate → ℝ × ℝ) :
    Prop :=
  ∀ q, 0 ≤ (offset q).1 ∧ (offset q).1 < 1 ∧
    0 ≤ (offset q).2 ∧ (offset q).2 < 1

/-- Translating half-open unit-square offsets by distinct lattice cells cannot produce the same
point. -/
theorem latticeLocation_cell_separated {Candidate : Type v}
    {offset : Candidate → ℝ × ℝ} (hoffset : OffsetsInHalfOpenUnitSquare offset) :
    ∀ ⦃cell cell' : PlaneCell⦄ ⦃q q' : Candidate⦄,
      latticeLocation offset cell q = latticeLocation offset cell' q' → cell = cell' := by
  intro cell cell' q q' hpoint
  have hx := congrArg (fun p : EuclideanPlane ↦ p 0) hpoint
  have hy := congrArg (fun p : EuclideanPlane ↦ p 1) hpoint
  simp only [latticeLocation_apply_zero] at hx
  simp only [latticeLocation_apply_one] at hy
  rcases hoffset q with ⟨hqx0, hqx1, hqy0, hqy1⟩
  rcases hoffset q' with ⟨hq'x0, hq'x1, hq'y0, hq'y1⟩
  apply Prod.ext
  · apply le_antisymm
    · by_contra hnot
      have hint : cell'.1 + 1 ≤ cell.1 := by omega
      have hcast : (cell'.1 : ℝ) + 1 ≤ (cell.1 : ℝ) := by exact_mod_cast hint
      linarith
    · by_contra hnot
      have hint : cell.1 + 1 ≤ cell'.1 := by omega
      have hcast : (cell.1 : ℝ) + 1 ≤ (cell'.1 : ℝ) := by exact_mod_cast hint
      linarith
  · apply le_antisymm
    · by_contra hnot
      have hint : cell'.2 + 1 ≤ cell.2 := by omega
      have hcast : (cell'.2 : ℝ) + 1 ≤ (cell.2 : ℝ) := by exact_mod_cast hint
      linarith
    · by_contra hnot
      have hint : cell.2 + 1 ≤ cell'.2 := by omega
      have hcast : (cell.2 : ℝ) + 1 ≤ (cell'.2 : ℝ) := by exact_mod_cast hint
      linarith

/-- Candidate locations with offsets in the closed unit square form a locally finite table.
The proof exhibits an integer bounding box for every Euclidean disk. -/
theorem latticeLocation_candidateTableLocallyFinite {Candidate : Type v}
    {offset : Candidate → ℝ × ℝ}
    (hoffset : ∀ q, 0 ≤ (offset q).1 ∧ (offset q).1 ≤ 1 ∧
      0 ≤ (offset q).2 ∧ (offset q).2 ≤ 1) :
    CandidateTableLocallyFinite (latticeLocation offset) := by
  intro center radius
  let xlo : ℤ := ⌈center 0 - radius - 1⌉
  let xhi : ℤ := ⌊center 0 + radius⌋
  let ylo : ℤ := ⌈center 1 - radius - 1⌉
  let yhi : ℤ := ⌊center 1 + radius⌋
  let box : Finset PlaneCell := Finset.Icc xlo xhi ×ˢ Finset.Icc ylo yhi
  apply box.finite_toSet.subset
  rintro cell ⟨q, hball⟩
  have hdist : dist (latticeLocation offset cell q) center ≤ radius :=
    Metric.mem_closedBall.mp hball
  have hdx : dist (latticeLocation offset cell q 0) (center 0) ≤ radius :=
    (PiLp.dist_apply_le (latticeLocation offset cell q) center 0).trans hdist
  have hdy : dist (latticeLocation offset cell q 1) (center 1) ≤ radius :=
    (PiLp.dist_apply_le (latticeLocation offset cell q) center 1).trans hdist
  rw [Real.dist_eq] at hdx hdy
  have hdx' := abs_le.mp hdx
  have hdy' := abs_le.mp hdy
  rcases hoffset q with ⟨hqx0, hqx1, hqy0, hqy1⟩
  have hxloReal : center 0 - radius - 1 ≤ (cell.1 : ℝ) := by
    simp only [latticeLocation_apply_zero] at hdx'
    linarith
  have hxhiReal : (cell.1 : ℝ) ≤ center 0 + radius := by
    simp only [latticeLocation_apply_zero] at hdx'
    linarith
  have hyloReal : center 1 - radius - 1 ≤ (cell.2 : ℝ) := by
    simp only [latticeLocation_apply_one] at hdy'
    linarith
  have hyhiReal : (cell.2 : ℝ) ≤ center 1 + radius := by
    simp only [latticeLocation_apply_one] at hdy'
    linarith
  change cell ∈ box
  rw [Finset.mem_product]
  constructor
  · rw [Finset.mem_Icc]
    exact ⟨Int.ceil_le.mpr hxloReal, Int.le_floor.mpr hxhiReal⟩
  · rw [Finset.mem_Icc]
    exact ⟨Int.ceil_le.mpr hyloReal, Int.le_floor.mpr hyhiReal⟩

/-- Fully geometric compactness output with canonical radius-sensitive supports.  Besides the
actual disk bounds, the returned point parametrization is injective and locally finite on every
compact set.  Thus its range is an admissible planar point set whenever the cell type is
infinite (as `PlaneCell` is).

The sole quantitative input remains `hfinite`, the finite-family estimate to be proved
separately. -/
theorem exists_locally_finite_injective_selection_with_all_disk_bounds
    {Candidate : Type v} {Constraint : Type w}
    [TopologicalSpace Candidate] [DiscreteTopology Candidate] [Finite Candidate]
    (location : PlaneCell → Candidate → EuclideanPlane)
    (hloc : CandidateTableLocallyFinite location)
    (hseparate : ∀ ⦃cell cell' : PlaneCell⦄ ⦃q q' : Candidate⦄,
      location cell q = location cell' q' → cell = cell')
    (center : Constraint → EuclideanPlane) (radius allowance : Constraint → ℝ)
    (hfinite : ∀ s : Finset Constraint, ∃ x : JitteredSelection Candidate,
      ∀ k ∈ s,
        |(localDiskCount
              (closedBallSupport location hloc (center k) (radius k))
              location (center k) (radius k) (fun i ↦ x i) : ℝ) -
            Real.pi * (radius k) ^ 2| ≤ allowance k) :
    ∃ x : JitteredSelection Candidate,
      Function.Injective (selectedPoint location x) ∧
      (∀ K : Set EuclideanPlane, IsCompact K →
        {cell | selectedPoint location x cell ∈ K}.Finite) ∧
      ∀ k,
        |(((Set.range (selectedPoint location x) ∩
              Metric.closedBall (center k) (radius k)).ncard : ℕ) : ℝ) -
            Real.pi * (radius k) ^ 2| ≤ allowance k := by
  let support : Constraint → Finset PlaneCell := fun k ↦
    closedBallSupport location hloc (center k) (radius k)
  have hcover : ∀ k, CoversClosedBall location (center k) (radius k) (support k) := by
    intro k
    exact closedBallSupport_covers location hloc (center k) (radius k)
  obtain ⟨x, hinj, hbound⟩ :=
    exists_injective_point_selection_with_all_disk_bounds
      location hseparate center radius allowance support hcover hfinite
  exact ⟨x, hinj, selectedPoint_compact_preimage_finite hloc x, hbound⟩

/-- Literal jittered-lattice specialization of the global disk theorem.  One candidate is
selected from each integer translate of the half-open unit square.  Cell separation and local
finiteness are discharged here, leaving only the finite-family discrepancy estimate as input. -/
theorem exists_unit_jittered_selection_with_all_disk_bounds
    {Candidate : Type v} {Constraint : Type w}
    [TopologicalSpace Candidate] [DiscreteTopology Candidate] [Finite Candidate]
    (offset : Candidate → ℝ × ℝ)
    (hoffset : OffsetsInHalfOpenUnitSquare offset)
    (center : Constraint → EuclideanPlane) (radius allowance : Constraint → ℝ)
    (hfinite : ∀ s : Finset Constraint, ∃ x : JitteredSelection Candidate,
      ∀ k ∈ s,
        |(localDiskCount
              (closedBallSupport (latticeLocation offset)
                (latticeLocation_candidateTableLocallyFinite fun q ↦
                  ⟨(hoffset q).1, (hoffset q).2.1.le,
                    (hoffset q).2.2.1, (hoffset q).2.2.2.le⟩)
                (center k) (radius k))
              (latticeLocation offset) (center k) (radius k) (fun i ↦ x i) : ℝ) -
            Real.pi * (radius k) ^ 2| ≤ allowance k) :
    ∃ x : JitteredSelection Candidate,
      Function.Injective (selectedPoint (latticeLocation offset) x) ∧
      (∀ K : Set EuclideanPlane, IsCompact K →
        {cell | selectedPoint (latticeLocation offset) x cell ∈ K}.Finite) ∧
      ∀ k,
        |(((Set.range (selectedPoint (latticeLocation offset) x) ∩
              Metric.closedBall (center k) (radius k)).ncard : ℕ) : ℝ) -
            Real.pi * (radius k) ^ 2| ≤ allowance k := by
  let hloc : CandidateTableLocallyFinite (latticeLocation offset) :=
    latticeLocation_candidateTableLocallyFinite fun q ↦
      ⟨(hoffset q).1, (hoffset q).2.1.le,
        (hoffset q).2.2.1, (hoffset q).2.2.2.le⟩
  exact exists_locally_finite_injective_selection_with_all_disk_bounds
    (latticeLocation offset) hloc (latticeLocation_cell_separated hoffset)
      center radius allowance hfinite

end GlobalSelection
end Erdos989
