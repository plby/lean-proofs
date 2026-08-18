/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.IndexedGraphDensity
import ErdosProblems.Erdos186.PZ.ConvexDensity.RelativeDyadicCells

/-! # A disjoint assignment to the closed unit graph grid -/

open Set
open scoped BigOperators

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

open Subgradient
open Erdos186.ConvexApprox

/-- The clamped floor assignment of a point of `[0,1]` to one of `m`
intervals.  Clamping sends the endpoint `1` to the final interval. -/
def unitIntervalIndex (m : ℕ) (hm : 0 < m) (x : ℝ) : Fin m :=
  ⟨min ⌊(m : ℝ) * x⌋₊ (m - 1), by
    exact lt_of_le_of_lt (min_le_right _ _)
      (Nat.sub_lt hm (by omega))⟩

/-- The assigned closed interval really contains the original unit-interval
point. -/
theorem unitIntervalIndex_bounds {m : ℕ} (hm : 0 < m)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ((unitIntervalIndex m hm x : Fin m) : ℕ) / (m : ℝ) ≤ x ∧
      x ≤ (((unitIntervalIndex m hm x : Fin m) : ℕ) + 1) / (m : ℝ) := by
  let k : ℕ := ⌊(m : ℝ) * x⌋₊
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmx0 : 0 ≤ (m : ℝ) * x := mul_nonneg (by positivity) hx.1
  have hkLower : (k : ℝ) ≤ (m : ℝ) * x := Nat.floor_le hmx0
  have hkUpper : (m : ℝ) * x < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  by_cases hk : k ≤ m - 1
  · have hmin : min k (m - 1) = k := min_eq_left hk
    change (min k (m - 1) : ℕ) / (m : ℝ) ≤ x ∧
      x ≤ ((min k (m - 1) : ℕ) + 1) / (m : ℝ)
    rw [hmin]
    constructor
    · exact (div_le_iff₀ hmR).2 (by simpa [mul_comm] using hkLower)
    · exact (le_div_iff₀ hmR).2 (by simpa [mul_comm] using hkUpper.le)
  · have hmk : m ≤ k := by omega
    have hxOne : x = 1 := by
      have hmle : (m : ℝ) ≤ (m : ℝ) * x :=
        (by exact_mod_cast hmk : (m : ℝ) ≤ k).trans hkLower
      exact le_antisymm hx.2 (by nlinarith [hmle])
    have hmin : min k (m - 1) = m - 1 := min_eq_right (by omega)
    change (min k (m - 1) : ℕ) / (m : ℝ) ≤ x ∧
      x ≤ ((min k (m - 1) : ℕ) + 1) / (m : ℝ)
    rw [hmin, hxOne]
    have hsub : (m - 1 : ℕ) + 1 = m := Nat.sub_add_cancel (by omega)
    have hsubR : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hsub
    rw [hsubR]
    constructor
    · exact (div_le_one hmR).2 (by exact_mod_cast (Nat.sub_le m 1))
    · rw [div_self (ne_of_gt hmR)]

/-- Coordinatewise unit-cube assignment. -/
def unitGraphGridIndex {n : ℕ} (m : ℕ) (hm : 0 < m)
    (z : EuclideanPoint (n + 1)) : Fin n → Fin m :=
  fun i ↦ unitIntervalIndex m hm (coordinate (baseCoordinates z) i)

/-- A point whose base is in the unit cube belongs to the closed graph cell
specified by its disjoint clamped-floor assignment. -/
theorem mem_graphBaseCellND_unitGraphGridIndex {n m : ℕ} (hm : 0 < m)
    {z : EuclideanPoint (n + 1)}
    (hz : ∀ i, coordinate (baseCoordinates z) i ∈ Set.Icc (0 : ℝ) 1) :
    baseCoordinates z ∈ graphBaseCellND (unitGraphGridIndex m hm z) := by
  rw [mem_graphBaseCellND_iff]
  change
    (∀ i, pzFinGridPoint (unitGraphGridIndex m hm z) i ≤
      coordinate (baseCoordinates z) i) ∧
    (∀ i, coordinate (baseCoordinates z) i ≤
      pzFinGridPoint (unitGraphGridIndex m hm z) i + 1 / (m : ℝ))
  constructor <;> intro i
  · simpa [pzFinGridPoint, pzGridPoint, unitGraphGridIndex] using
      (unitIntervalIndex_bounds hm (hz i)).1
  · have hi := (unitIntervalIndex_bounds hm (hz i)).2
    rw [add_div, one_div] at hi
    simpa [pzFinGridPoint, pzGridPoint, unitGraphGridIndex] using hi

/-- Labels assigned to one unit graph cell. -/
def unitAssignedLabels {ι : Type*} [DecidableEq ι] {n m : ℕ}
    (hm : 0 < m) (J : Finset ι)
    (z : ι → EuclideanPoint (n + 1)) (v : Fin n → Fin m) : Finset ι :=
  J.filter fun i ↦ unitGraphGridIndex m hm (z i) = v

@[simp]
theorem mem_unitAssignedLabels_iff {ι : Type*} [DecidableEq ι]
    {n m : ℕ} {hm : 0 < m} {J : Finset ι}
    {z : ι → EuclideanPoint (n + 1)} {v : Fin n → Fin m} {i : ι} :
    i ∈ unitAssignedLabels hm J z v ↔
      i ∈ J ∧ unitGraphGridIndex m hm (z i) = v := by
  simp [unitAssignedLabels]

theorem card_unitAssignedLabels {ι : Type*} [DecidableEq ι]
    {n m : ℕ} (hm : 0 < m) (J : Finset ι)
    (z : ι → EuclideanPoint (n + 1)) (v : Fin n → Fin m) :
    (unitAssignedLabels hm J z v).card =
      DyadicCells.occupancy J (fun i ↦ unitGraphGridIndex m hm (z i)) v := by
  rfl

theorem pairwiseDisjoint_unitAssignedLabels {ι : Type*} [DecidableEq ι]
    {n m : ℕ} (hm : 0 < m) (J : Finset ι)
    (z : ι → EuclideanPoint (n + 1))
    (I : Finset (Fin n → Fin m)) :
    (I : Set (Fin n → Fin m)).PairwiseDisjoint
      (unitAssignedLabels hm J z) := by
  intro v _hv w _hw hvw
  change Disjoint (unitAssignedLabels hm J z v) (unitAssignedLabels hm J z w)
  rw [Finset.disjoint_left]
  intro i hiv hiw
  exact hvw ((mem_unitAssignedLabels_iff.mp hiv).2.symm.trans
    (mem_unitAssignedLabels_iff.mp hiw).2)

/-- Exact mass partition over all `m^n` unit-grid cells. -/
theorem sum_card_unitAssignedLabels {ι : Type*} [DecidableEq ι]
    {n m : ℕ} (hm : 0 < m) (J : Finset ι)
    (z : ι → EuclideanPoint (n + 1)) :
    (∑ v : Fin n → Fin m, (unitAssignedLabels hm J z v).card) = J.card := by
  simpa [card_unitAssignedLabels] using
    DyadicCells.sum_occupancy_eq_card J
      (Finset.univ : Finset (Fin n → Fin m))
      (fun i ↦ unitGraphGridIndex m hm (z i))
      (by simp)

/-- The disjoint assignment fibre is contained in the closed-cell filter
used by the indexed graph-density theorem. -/
theorem unitAssignedLabels_subset_indexedLabelsOverCellND
    {ι : Type*} [DecidableEq ι] {n m : ℕ} (hm : 0 < m)
    {J : Finset ι} {z : ι → EuclideanPoint (n + 1)}
    (hunit : ∀ i ∈ J, ∀ k,
      coordinate (baseCoordinates (z i)) k ∈ Set.Icc (0 : ℝ) 1)
    (v : Fin n → Fin m) :
    unitAssignedLabels hm J z v ⊆ indexedLabelsOverCellND J z v := by
  intro i hi
  have hi' := mem_unitAssignedLabels_iff.mp hi
  rw [mem_indexedLabelsOverCellND_iff]
  refine ⟨hi'.1, ?_⟩
  rw [← hi'.2]
  exact mem_graphBaseCellND_unitGraphGridIndex hm (hunit i hi'.1)

/-- Consequently every assigned-cell occupancy lower bound is also a lower
bound for the possibly boundary-overlapping filter consumed by
`IndexedGraphDensity`. -/
theorem card_unitAssignedLabels_le_indexedLabelsOverCellND
    {ι : Type*} [DecidableEq ι] {n m : ℕ} (hm : 0 < m)
    {J : Finset ι} {z : ι → EuclideanPoint (n + 1)}
    (hunit : ∀ i ∈ J, ∀ k,
      coordinate (baseCoordinates (z i)) k ∈ Set.Icc (0 : ℝ) 1)
    (v : Fin n → Fin m) :
    (unitAssignedLabels hm J z v).card ≤
      (indexedLabelsOverCellND J z v).card :=
  Finset.card_le_card
    (unitAssignedLabels_subset_indexedLabelsOverCellND hm hunit v)

/-- Relative dyadic regularization of the disjoint unit-grid assignment.

The cutoff removes at most half the labels.  The surviving labels therefore
have a single relative dyadic occupancy scale, and every selected assignment
fibre is contained in the (closed-cell) label filter used by the indexed graph
density theorem.  Keeping the assignment fibres rather than deduplicating the
geometric points is what preserves label multiplicity. -/
theorem exists_unitGraphGrid_relative_occupancy_shell
    {ι : Type*} [DecidableEq ι] {n m : ℕ} (hm : 0 < m)
    (J : Finset ι) (z : ι → EuclideanPoint (n + 1))
    (hunit : ∀ i ∈ J, ∀ k,
      coordinate (baseCoordinates (z i)) k ∈ Set.Icc (0 : ℝ) 1)
    (cutoff L : ℕ) (hJ : 2 ≤ J.card) (hcutoff : 0 < cutoff)
    (hupper : J.card < cutoff * 2 ^ (L + 1))
    (hdiscard : Fintype.card (Fin n → Fin m) * cutoff ≤ J.card / 2) :
    ∃ j < L + 1,
      let I := RelativeDyadicCells.relativeShell
        (Finset.univ : Finset (Fin n → Fin m))
        (fun v ↦ (unitAssignedLabels hm J z v).card) cutoff j
      I.Nonempty ∧
      J.card / 2 ≤ (L + 1) *
        RelativeDyadicCells.shellWeight
          (Finset.univ : Finset (Fin n → Fin m))
          (fun v ↦ (unitAssignedLabels hm J z v).card) cutoff j ∧
      (∀ v ∈ I,
        cutoff * 2 ^ j ≤ (unitAssignedLabels hm J z v).card ∧
          (unitAssignedLabels hm J z v).card < cutoff * 2 ^ (j + 1)) ∧
      ∀ v ∈ I,
        cutoff * 2 ^ j ≤ (indexedLabelsOverCellND J z v).card := by
  let cell : ι → (Fin n → Fin m) := fun i ↦ unitGraphGridIndex m hm (z i)
  have hmaps : ∀ i ∈ J,
      cell i ∈ (Finset.univ : Finset (Fin n → Fin m)) := by simp
  obtain ⟨j, hj, hglobal, _hretained, _hdivNat, _hdivReal,
      hpointwise, _hlower, _hupperMass, _hcard⟩ :=
    RelativeDyadicCells.exists_relative_occupancy_shell_after_discard
      J (Finset.univ : Finset (Fin n → Fin m)) cell cutoff L
      hmaps hcutoff hupper
  have hhalf : J.card / 2 ≤ (L + 1) *
      RelativeDyadicCells.shellWeight
        (Finset.univ : Finset (Fin n → Fin m))
        (DyadicCells.occupancy J cell) cutoff j := by
    have hcells : (Finset.univ : Finset (Fin n → Fin m)).card =
        Fintype.card (Fin n → Fin m) := Finset.card_univ
    rw [hcells] at hglobal
    omega
  have hshellNonempty :
      (RelativeDyadicCells.relativeShell
        (Finset.univ : Finset (Fin n → Fin m))
        (DyadicCells.occupancy J cell) cutoff j).Nonempty := by
    by_contra hempty
    have heq : RelativeDyadicCells.relativeShell
        (Finset.univ : Finset (Fin n → Fin m))
        (DyadicCells.occupancy J cell) cutoff j = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hhalfPos : 0 < J.card / 2 := Nat.div_pos (by omega) (by omega)
    rw [RelativeDyadicCells.shellWeight, heq] at hhalf
    simp at hhalf
    omega
  refine ⟨j, hj, ?_, ?_, ?_, ?_⟩
  · simpa [cell, card_unitAssignedLabels] using hshellNonempty
  · simpa [cell, card_unitAssignedLabels] using hhalf
  · intro v hv
    have hv' : v ∈ RelativeDyadicCells.relativeShell
        (Finset.univ : Finset (Fin n → Fin m))
        (DyadicCells.occupancy J cell) cutoff j := by
      simpa [cell, card_unitAssignedLabels] using hv
    simpa [cell, card_unitAssignedLabels] using hpointwise v hv'
  · intro v hv
    exact (hpointwise v (by
      simpa [cell, card_unitAssignedLabels] using hv)).1.trans
        (card_unitAssignedLabels_le_indexedLabelsOverCellND hm hunit v)

/-- The source-faithful second-grid regularization.  Empty graph cells cost
nothing: with cutoff one, every discarded assignment fibre has cardinality
zero. -/
theorem exists_unitGraphGrid_occupied_shell
    {ι : Type*} [DecidableEq ι] {n m : ℕ} (hm : 0 < m)
    (J : Finset ι) (z : ι → EuclideanPoint (n + 1))
    (hunit : ∀ i ∈ J, ∀ k,
      coordinate (baseCoordinates (z i)) k ∈ Set.Icc (0 : ℝ) 1)
    (L : ℕ) (hJ : J.Nonempty) (hupper : J.card < 2 ^ (L + 1)) :
    ∃ j < L + 1,
      let I := RelativeDyadicCells.relativeShell
        (Finset.univ : Finset (Fin n → Fin m))
        (fun v ↦ (unitAssignedLabels hm J z v).card) 1 j
      I.Nonempty ∧
      J.card ≤ (L + 1) *
        RelativeDyadicCells.shellWeight
          (Finset.univ : Finset (Fin n → Fin m))
          (fun v ↦ (unitAssignedLabels hm J z v).card) 1 j ∧
      (∀ v ∈ I,
        2 ^ j ≤ (unitAssignedLabels hm J z v).card ∧
          (unitAssignedLabels hm J z v).card < 2 ^ (j + 1)) ∧
      ∀ v ∈ I,
        2 ^ j ≤ (indexedLabelsOverCellND J z v).card := by
  let weight : (Fin n → Fin m) → ℕ :=
    fun v ↦ (unitAssignedLabels hm J z v).card
  have hmass : RelativeDyadicCells.retainedWeight
      (Finset.univ : Finset (Fin n → Fin m)) weight 1 = J.card := by
    rw [RelativeDyadicCells.retainedWeight_one_eq_sum]
    simpa [weight] using sum_card_unitAssignedLabels hm J z
  have hweight : ∀ v, weight v ≤ J.card := by
    intro v
    exact Finset.card_le_card (Finset.filter_subset _ _)
  obtain ⟨j, hj, hjmass, _hdivNat, _hdivReal, hpointwise,
      _hlower, _hupperMass, _hcard⟩ :=
    RelativeDyadicCells.exists_relativeShell_weight
      (Finset.univ : Finset (Fin n → Fin m)) weight 1 L (by omega)
      (by
        intro v _hv
        simpa using (hweight v).trans_lt hupper)
  have hshellNonempty :
      (RelativeDyadicCells.relativeShell
        (Finset.univ : Finset (Fin n → Fin m)) weight 1 j).Nonempty := by
    by_contra hempty
    have heq : RelativeDyadicCells.relativeShell
        (Finset.univ : Finset (Fin n → Fin m)) weight 1 j = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hjzero : J.card ≤ 0 := by
      rw [← hmass]
      simpa [RelativeDyadicCells.shellWeight, heq] using hjmass
    have hJpos : 0 < J.card := hJ.card_pos
    omega
  refine ⟨j, hj, ?_, ?_, ?_, ?_⟩
  · simpa [weight] using hshellNonempty
  · simpa [hmass, weight] using hjmass
  · intro v hv
    have hv' : v ∈ RelativeDyadicCells.relativeShell
        (Finset.univ : Finset (Fin n → Fin m)) weight 1 j := by
      simpa [weight] using hv
    simpa [weight] using hpointwise v hv'
  · intro v hv
    have hv' : v ∈ RelativeDyadicCells.relativeShell
        (Finset.univ : Finset (Fin n → Fin m)) weight 1 j := by
      simpa [weight] using hv
    have hlower : 2 ^ j ≤ (unitAssignedLabels hm J z v).card := by
      simpa [weight] using (hpointwise v hv').1
    exact hlower.trans
      (card_unitAssignedLabels_le_indexedLabelsOverCellND hm hunit v)

/-! ## Planar specialization with natural-number cell labels -/

/-- The one-dimensional unit-grid label in the natural-number format used
by the sharp planar graph theorem. -/
def unitGraphGridIndex1D (m : ℕ) (hm : 0 < m)
    (z : EuclideanPoint 2) : ℕ :=
  unitIntervalIndex m hm (coordinate (baseCoordinates z) 0)

theorem unitGraphGridIndex1D_mem_range (m : ℕ) (hm : 0 < m)
    (z : EuclideanPoint 2) : unitGraphGridIndex1D m hm z ∈ Finset.range m := by
  exact Finset.mem_range.mpr (unitIntervalIndex m hm _).isLt

/-- Disjoint planar assignment fibre. -/
def unitAssignedLabels1D {ι : Type*} [DecidableEq ι]
    (m : ℕ) (hm : 0 < m) (J : Finset ι)
    (z : ι → EuclideanPoint 2) (k : ℕ) : Finset ι :=
  J.filter fun i ↦ unitGraphGridIndex1D m hm (z i) = k

theorem card_unitAssignedLabels1D {ι : Type*} [DecidableEq ι]
    (m : ℕ) (hm : 0 < m) (J : Finset ι)
    (z : ι → EuclideanPoint 2) (k : ℕ) :
    (unitAssignedLabels1D m hm J z k).card =
      DyadicCells.occupancy J
        (fun i ↦ unitGraphGridIndex1D m hm (z i)) k := by
  rfl

@[simp]
theorem mem_unitAssignedLabels1D_iff
    {ι : Type*} [DecidableEq ι] {m : ℕ} {hm : 0 < m}
    {J : Finset ι} {z : ι → EuclideanPoint 2} {k : ℕ} {i : ι} :
    i ∈ unitAssignedLabels1D m hm J z k ↔
      i ∈ J ∧ unitGraphGridIndex1D m hm (z i) = k := by
  simp [unitAssignedLabels1D]

theorem pairwiseDisjoint_unitAssignedLabels1D
    {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 0 < m)
    (J : Finset ι) (z : ι → EuclideanPoint 2) (I : Finset ℕ) :
    (I : Set ℕ).PairwiseDisjoint (unitAssignedLabels1D m hm J z) := by
  intro k _hk l _hl hkl
  change Disjoint (unitAssignedLabels1D m hm J z k)
    (unitAssignedLabels1D m hm J z l)
  rw [Finset.disjoint_left]
  intro i hik hil
  exact hkl ((mem_unitAssignedLabels1D_iff.mp hik).2.symm.trans
    (mem_unitAssignedLabels1D_iff.mp hil).2)

theorem unitAssignedLabels1D_subset_indexedLabelsOverCell1D
    {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 0 < m)
    {J : Finset ι} {z : ι → EuclideanPoint 2}
    (hunit : ∀ i ∈ J,
      coordinate (baseCoordinates (z i)) 0 ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) :
    unitAssignedLabels1D m hm J z k ⊆ indexedLabelsOverCell1D J z m k := by
  intro i hi
  have hi' := mem_unitAssignedLabels1D_iff.mp hi
  rw [mem_indexedLabelsOverCell1D_iff, mem_graphBaseCell_iff]
  refine ⟨hi'.1, ?_⟩
  have hb := unitIntervalIndex_bounds hm (hunit i hi'.1)
  rw [← hi'.2]
  simpa [unitGraphGridIndex1D, gridPoint] using hb

theorem card_unitAssignedLabels1D_le_indexedLabelsOverCell1D
    {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 0 < m)
    {J : Finset ι} {z : ι → EuclideanPoint 2}
    (hunit : ∀ i ∈ J,
      coordinate (baseCoordinates (z i)) 0 ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) :
    (unitAssignedLabels1D m hm J z k).card ≤
      (indexedLabelsOverCell1D J z m k).card :=
  Finset.card_le_card
    (unitAssignedLabels1D_subset_indexedLabelsOverCell1D hm hunit k)

/-- The planar second-grid relative shell, retaining natural-number labels
and the exact inclusion required by the planar indexed graph theorem. -/
theorem exists_unitGraphGrid_relative_occupancy_shell_2d
    {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 0 < m)
    (J : Finset ι) (z : ι → EuclideanPoint 2)
    (hunit : ∀ i ∈ J,
      coordinate (baseCoordinates (z i)) 0 ∈ Set.Icc (0 : ℝ) 1)
    (cutoff L : ℕ) (hJ : 2 ≤ J.card) (hcutoff : 0 < cutoff)
    (hupper : J.card < cutoff * 2 ^ (L + 1))
    (hdiscard : m * cutoff ≤ J.card / 2) :
    ∃ j < L + 1,
      let I := RelativeDyadicCells.relativeShell (Finset.range m)
        (fun k ↦ (unitAssignedLabels1D m hm J z k).card) cutoff j
      I.Nonempty ∧ I ⊆ Finset.range m ∧
      J.card / 2 ≤ (L + 1) *
        RelativeDyadicCells.shellWeight (Finset.range m)
          (fun k ↦ (unitAssignedLabels1D m hm J z k).card) cutoff j ∧
      (∀ k ∈ I,
        cutoff * 2 ^ j ≤ (unitAssignedLabels1D m hm J z k).card ∧
          (unitAssignedLabels1D m hm J z k).card < cutoff * 2 ^ (j + 1)) ∧
      ∀ k ∈ I,
        cutoff * 2 ^ j ≤ (indexedLabelsOverCell1D J z m k).card := by
  let cell : ι → ℕ := fun i ↦ unitGraphGridIndex1D m hm (z i)
  have hmaps : ∀ i ∈ J, cell i ∈ Finset.range m := by
    intro i _hi
    exact unitGraphGridIndex1D_mem_range m hm (z i)
  obtain ⟨j, hj, hglobal, _hretained, _hdivNat, _hdivReal,
      hpointwise, _hlower, _hupperMass, _hcard⟩ :=
    RelativeDyadicCells.exists_relative_occupancy_shell_after_discard
      J (Finset.range m) cell cutoff L hmaps hcutoff hupper
  have hhalf : J.card / 2 ≤ (L + 1) *
      RelativeDyadicCells.shellWeight (Finset.range m)
        (DyadicCells.occupancy J cell) cutoff j := by
    simp only [Finset.card_range] at hglobal
    omega
  have hshellNonempty :
      (RelativeDyadicCells.relativeShell (Finset.range m)
        (DyadicCells.occupancy J cell) cutoff j).Nonempty := by
    by_contra hempty
    have heq : RelativeDyadicCells.relativeShell (Finset.range m)
        (DyadicCells.occupancy J cell) cutoff j = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hhalfPos : 0 < J.card / 2 := Nat.div_pos (by omega) (by omega)
    rw [RelativeDyadicCells.shellWeight, heq] at hhalf
    simp at hhalf
    omega
  refine ⟨j, hj, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [cell, card_unitAssignedLabels1D] using hshellNonempty
  · intro k hk
    exact (RelativeDyadicCells.mem_relativeShell_iff hcutoff).mp hk |>.1
  · simpa [cell, card_unitAssignedLabels1D] using hhalf
  · intro k hk
    have hk' : k ∈ RelativeDyadicCells.relativeShell (Finset.range m)
        (DyadicCells.occupancy J cell) cutoff j := by
      simpa [cell, card_unitAssignedLabels1D] using hk
    simpa [cell, card_unitAssignedLabels1D] using
      hpointwise k hk'
  · intro k hk
    have hk' : k ∈ RelativeDyadicCells.relativeShell (Finset.range m)
        (DyadicCells.occupancy J cell) cutoff j := by
      simpa [cell, card_unitAssignedLabels1D] using hk
    exact (hpointwise k hk').1.trans
      (card_unitAssignedLabels1D_le_indexedLabelsOverCell1D hm hunit k)

/-- Planar natural-label version of `exists_unitGraphGrid_occupied_shell`. -/
theorem exists_unitGraphGrid_occupied_shell_2d
    {ι : Type*} [DecidableEq ι] {m : ℕ} (hm : 0 < m)
    (J : Finset ι) (z : ι → EuclideanPoint 2)
    (hunit : ∀ i ∈ J,
      coordinate (baseCoordinates (z i)) 0 ∈ Set.Icc (0 : ℝ) 1)
    (L : ℕ) (hJ : J.Nonempty) (hupper : J.card < 2 ^ (L + 1)) :
    ∃ j < L + 1,
      let I := RelativeDyadicCells.relativeShell (Finset.range m)
        (fun k ↦ (unitAssignedLabels1D m hm J z k).card) 1 j
      I.Nonempty ∧ I ⊆ Finset.range m ∧
      J.card ≤ (L + 1) *
        RelativeDyadicCells.shellWeight (Finset.range m)
          (fun k ↦ (unitAssignedLabels1D m hm J z k).card) 1 j ∧
      (∀ k ∈ I,
        2 ^ j ≤ (unitAssignedLabels1D m hm J z k).card ∧
          (unitAssignedLabels1D m hm J z k).card < 2 ^ (j + 1)) ∧
      ∀ k ∈ I,
        2 ^ j ≤ (indexedLabelsOverCell1D J z m k).card := by
  let weight : ℕ → ℕ := fun k ↦ (unitAssignedLabels1D m hm J z k).card
  let cell : ι → ℕ := fun i ↦ unitGraphGridIndex1D m hm (z i)
  have hmaps : ∀ i ∈ J, cell i ∈ Finset.range m := by
    intro i _hi
    exact unitGraphGridIndex1D_mem_range m hm (z i)
  have hmass : RelativeDyadicCells.retainedWeight
      (Finset.range m) weight 1 = J.card := by
    rw [RelativeDyadicCells.retainedWeight_one_eq_sum]
    simpa [weight, cell, card_unitAssignedLabels1D] using
      DyadicCells.sum_occupancy_eq_card J (Finset.range m) cell hmaps
  have hweight : ∀ k, weight k ≤ J.card := by
    intro k
    exact Finset.card_le_card (Finset.filter_subset _ _)
  obtain ⟨j, hj, hjmass, _hdivNat, _hdivReal, hpointwise,
      _hlower, _hupperMass, _hcard⟩ :=
    RelativeDyadicCells.exists_relativeShell_weight
      (Finset.range m) weight 1 L (by omega)
      (by
        intro k _hk
        simpa using (hweight k).trans_lt hupper)
  have hshellNonempty :
      (RelativeDyadicCells.relativeShell (Finset.range m) weight 1 j).Nonempty := by
    by_contra hempty
    have heq : RelativeDyadicCells.relativeShell
        (Finset.range m) weight 1 j = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hjzero : J.card ≤ 0 := by
      rw [← hmass]
      simpa [RelativeDyadicCells.shellWeight, heq] using hjmass
    have hJpos : 0 < J.card := hJ.card_pos
    omega
  refine ⟨j, hj, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [weight] using hshellNonempty
  · intro k hk
    exact (RelativeDyadicCells.mem_relativeShell_iff (by omega)).mp hk |>.1
  · simpa [hmass, weight] using hjmass
  · intro k hk
    have hk' : k ∈ RelativeDyadicCells.relativeShell
        (Finset.range m) weight 1 j := by
      simpa [weight] using hk
    simpa [weight] using hpointwise k hk'
  · intro k hk
    have hk' : k ∈ RelativeDyadicCells.relativeShell
        (Finset.range m) weight 1 j := by
      simpa [weight] using hk
    have hlower : 2 ^ j ≤ (unitAssignedLabels1D m hm J z k).card := by
      simpa [weight] using (hpointwise k hk').1
    exact hlower.trans
      (card_unitAssignedLabels1D_le_indexedLabelsOverCell1D hm hunit k)

end
end Erdos186.PZ.ConvexDensity
