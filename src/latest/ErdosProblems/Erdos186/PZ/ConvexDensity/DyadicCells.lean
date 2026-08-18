/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CombinatorialTools

/-!
# Finite dyadic cell selection for the Pham--Zakharov density lemma

This file isolates the counting part of the grid argument in Lemma 1 of
Pham--Zakharov.  Geometry enters that argument only by assigning every point
to one of finitely many cells.  We therefore work with an arbitrary map
`cell : alpha -> iota` and a finite set of admissible cell indices.

The argument has two exact losses.

* Cells containing fewer than `cutoff` points are discarded.  Their total
  mass is at most `cells.card * cutoff` (and the sharper bound using the
  number of light cells is also recorded).
* The retained occupancies are split according to their lower binary
  logarithm.  If every occupancy is below `2 ^ (L + 1)`, one of the `L + 1`
  dyadic scales carries at least a `1 / (L + 1)` share of the retained mass.

The final theorem gives the chosen scale, both multiplicative and division
forms of the mass estimate, the dyadic interval for every selected cell, and
both cardinality inequalities obtained by summing those interval bounds.
No floor or Euclidean geometry is used here.
-/

open scoped BigOperators

namespace Erdos186.PZ.ConvexDensity.DyadicCells

open Erdos186.CombinatorialTools

/-! ## Cells, occupancies, and the cutoff decomposition -/

/-- The number of points assigned to the cell with index `i`. -/
def occupancy {alpha iota : Type*} [DecidableEq alpha] [DecidableEq iota]
    (points : Finset alpha) (cell : alpha -> iota) (i : iota) : ℕ :=
  (points.filter fun x => cell x = i).card

/-- Candidate cells whose occupancy is strictly below the cutoff. -/
def lightCells {alpha iota : Type*} [DecidableEq alpha] [DecidableEq iota]
    (points : Finset alpha) (cells : Finset iota) (cell : alpha -> iota)
    (cutoff : ℕ) : Finset iota :=
  cells.filter fun i => occupancy points cell i < cutoff

/-- Candidate cells which survive the cutoff. -/
def retainedCells {alpha iota : Type*} [DecidableEq alpha] [DecidableEq iota]
    (points : Finset alpha) (cells : Finset iota) (cell : alpha -> iota)
    (cutoff : ℕ) : Finset iota :=
  cells.filter fun i => cutoff <= occupancy points cell i

/-- The point mass carried by the cells which survive the cutoff. -/
def retainedMass {alpha iota : Type*} [DecidableEq alpha] [DecidableEq iota]
    (points : Finset alpha) (cells : Finset iota) (cell : alpha -> iota)
    (cutoff : ℕ) : ℕ :=
  ∑ i ∈ retainedCells points cells cell cutoff, occupancy points cell i

@[simp]
theorem mem_lightCells {alpha iota : Type*} [DecidableEq alpha]
    [DecidableEq iota] {points : Finset alpha} {cells : Finset iota}
    {cell : alpha -> iota} {cutoff : ℕ} {i : iota} :
    i ∈ lightCells points cells cell cutoff ↔
      i ∈ cells ∧ occupancy points cell i < cutoff := by
  simp [lightCells]

@[simp]
theorem mem_retainedCells {alpha iota : Type*} [DecidableEq alpha]
    [DecidableEq iota] {points : Finset alpha} {cells : Finset iota}
    {cell : alpha -> iota} {cutoff : ℕ} {i : iota} :
    i ∈ retainedCells points cells cell cutoff ↔
      i ∈ cells ∧ cutoff ≤ occupancy points cell i := by
  simp [retainedCells]

/-- Occupancy never exceeds the total number of points. -/
theorem occupancy_le_card {alpha iota : Type*} [DecidableEq alpha]
    [DecidableEq iota] (points : Finset alpha) (cell : alpha -> iota)
    (i : iota) :
    occupancy points cell i ≤ points.card := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- If all points map into `cells`, the sum of the cell occupancies is
exactly the total number of points. -/
theorem sum_occupancy_eq_card {alpha iota : Type*} [DecidableEq alpha]
    [DecidableEq iota] (points : Finset alpha) (cells : Finset iota)
    (cell : alpha -> iota) (hmaps : ∀ x ∈ points, cell x ∈ cells) :
    (∑ i ∈ cells, occupancy points cell i) = points.card := by
  simpa [occupancy] using
    (Finset.sum_fiberwise_of_maps_to hmaps (fun _ => (1 : ℕ)))

/-- Light and retained cells partition the candidate cells. -/
theorem lightCells_union_retainedCells {alpha iota : Type*}
    [DecidableEq alpha] [DecidableEq iota] (points : Finset alpha)
    (cells : Finset iota) (cell : alpha -> iota) (cutoff : ℕ) :
    lightCells points cells cell cutoff ∪
        retainedCells points cells cell cutoff = cells := by
  ext i
  simp only [Finset.mem_union, mem_lightCells, mem_retainedCells]
  constructor
  · rintro (hi | hi) <;> exact hi.1
  · intro hi
    by_cases hlight : occupancy points cell i < cutoff
    · exact Or.inl ⟨hi, hlight⟩
    · exact Or.inr ⟨hi, Nat.le_of_not_gt hlight⟩

/-- The light and retained parts are disjoint. -/
theorem disjoint_lightCells_retainedCells {alpha iota : Type*}
    [DecidableEq alpha] [DecidableEq iota] (points : Finset alpha)
    (cells : Finset iota) (cell : alpha -> iota) (cutoff : ℕ) :
    Disjoint (lightCells points cells cell cutoff)
      (retainedCells points cells cell cutoff) := by
  refine Finset.disjoint_left.mpr ?_
  intro i hil hir
  have hil' := (mem_lightCells.mp hil).2
  have hir' := (mem_retainedCells.mp hir).2
  omega

/-- Exact decomposition into discarded and retained point mass. -/
theorem light_mass_add_retainedMass_eq_card {alpha iota : Type*}
    [DecidableEq alpha] [DecidableEq iota] (points : Finset alpha)
    (cells : Finset iota) (cell : alpha -> iota) (cutoff : ℕ)
    (hmaps : ∀ x ∈ points, cell x ∈ cells) :
    (∑ i ∈ lightCells points cells cell cutoff, occupancy points cell i) +
        retainedMass points cells cell cutoff = points.card := by
  rw [← sum_occupancy_eq_card points cells cell hmaps]
  change
    (∑ i ∈ lightCells points cells cell cutoff, occupancy points cell i) +
        (∑ i ∈ retainedCells points cells cell cutoff,
          occupancy points cell i) =
      ∑ i ∈ cells, occupancy points cell i
  rw [← Finset.sum_union
    (disjoint_lightCells_retainedCells points cells cell cutoff)]
  rw [lightCells_union_retainedCells]

/-- The discarded mass is bounded by the cutoff times the actual number of
light cells. -/
theorem light_mass_le_light_card_mul_cutoff {alpha iota : Type*}
    [DecidableEq alpha] [DecidableEq iota] (points : Finset alpha)
    (cells : Finset iota) (cell : alpha -> iota) (cutoff : ℕ) :
    (∑ i ∈ lightCells points cells cell cutoff, occupancy points cell i) ≤
      (lightCells points cells cell cutoff).card * cutoff := by
  calc
    (∑ i ∈ lightCells points cells cell cutoff, occupancy points cell i) ≤
        ∑ _i ∈ lightCells points cells cell cutoff, cutoff := by
      exact Finset.sum_le_sum fun i hi =>
        Nat.le_of_lt (mem_lightCells.mp hi).2
    _ = (lightCells points cells cell cutoff).card * cutoff := by simp

/-- The usual grid form of the discard estimate: at most `cells.card *
cutoff` points are lost. -/
theorem light_mass_le_cells_card_mul_cutoff {alpha iota : Type*}
    [DecidableEq alpha] [DecidableEq iota] (points : Finset alpha)
    (cells : Finset iota) (cell : alpha -> iota) (cutoff : ℕ) :
    (∑ i ∈ lightCells points cells cell cutoff, occupancy points cell i) ≤
      cells.card * cutoff := by
  calc
    (∑ i ∈ lightCells points cells cell cutoff, occupancy points cell i) ≤
        (lightCells points cells cell cutoff).card * cutoff :=
      light_mass_le_light_card_mul_cutoff points cells cell cutoff
    _ ≤ cells.card * cutoff := by
      exact Nat.mul_le_mul_right cutoff
        (Finset.card_le_card (Finset.filter_subset _ _))

/-- Division-free retained-mass estimate after throwing away sparse cells. -/
theorem card_le_discard_cost_add_retainedMass {alpha iota : Type*}
    [DecidableEq alpha] [DecidableEq iota] (points : Finset alpha)
    (cells : Finset iota) (cell : alpha -> iota) (cutoff : ℕ)
    (hmaps : ∀ x ∈ points, cell x ∈ cells) :
    points.card ≤ cells.card * cutoff +
      retainedMass points cells cell cutoff := by
  have hsplit := light_mass_add_retainedMass_eq_card
    points cells cell cutoff hmaps
  have hlight := light_mass_le_cells_card_mul_cutoff
    points cells cell cutoff
  omega

/-- Subtraction form of the retained-mass estimate. -/
theorem card_sub_discard_cost_le_retainedMass {alpha iota : Type*}
    [DecidableEq alpha] [DecidableEq iota] (points : Finset alpha)
    (cells : Finset iota) (cell : alpha -> iota) (cutoff : ℕ)
    (hmaps : ∀ x ∈ points, cell x ∈ cells) :
    points.card - cells.card * cutoff ≤
      retainedMass points cells cell cutoff := by
  have h := card_le_discard_cost_add_retainedMass
    points cells cell cutoff hmaps
  omega

/-- Cast variant of the retained-mass estimate.  Unlike natural
subtraction, this records the literal real loss used in density estimates. -/
theorem card_cast_sub_discard_cost_le_retainedMass {alpha iota : Type*}
    [DecidableEq alpha] [DecidableEq iota] (points : Finset alpha)
    (cells : Finset iota) (cell : alpha -> iota) (cutoff : ℕ)
    (hmaps : ∀ x ∈ points, cell x ∈ cells) :
    (points.card : Real) - (cells.card : Real) * cutoff ≤
      (retainedMass points cells cell cutoff : Real) := by
  have h := card_le_discard_cost_add_retainedMass
    points cells cell cutoff hmaps
  have hReal : (points.card : ℝ) ≤
      (cells.card : ℝ) * cutoff +
        (retainedMass points cells cell cutoff : ℝ) := by
    exact_mod_cast h
  linarith

/-- Literal `c * r ^ d` version of the sparse-cell discard. -/
theorem card_sub_grid_cutoff_le_retainedMass {alpha iota : Type*}
    [DecidableEq alpha] [DecidableEq iota] (points : Finset alpha)
    (cells : Finset iota) (cell : alpha -> iota) (c r d : ℕ)
    (hmaps : ∀ x ∈ points, cell x ∈ cells) :
    points.card - cells.card * (c * r ^ d) ≤
      retainedMass points cells cell (c * r ^ d) := by
  exact card_sub_discard_cost_le_retainedMass points cells cell
    (c * r ^ d) hmaps

/-- Real-valued `c * r ^ d` version of the sparse-cell discard. -/
theorem card_cast_sub_grid_cutoff_le_retainedMass {alpha iota : Type*}
    [DecidableEq alpha] [DecidableEq iota] (points : Finset alpha)
    (cells : Finset iota) (cell : alpha -> iota) (c r d : ℕ)
    (hmaps : ∀ x ∈ points, cell x ∈ cells) :
    (points.card : ℝ) - (cells.card : ℝ) * (c * r ^ d : ℕ) ≤
      (retainedMass points cells cell (c * r ^ d) : ℝ) := by
  exact card_cast_sub_discard_cost_le_retainedMass points cells cell
    (c * r ^ d) hmaps

/-! ## Dyadic occupancy scales -/

/-- Retained cells on the dyadic occupancy scale `j`. -/
def scaleCells {alpha iota : Type*} [DecidableEq alpha] [DecidableEq iota]
    (points : Finset alpha) (cells : Finset iota) (cell : alpha -> iota)
    (cutoff j : ℕ) : Finset iota :=
  dyadicShell (retainedCells points cells cell cutoff)
    (occupancy points cell) j

/-- Total point mass on one retained dyadic occupancy scale. -/
def scaleMass {alpha iota : Type*} [DecidableEq alpha] [DecidableEq iota]
    (points : Finset alpha) (cells : Finset iota) (cell : alpha -> iota)
    (cutoff j : ℕ) : ℕ :=
  ∑ i ∈ scaleCells points cells cell cutoff j, occupancy points cell i

@[simp]
theorem mem_scaleCells {alpha iota : Type*} [DecidableEq alpha]
    [DecidableEq iota] {points : Finset alpha} {cells : Finset iota}
    {cell : alpha -> iota} {cutoff j : ℕ} {i : iota} :
    i ∈ scaleCells points cells cell cutoff j ↔
      i ∈ cells ∧ cutoff ≤ occupancy points cell i ∧
        dyadicLevel (occupancy points cell i) = j := by
  simp [scaleCells, and_assoc]

/-- Every cell in `scaleCells j` has occupancy in the half-open interval
`[2^j, 2^(j+1))`. -/
theorem occupancy_bounds_of_mem_scaleCells {alpha iota : Type*}
    [DecidableEq alpha] [DecidableEq iota] {points : Finset alpha}
    {cells : Finset iota} {cell : alpha -> iota} {cutoff j : ℕ}
    {i : iota} (hi : i ∈ scaleCells points cells cell cutoff j)
    (hcutoff : 0 < cutoff) :
    2 ^ j ≤ occupancy points cell i ∧
      occupancy points cell i < 2 ^ (j + 1) := by
  apply dyadicShell_bounds hi
  exact hcutoff.trans_le (mem_retainedCells.mp
    (mem_dyadicShell.mp hi).1).2

/-- Summing the lower endpoint of a dyadic occupancy interval. -/
theorem scale_card_mul_lower_le_mass {alpha iota : Type*}
    [DecidableEq alpha] [DecidableEq iota] (points : Finset alpha)
    (cells : Finset iota) (cell : alpha -> iota) (cutoff j : ℕ)
    (hcutoff : 0 < cutoff) :
    (scaleCells points cells cell cutoff j).card * 2 ^ j ≤
      scaleMass points cells cell cutoff j := by
  calc
    (scaleCells points cells cell cutoff j).card * 2 ^ j =
        ∑ _i ∈ scaleCells points cells cell cutoff j, 2 ^ j := by simp
    _ ≤ ∑ i ∈ scaleCells points cells cell cutoff j,
        occupancy points cell i := by
      exact Finset.sum_le_sum fun i hi =>
        (occupancy_bounds_of_mem_scaleCells hi hcutoff).1

/-- Summing the upper endpoint of a dyadic occupancy interval. -/
theorem scale_mass_le_upper_mul_card {alpha iota : Type*}
    [DecidableEq alpha] [DecidableEq iota] (points : Finset alpha)
    (cells : Finset iota) (cell : alpha -> iota) (cutoff j : ℕ)
    (hcutoff : 0 < cutoff) :
    scaleMass points cells cell cutoff j ≤
      2 ^ (j + 1) * (scaleCells points cells cell cutoff j).card := by
  calc
    scaleMass points cells cell cutoff j ≤
        ∑ _i ∈ scaleCells points cells cell cutoff j, 2 ^ (j + 1) := by
      exact Finset.sum_le_sum fun i hi =>
        Nat.le_of_lt (occupancy_bounds_of_mem_scaleCells hi hcutoff).2
    _ = 2 ^ (j + 1) *
        (scaleCells points cells cell cutoff j).card := by simp [mul_comm]

/-- Consequently the number of occupied cells is at least the scale mass
divided by the upper dyadic endpoint. -/
theorem scale_mass_div_upper_le_card {alpha iota : Type*}
    [DecidableEq alpha] [DecidableEq iota] (points : Finset alpha)
    (cells : Finset iota) (cell : alpha -> iota) (cutoff j : ℕ)
    (hcutoff : 0 < cutoff) :
    scaleMass points cells cell cutoff j / 2 ^ (j + 1) ≤
      (scaleCells points cells cell cutoff j).card := by
  exact Nat.div_le_of_le_mul
    (scale_mass_le_upper_mul_card points cells cell cutoff j hcutoff)

/-- Real cast of the summed lower-endpoint inequality. -/
theorem scale_card_mul_lower_le_mass_cast {alpha iota : Type*}
    [DecidableEq alpha] [DecidableEq iota] (points : Finset alpha)
    (cells : Finset iota) (cell : alpha -> iota) (cutoff j : ℕ)
    (hcutoff : 0 < cutoff) :
    ((scaleCells points cells cell cutoff j).card : ℝ) * (2 : ℝ) ^ j ≤
      (scaleMass points cells cell cutoff j : ℝ) := by
  exact_mod_cast
    (scale_card_mul_lower_le_mass points cells cell cutoff j hcutoff)

/-- Real cast of the summed upper-endpoint inequality. -/
theorem scale_mass_cast_le_upper_mul_card {alpha iota : Type*}
    [DecidableEq alpha] [DecidableEq iota] (points : Finset alpha)
    (cells : Finset iota) (cell : alpha -> iota) (cutoff j : ℕ)
    (hcutoff : 0 < cutoff) :
    (scaleMass points cells cell cutoff j : ℝ) ≤
      (2 : ℝ) ^ (j + 1) *
        (scaleCells points cells cell cutoff j).card := by
  exact_mod_cast
    (scale_mass_le_upper_mul_card points cells cell cutoff j hcutoff)

/-- Real, floor-free form of the lower bound for the number of selected
cells. -/
theorem scale_mass_cast_div_upper_le_card {alpha iota : Type*}
    [DecidableEq alpha] [DecidableEq iota] (points : Finset alpha)
    (cells : Finset iota) (cell : alpha -> iota) (cutoff j : ℕ)
    (hcutoff : 0 < cutoff) :
    (scaleMass points cells cell cutoff j : ℝ) / (2 : ℝ) ^ (j + 1) ≤
      ((scaleCells points cells cell cutoff j).card : ℝ) := by
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (j + 1))]
  simpa [mul_comm] using
    scale_mass_cast_le_upper_mul_card points cells cell cutoff j hcutoff

/-! ## The combined finite selection lemma -/

/-- Exact finite dyadic/grid mass selection.

After discarding cells of occupancy below `cutoff`, this chooses one of the
`L + 1` dyadic occupancy scales.  `hupper` can normally be discharged from
the trivial bound `occupancy <= points.card`; it is stated as a bound on the
total point set to make the result directly usable by the grid argument.

The first two inequalities are respectively the discard estimate and the
dyadic logarithmic loss.  Both natural-division and real-division forms are
included, followed by the pointwise occupancy interval and its two summed
cardinality consequences. -/
theorem exists_dyadic_scale_after_discard {alpha iota : Type*}
    [DecidableEq alpha] [DecidableEq iota] (points : Finset alpha)
    (cells : Finset iota) (cell : alpha -> iota) (cutoff L : ℕ)
    (hmaps : ∀ x ∈ points, cell x ∈ cells) (hcutoff : 0 < cutoff)
    (hupper : points.card < 2 ^ (L + 1)) :
    ∃ j < L + 1,
      points.card ≤ cells.card * cutoff +
        (L + 1) * scaleMass points cells cell cutoff j ∧
      retainedMass points cells cell cutoff ≤
        (L + 1) * scaleMass points cells cell cutoff j ∧
      retainedMass points cells cell cutoff / (L + 1) ≤
        scaleMass points cells cell cutoff j ∧
      (retainedMass points cells cell cutoff : Real) / (L + 1) ≤
        (scaleMass points cells cell cutoff j : Real) ∧
      ((points.card : Real) - (cells.card : Real) * cutoff) / (L + 1) ≤
        (scaleMass points cells cell cutoff j : Real) ∧
      (∀ i ∈ scaleCells points cells cell cutoff j,
        2 ^ j ≤ occupancy points cell i ∧
          occupancy points cell i < 2 ^ (j + 1)) ∧
      (scaleCells points cells cell cutoff j).card * 2 ^ j ≤
        scaleMass points cells cell cutoff j ∧
      scaleMass points cells cell cutoff j ≤
        2 ^ (j + 1) * (scaleCells points cells cell cutoff j).card ∧
      scaleMass points cells cell cutoff j / 2 ^ (j + 1) ≤
        (scaleCells points cells cell cutoff j).card ∧
      (scaleMass points cells cell cutoff j : Real) /
          (2 : Real) ^ (j + 1) ≤
        ((scaleCells points cells cell cutoff j).card : Real) := by
  let retained := retainedCells points cells cell cutoff
  have hsize : ∀ i ∈ retained, 0 < occupancy points cell i := by
    intro i hi
    exact hcutoff.trans_le (mem_retainedCells.mp hi).2
  have hoccUpper : ∀ i ∈ retained,
      occupancy points cell i < 2 ^ (L + 1) := by
    intro i _hi
    exact (occupancy_le_card points cell i).trans_lt hupper
  obtain ⟨j, hj, hjmassReal⟩ :=
    exists_dyadicShell_mass retained (occupancy points cell)
      (fun i => (occupancy points cell i : Real)) L hsize hoccUpper
      (by intro i hi; positivity)
  have hjmass : retainedMass points cells cell cutoff ≤
      (L + 1) * scaleMass points cells cell cutoff j := by
    exact_mod_cast hjmassReal
  have hglobal : points.card ≤ cells.card * cutoff +
      (L + 1) * scaleMass points cells cell cutoff j :=
    (card_le_discard_cost_add_retainedMass points cells cell cutoff hmaps).trans
      (Nat.add_le_add_left hjmass _)
  have hdivNat : retainedMass points cells cell cutoff / (L + 1) ≤
      scaleMass points cells cell cutoff j := by
    apply Nat.div_le_of_le_mul
    simpa [mul_comm] using hjmass
  have hLpos : (0 : Real) < L + 1 := by positivity
  have hdivReal : (retainedMass points cells cell cutoff : Real) / (L + 1) ≤
      (scaleMass points cells cell cutoff j : Real) := by
    rw [div_le_iff₀ hLpos]
    exact_mod_cast (by simpa [mul_comm] using hjmass)
  have hglobalDivReal :
      ((points.card : Real) - (cells.card : Real) * cutoff) / (L + 1) ≤
        (scaleMass points cells cell cutoff j : Real) := by
    rw [div_le_iff₀ hLpos]
    have hglobalReal : (points.card : Real) ≤
        (cells.card : Real) * cutoff +
          (L + 1 : ℕ) * (scaleMass points cells cell cutoff j : ℕ) := by
      exact_mod_cast hglobal
    push_cast at hglobalReal ⊢
    linarith
  refine ⟨j, hj, hglobal, hjmass, hdivNat, hdivReal, hglobalDivReal,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact occupancy_bounds_of_mem_scaleCells hi hcutoff
  · exact scale_card_mul_lower_le_mass points cells cell cutoff j hcutoff
  · exact scale_mass_le_upper_mul_card points cells cell cutoff j hcutoff
  · exact scale_mass_div_upper_le_card points cells cell cutoff j hcutoff
  · exact scale_mass_cast_div_upper_le_card points cells cell cutoff j hcutoff

end Erdos186.PZ.ConvexDensity.DyadicCells
