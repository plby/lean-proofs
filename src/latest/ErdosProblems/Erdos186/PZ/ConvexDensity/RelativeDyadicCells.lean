/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.DyadicCells

/-!
# Dyadic shells relative to a positive cutoff

The absolute shells in `DyadicCells` sort a weight `w` between `2^j` and
`2^(j+1)`.  In both cell decompositions of the Pham--Zakharov proof the
correct logarithmic loss is instead relative to the cutoff: the retained
weights are sorted between `cutoff * 2^j` and `cutoff * 2^(j+1)`.

This file proves the relative statement for an arbitrary natural-valued
weight.  The construction applies the exact dyadic decomposition to the
quotient `w / cutoff`; natural-division equivalences recover the desired
unrounded endpoints.  An occupancy specialization then interfaces directly
with the cutoff-discard API of `DyadicCells`.
-/

open scoped BigOperators

namespace Erdos186.PZ.ConvexDensity.RelativeDyadicCells

open Erdos186.CombinatorialTools
open Erdos186.PZ.ConvexDensity.DyadicCells

/-! ## Abstract natural-valued weights -/

/-- Indices whose weight survives the positive cutoff. -/
def retainedIndices {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (weight : ι → ℕ) (cutoff : ℕ) : Finset ι :=
  indices.filter fun i ↦ cutoff ≤ weight i

@[simp]
theorem mem_retainedIndices {ι : Type*} [DecidableEq ι]
    {indices : Finset ι} {weight : ι → ℕ} {cutoff : ℕ} {i : ι} :
    i ∈ retainedIndices indices weight cutoff ↔
      i ∈ indices ∧ cutoff ≤ weight i := by
  simp [retainedIndices]

/-- Total weight after discarding all indices below the cutoff. -/
def retainedWeight {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (weight : ι → ℕ) (cutoff : ℕ) : ℕ :=
  ∑ i ∈ retainedIndices indices weight cutoff, weight i

/-- At cutoff one, every omitted index has weight zero, so no mass is
actually discarded. -/
theorem retainedWeight_one_eq_sum {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (weight : ι → ℕ) :
    retainedWeight indices weight 1 = ∑ i ∈ indices, weight i := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi hnot
  have hlt : weight i < 1 := by
    by_contra h
    exact hnot (by simpa [retainedIndices] using
      (show i ∈ indices ∧ 1 ≤ weight i from ⟨hi, Nat.le_of_not_gt h⟩))
  omega

/-- Relative dyadic shell `j`.  Its defining quotient is equivalent, for a
positive cutoff, to the interval
`cutoff * 2^j ≤ weight i < cutoff * 2^(j+1)`. -/
def relativeShell {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (weight : ι → ℕ) (cutoff j : ℕ) : Finset ι :=
  dyadicShell (retainedIndices indices weight cutoff)
    (fun i ↦ weight i / cutoff) j

/-- Total weight on one relative dyadic shell. -/
def shellWeight {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (weight : ι → ℕ) (cutoff j : ℕ) : ℕ :=
  ∑ i ∈ relativeShell indices weight cutoff j, weight i

/-- Exact membership description of a relative shell. -/
theorem mem_relativeShell_iff {ι : Type*} [DecidableEq ι]
    {indices : Finset ι} {weight : ι → ℕ} {cutoff j : ℕ}
    (hcutoff : 0 < cutoff) {i : ι} :
    i ∈ relativeShell indices weight cutoff j ↔
      i ∈ indices ∧ cutoff * 2 ^ j ≤ weight i ∧
        weight i < cutoff * 2 ^ (j + 1) := by
  rw [relativeShell, mem_dyadicShell, mem_retainedIndices]
  constructor
  · rintro ⟨⟨hi, hretain⟩, hlevel⟩
    have hquotPos : 0 < weight i / cutoff := Nat.div_pos hretain hcutoff
    have hiShell : i ∈ dyadicShell
        (retainedIndices indices weight cutoff)
        (fun i ↦ weight i / cutoff) j :=
      mem_dyadicShell.mpr
        ⟨mem_retainedIndices.mpr ⟨hi, hretain⟩, hlevel⟩
    have hbounds := dyadicShell_bounds
      (s := retainedIndices indices weight cutoff)
      (size := fun i ↦ weight i / cutoff)
      (j := j) (x := i)
      hiShell hquotPos
    have hlower : 2 ^ j * cutoff ≤ weight i :=
      (Nat.le_div_iff_mul_le hcutoff).mp hbounds.1
    have hupper : weight i < 2 ^ (j + 1) * cutoff :=
      (Nat.div_lt_iff_lt_mul hcutoff).mp hbounds.2
    exact ⟨hi, by simpa [mul_comm] using hlower,
      by simpa [mul_comm] using hupper⟩
  · rintro ⟨hi, hlower, hupper⟩
    have hretain : cutoff ≤ weight i := by
      have hone : 1 ≤ 2 ^ j :=
        Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
      simpa using (Nat.mul_le_mul_left cutoff hone).trans hlower
    have hquotPos : 0 < weight i / cutoff := Nat.div_pos hretain hcutoff
    have hlower' : 2 ^ j ≤ weight i / cutoff :=
      (Nat.le_div_iff_mul_le hcutoff).mpr (by simpa [mul_comm] using hlower)
    have hupper' : weight i / cutoff < 2 ^ (j + 1) :=
      (Nat.div_lt_iff_lt_mul hcutoff).mpr (by simpa [mul_comm] using hupper)
    have hlevel : dyadicLevel (weight i / cutoff) = j := by
      apply Nat.le_antisymm
      · exact Nat.lt_succ_iff.mp
          (Nat.log_lt_of_lt_pow hquotPos.ne' hupper')
      · exact (Nat.le_log_iff_pow_le Nat.one_lt_two hquotPos.ne').mpr hlower'
    exact ⟨⟨hi, hretain⟩, hlevel⟩

/-- Pointwise interval bounds, in a convenient projection form. -/
theorem weight_bounds_of_mem_relativeShell {ι : Type*} [DecidableEq ι]
    {indices : Finset ι} {weight : ι → ℕ} {cutoff j : ℕ}
    (hcutoff : 0 < cutoff) {i : ι}
    (hi : i ∈ relativeShell indices weight cutoff j) :
    cutoff * 2 ^ j ≤ weight i ∧
      weight i < cutoff * 2 ^ (j + 1) :=
  ((mem_relativeShell_iff hcutoff).mp hi).2

/-- Summed lower endpoint of a relative shell. -/
theorem shell_card_mul_lower_le_weight {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (weight : ι → ℕ) (cutoff j : ℕ)
    (hcutoff : 0 < cutoff) :
    (relativeShell indices weight cutoff j).card * (cutoff * 2 ^ j) ≤
      shellWeight indices weight cutoff j := by
  calc
    (relativeShell indices weight cutoff j).card * (cutoff * 2 ^ j) =
        ∑ _i ∈ relativeShell indices weight cutoff j, cutoff * 2 ^ j := by simp
    _ ≤ ∑ i ∈ relativeShell indices weight cutoff j, weight i := by
      exact Finset.sum_le_sum fun i hi ↦
        (weight_bounds_of_mem_relativeShell hcutoff hi).1

/-- Summed upper endpoint of a relative shell. -/
theorem shell_weight_le_upper_mul_card {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (weight : ι → ℕ) (cutoff j : ℕ)
    (hcutoff : 0 < cutoff) :
    shellWeight indices weight cutoff j ≤
      (cutoff * 2 ^ (j + 1)) *
        (relativeShell indices weight cutoff j).card := by
  calc
    shellWeight indices weight cutoff j ≤
        ∑ _i ∈ relativeShell indices weight cutoff j,
          cutoff * 2 ^ (j + 1) := by
      exact Finset.sum_le_sum fun i hi ↦
        Nat.le_of_lt (weight_bounds_of_mem_relativeShell hcutoff hi).2
    _ = (cutoff * 2 ^ (j + 1)) *
        (relativeShell indices weight cutoff j).card := by simp [mul_comm]

/-- The selected shell contains at least its weight divided by the upper
endpoint many indices. -/
theorem shell_weight_div_upper_le_card {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (weight : ι → ℕ) (cutoff j : ℕ)
    (hcutoff : 0 < cutoff) :
    shellWeight indices weight cutoff j / (cutoff * 2 ^ (j + 1)) ≤
      (relativeShell indices weight cutoff j).card := by
  exact Nat.div_le_of_le_mul
    (shell_weight_le_upper_mul_card indices weight cutoff j hcutoff)

/-- Relative dyadic mass pigeonhole for an arbitrary natural-valued weight.

Only retained indices need the stated upper bound.  The `L+1` shells are
therefore exactly sufficient when retained weights are below
`cutoff * 2^(L+1)`. -/
theorem exists_relativeShell_weight {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (weight : ι → ℕ) (cutoff L : ℕ)
    (hcutoff : 0 < cutoff)
    (hupper : ∀ i ∈ retainedIndices indices weight cutoff,
      weight i < cutoff * 2 ^ (L + 1)) :
    ∃ j < L + 1,
      retainedWeight indices weight cutoff ≤
        (L + 1) * shellWeight indices weight cutoff j ∧
      retainedWeight indices weight cutoff / (L + 1) ≤
        shellWeight indices weight cutoff j ∧
      (retainedWeight indices weight cutoff : ℝ) / (L + 1) ≤
        (shellWeight indices weight cutoff j : ℝ) ∧
      (∀ i ∈ relativeShell indices weight cutoff j,
        cutoff * 2 ^ j ≤ weight i ∧
          weight i < cutoff * 2 ^ (j + 1)) ∧
      (relativeShell indices weight cutoff j).card * (cutoff * 2 ^ j) ≤
        shellWeight indices weight cutoff j ∧
      shellWeight indices weight cutoff j ≤
        (cutoff * 2 ^ (j + 1)) *
          (relativeShell indices weight cutoff j).card ∧
      shellWeight indices weight cutoff j / (cutoff * 2 ^ (j + 1)) ≤
        (relativeShell indices weight cutoff j).card := by
  let retained := retainedIndices indices weight cutoff
  have hsize : ∀ i ∈ retained, 0 < weight i / cutoff := by
    intro i hi
    exact Nat.div_pos (mem_retainedIndices.mp hi).2 hcutoff
  have hquotUpper : ∀ i ∈ retained, weight i / cutoff < 2 ^ (L + 1) := by
    intro i hi
    apply (Nat.div_lt_iff_lt_mul hcutoff).mpr
    simpa [mul_comm] using hupper i hi
  obtain ⟨j, hj, hjmassReal⟩ :=
    exists_dyadicShell_mass retained (fun i ↦ weight i / cutoff)
      (fun i ↦ (weight i : ℝ)) L hsize hquotUpper
      (by intro i hi; positivity)
  have hjmass : retainedWeight indices weight cutoff ≤
      (L + 1) * shellWeight indices weight cutoff j := by
    exact_mod_cast hjmassReal
  have hdivNat : retainedWeight indices weight cutoff / (L + 1) ≤
      shellWeight indices weight cutoff j := by
    apply Nat.div_le_of_le_mul
    simpa [mul_comm] using hjmass
  have hLpos : (0 : ℝ) < L + 1 := by positivity
  have hdivReal : (retainedWeight indices weight cutoff : ℝ) / (L + 1) ≤
      (shellWeight indices weight cutoff j : ℝ) := by
    rw [div_le_iff₀ hLpos]
    exact_mod_cast (by simpa [mul_comm] using hjmass)
  refine ⟨j, hj, hjmass, hdivNat, hdivReal, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact weight_bounds_of_mem_relativeShell hcutoff hi
  · exact shell_card_mul_lower_le_weight indices weight cutoff j hcutoff
  · exact shell_weight_le_upper_mul_card indices weight cutoff j hcutoff
  · exact shell_weight_div_upper_le_card indices weight cutoff j hcutoff

/-! ## Occupancy specialization -/

@[simp]
theorem retainedIndices_occupancy {α ι : Type*} [DecidableEq α]
    [DecidableEq ι] (points : Finset α) (cells : Finset ι)
    (cell : α → ι) (cutoff : ℕ) :
    retainedIndices cells (occupancy points cell) cutoff =
      retainedCells points cells cell cutoff := by
  ext i
  simp

@[simp]
theorem retainedWeight_occupancy {α ι : Type*} [DecidableEq α]
    [DecidableEq ι] (points : Finset α) (cells : Finset ι)
    (cell : α → ι) (cutoff : ℕ) :
    retainedWeight cells (occupancy points cell) cutoff =
      retainedMass points cells cell cutoff := by
  simp [retainedWeight, retainedIndices_occupancy, retainedMass]

/-- Cutoff-relative occupancy selection after the sparse cells are
discarded.  The only logarithmic-range hypothesis is the natural one
`points.card < cutoff * 2^(L+1)`. -/
theorem exists_relative_occupancy_shell_after_discard
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (points : Finset α) (cells : Finset ι) (cell : α → ι)
    (cutoff L : ℕ) (hmaps : ∀ x ∈ points, cell x ∈ cells)
    (hcutoff : 0 < cutoff)
    (hupper : points.card < cutoff * 2 ^ (L + 1)) :
    ∃ j < L + 1,
      points.card ≤ cells.card * cutoff +
        (L + 1) * shellWeight cells (occupancy points cell) cutoff j ∧
      retainedMass points cells cell cutoff ≤
        (L + 1) * shellWeight cells (occupancy points cell) cutoff j ∧
      retainedMass points cells cell cutoff / (L + 1) ≤
        shellWeight cells (occupancy points cell) cutoff j ∧
      (retainedMass points cells cell cutoff : ℝ) / (L + 1) ≤
        (shellWeight cells (occupancy points cell) cutoff j : ℝ) ∧
      (∀ i ∈ relativeShell cells (occupancy points cell) cutoff j,
        cutoff * 2 ^ j ≤ occupancy points cell i ∧
          occupancy points cell i < cutoff * 2 ^ (j + 1)) ∧
      (relativeShell cells (occupancy points cell) cutoff j).card *
          (cutoff * 2 ^ j) ≤
        shellWeight cells (occupancy points cell) cutoff j ∧
      shellWeight cells (occupancy points cell) cutoff j ≤
        (cutoff * 2 ^ (j + 1)) *
          (relativeShell cells (occupancy points cell) cutoff j).card ∧
      shellWeight cells (occupancy points cell) cutoff j /
          (cutoff * 2 ^ (j + 1)) ≤
        (relativeShell cells (occupancy points cell) cutoff j).card := by
  have habstract := exists_relativeShell_weight cells (occupancy points cell)
    cutoff L hcutoff (by
      intro i hi
      exact (occupancy_le_card points cell i).trans_lt hupper)
  obtain ⟨j, hj, hmass, hdivNat, hdivReal, hpointwise,
    hlower, hupperMass, hcard⟩ := habstract
  have hglobal : points.card ≤ cells.card * cutoff +
      (L + 1) * shellWeight cells (occupancy points cell) cutoff j :=
    (card_le_discard_cost_add_retainedMass points cells cell cutoff hmaps).trans
      (Nat.add_le_add_left (by simpa using hmass) _)
  refine ⟨j, hj, hglobal, by simpa using hmass, by simpa using hdivNat,
    by simpa using hdivReal, hpointwise, hlower, hupperMass, hcard⟩

end Erdos186.PZ.ConvexDensity.RelativeDyadicCells
