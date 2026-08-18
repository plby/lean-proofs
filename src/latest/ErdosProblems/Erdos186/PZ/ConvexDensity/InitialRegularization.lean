/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.GridPartition
import ErdosProblems.Erdos186.PZ.ConvexDensity.RelativeDyadicCells
import ErdosProblems.Erdos186.PZ.ConvexDensity.BranchNumerics

/-!
# Initial relative-occupancy regularization

This is the exact finite combinatorial package used before the geometric
boundary argument.  Its dyadic loss depends only on the supplied relative
range `L`, never on the total number of points.
-/

open Set

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

open GridPartition RelativeDyadicCells

/-- The explicit logarithmic level count is long enough to cover every
possible occupancy above the initial relative cutoff. -/
theorem card_lt_initialOccupancyCutoff_mul_two_pow_dyadicLevelCount
    {delta : ℝ} {n : ℕ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hn : 0 < n) :
    n < initialOccupancyCutoff delta n *
      2 ^ (dyadicLevelCount delta + 1) := by
  let x : ℝ := Real.logb 2 (1 / delta)
  have hinvOne : 1 ≤ 1 / delta := by
    rw [le_div_iff₀ hdelta]
    nlinarith
  have hx : 0 ≤ x := by
    exact Real.logb_nonneg (by norm_num) hinvOne
  have hceil : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
  have hpowReal : 1 / delta ≤ (2 : ℝ) ^ (Nat.ceil x : ℕ) := by
    have hp := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hceil
    rw [Real.rpow_natCast] at hp
    have hlogb : (2 : ℝ) ^ x = 1 / delta := by
      dsimp only [x]
      exact Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
    simpa only [hlogb] using hp
  have hcutoff : 2 * delta * (n : ℝ) ≤
      (initialOccupancyCutoff delta n : ℝ) := by
    exact Nat.le_ceil (2 * delta * (n : ℝ))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlarge : (n : ℝ) <
      (initialOccupancyCutoff delta n : ℝ) *
        ((2 : ℝ) ^ (Nat.ceil x : ℕ) * 4) := by
    have hprod : 8 * (n : ℝ) ≤
        (initialOccupancyCutoff delta n : ℝ) *
          ((2 : ℝ) ^ (Nat.ceil x : ℕ) * 4) := by
      calc
        8 * (n : ℝ) = (2 * delta * n) * ((1 / delta) * 4) := by
          field_simp
          ring
        _ ≤ (initialOccupancyCutoff delta n : ℝ) *
            ((2 : ℝ) ^ (Nat.ceil x : ℕ) * 4) := by
          gcongr <;> positivity
    linarith
  have hpowNat : 2 ^ (dyadicLevelCount delta + 1) =
      2 ^ (Nat.ceil x) * 4 := by
    change 2 ^ (Nat.ceil x + 1 + 1) = _
    simp [pow_succ]
    ring
  rw [hpowNat]
  exact_mod_cast hlarge

/-- After discarding sparse normalized grid cells, one relative dyadic shell
is nonempty, consists entirely of `delta`-heavy cells, and carries the usual
`L+1` fraction of the retained mass. -/
theorem exists_initial_heavy_cell_shell
    {d : ℕ} {mesh delta : ℝ} {cutoff L : ℕ}
    (X : Finset (EuclideanPoint d))
    (hXne : X.Nonempty)
    (hmesh : 0 < mesh)
    (hXcube : (X : Set (EuclideanPoint d)) ⊆ normalizedCube d)
    (hcutoff : 0 < cutoff)
    (hupper : X.card < cutoff * 2 ^ (L + 1))
    (hdiscard : (candidateGridIndices d mesh).card * cutoff ≤ X.card / 2)
    (hheavy : ∀ occupancy : ℕ, cutoff ≤ occupancy →
      delta * (X.card : ℝ) < occupancy) :
    ∃ j < L + 1,
      let J := relativeShell (candidateGridIndices d mesh)
        (DyadicCells.occupancy X (gridIndex mesh)) cutoff j
      J.Nonempty ∧
      X.card / 2 ≤ (L + 1) *
        shellWeight (candidateGridIndices d mesh)
          (DyadicCells.occupancy X (gridIndex mesh)) cutoff j ∧
      X.card ≤ 2 * ((L + 1) *
        shellWeight (candidateGridIndices d mesh)
          (DyadicCells.occupancy X (gridIndex mesh)) cutoff j) ∧
      (∀ k ∈ J,
        delta * (X.card : ℝ) <
          DyadicCells.occupancy X (gridIndex mesh) k) ∧
      (∀ k ∈ J,
        cutoff * 2 ^ j ≤ DyadicCells.occupancy X (gridIndex mesh) k ∧
          DyadicCells.occupancy X (gridIndex mesh) k < cutoff * 2 ^ (j + 1)) ∧
      J.card * (cutoff * 2 ^ j) ≤
        shellWeight (candidateGridIndices d mesh)
          (DyadicCells.occupancy X (gridIndex mesh)) cutoff j ∧
      shellWeight (candidateGridIndices d mesh)
          (DyadicCells.occupancy X (gridIndex mesh)) cutoff j ≤
        (cutoff * 2 ^ (j + 1)) * J.card := by
  classical
  let cells := candidateGridIndices d mesh
  let weight := DyadicCells.occupancy X (gridIndex mesh)
  have hmaps : ∀ x ∈ X, gridIndex mesh x ∈ cells := by
    exact gridIndex_maps_finset_to_candidates hmesh X hXcube
  obtain ⟨j, hj, hglobal, _hmass, _hdivNat, _hdivReal,
      hpointwise, hlower, hupperMass, _hcard⟩ :=
    exists_relative_occupancy_shell_after_discard X cells
      (gridIndex mesh) cutoff L hmaps hcutoff hupper
  let J := relativeShell cells weight cutoff j
  have hdiscard' : cells.card * cutoff ≤ X.card / 2 := by
    simpa only [cells] using hdiscard
  have hglobal' : X.card ≤ cells.card * cutoff +
      (L + 1) * shellWeight cells weight cutoff j := by
    simpa only [cells, weight] using hglobal
  have hhalfMass : X.card / 2 ≤ (L + 1) * shellWeight cells weight cutoff j := by
    omega
  have htwiceMass : X.card ≤
      2 * ((L + 1) * shellWeight cells weight cutoff j) := by
    omega
  have hmassPos : 0 < shellWeight cells weight cutoff j := by
    by_contra hzero
    have hz : shellWeight cells weight cutoff j = 0 := Nat.eq_zero_of_not_pos hzero
    rw [hz, mul_zero, add_zero] at hglobal'
    have hcardPos : 0 < X.card := Finset.card_pos.mpr hXne
    omega
  have hJne : J.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hJempty
    have : shellWeight cells weight cutoff j = 0 := by
      simp [shellWeight, J, hJempty]
    omega
  refine ⟨j, hj, hJne, hhalfMass, htwiceMass, ?_, hpointwise, hlower, hupperMass⟩
  intro k hk
  apply hheavy
  calc
    cutoff = cutoff * 1 := by omega
    _ ≤ cutoff * 2 ^ j := by
      exact Nat.mul_le_mul_left cutoff (by simpa using Nat.one_le_pow' j 1)
    _ ≤ DyadicCells.occupancy X (gridIndex mesh) k := (hpointwise k hk).1

end
end Erdos186.PZ.ConvexDensity
