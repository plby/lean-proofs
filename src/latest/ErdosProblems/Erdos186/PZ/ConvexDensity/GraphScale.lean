/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.BranchNumerics

/-!
# The integral graph-grid scale

The numerical part of the Pham--Zakharov argument is naturally written with
the real scale `delta ^ (-3 / (10 * (d + 1)))`, whereas the graph partition
uses a positive natural number of intervals.  This file fixes that mismatch
once and for all by taking the ceiling.  It also packages the two lower bounds
on the integral scale needed by the finite-cap and graph-window steps.
-/

open Filter Set
open scoped Topology

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false

noncomputable section

/-- The number of intervals in the second, boundary-graph grid. -/
def graphGridSize (d : ℕ) (delta : ℝ) : ℕ :=
  Nat.ceil (realGridScale d delta)

/-- The real PZ scale is bounded by its integral realization. -/
theorem realGridScale_le_graphGridSize_cast (d : ℕ) (delta : ℝ) :
    realGridScale d delta ≤ (graphGridSize d delta : ℝ) := by
  exact Nat.le_ceil _

/-- On the small-parameter range, rounding the graph scale costs at most a
factor of two. -/
theorem graphGridSize_cast_le_two_mul_realGridScale (d : ℕ)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1) :
    (graphGridSize d delta : ℝ) ≤ 2 * realGridScale d delta := by
  exact Nat.ceil_le_two_mul
    ((by norm_num : (2 : ℝ)⁻¹ ≤ 1).trans
      (one_le_realGridScale d hdelta hdelta_one))

/-- The rounded graph scale is positive throughout the small-parameter
range. -/
theorem graphGridSize_pos (d : ℕ) {delta : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1) :
    0 < graphGridSize d delta := by
  exact Nat.ceil_pos.mpr (realGridScale_pos d hdelta)

/-- The real graph scale diverges as `delta` tends to zero from the right. -/
theorem tendsto_realGridScale_nhdsGT_zero (d : ℕ) :
    Tendsto (realGridScale d) (𝓝[>] (0 : ℝ)) atTop := by
  have hrate : -gridRate d < 0 := by
    have := gridRate_pos d
    linarith
  change Tendsto (fun delta : ℝ ↦ delta ^ (-gridRate d))
    (𝓝[>] (0 : ℝ)) atTop
  exact tendsto_rpow_neg_nhdsGT_zero hrate

/-- Any fixed real threshold is eventually below the integral graph scale. -/
theorem exists_deltaZero_graphGridSize_ge (d : ℕ) (M : ℝ) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero < 1 ∧
      ∀ delta : ℝ, 0 < delta → delta < deltaZero →
        M ≤ (graphGridSize d delta : ℝ) := by
  have H : ∀ᶠ delta : ℝ in 𝓝[>] (0 : ℝ),
      M ≤ realGridScale d delta :=
    (tendsto_realGridScale_nhdsGT_zero d).eventually
      (eventually_ge_atTop M)
  obtain ⟨r, hr, hrH⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp H
  refine ⟨min r (1 / 2), by positivity, by
    calc
      min r (1 / 2) ≤ 1 / 2 := min_le_right _ _
      _ < 1 := by norm_num, ?_⟩
  intro delta hdelta hdeltaCutoff
  exact (hrH ⟨hdelta, hdeltaCutoff.trans_le (min_le_left _ _)⟩).trans
    (realGridScale_le_graphGridSize_cast d delta)

/-- A convenient physical half-width for the upper-boundary graph. -/
def graphWindowRadius (n : ℕ) (inner : ℝ) : ℝ :=
  inner / (4 * Real.sqrt n)

theorem graphWindowRadius_pos {n : ℕ} (hn : 0 < n)
    {inner : ℝ} (hinner : 0 < inner) :
    0 < graphWindowRadius n inner := by
  simp only [graphWindowRadius]
  positivity

/-- The expanded normalized box maps inside the standard inscribed graph
window for this choice of physical half-width. -/
theorem two_mul_graphWindowRadius_le {n : ℕ} (hn : 0 < n)
    {inner : ℝ} (hinner : 0 ≤ inner) :
    2 * graphWindowRadius n inner ≤ inner / Real.sqrt n := by
  have hsqrt : 0 < Real.sqrt (n : ℝ) := by positivity
  rw [graphWindowRadius]
  have heq : 2 * (inner / (4 * Real.sqrt (n : ℝ))) =
      (inner / 2) / Real.sqrt (n : ℝ) := by
    field_simp [hsqrt.ne']
    ring
  rw [heq, div_le_div_iff_of_pos_right hsqrt]
  linarith

/-- One small-parameter cutoff makes the rounded grid sufficiently fine for
both the finite cap and the upper-boundary graph chart. -/
theorem exists_deltaZero_graphGrid_cap_window
    (d n : ℕ) {inner outer : ℝ}
    (hn : 0 < n) (hinner : 0 < inner) (houter : 0 ≤ outer) :
    ∃ deltaZero : ℝ, 0 < deltaZero ∧ deltaZero < 1 ∧
      ∀ delta : ℝ, 0 < delta → delta < deltaZero →
        0 < graphGridSize d delta ∧
        4 * Real.sqrt n ≤ (graphGridSize d delta : ℝ) ∧
        outer * (2 * Real.sqrt n / (graphGridSize d delta : ℝ)) < inner := by
  let A : ℝ := outer * (2 * Real.sqrt n)
  let M : ℝ := max (4 * Real.sqrt n) (A / inner + 1)
  obtain ⟨deltaZero, hdeltaZero, hdeltaZeroOne, hscale⟩ :=
    exists_deltaZero_graphGridSize_ge d M
  refine ⟨deltaZero, hdeltaZero, hdeltaZeroOne, ?_⟩
  intro delta hdelta hdeltaCutoff
  have hdeltaOne : delta ≤ 1 :=
    hdeltaCutoff.le.trans hdeltaZeroOne.le
  have hmNat : 0 < graphGridSize d delta :=
    graphGridSize_pos d hdelta hdeltaOne
  have hm : 0 < (graphGridSize d delta : ℝ) := by exact_mod_cast hmNat
  have hM := hscale delta hdelta hdeltaCutoff
  have hcap : 4 * Real.sqrt n ≤ (graphGridSize d delta : ℝ) :=
    (le_max_left _ _).trans hM
  have hratio : A / inner < (graphGridSize d delta : ℝ) := by
    have := (le_max_right (4 * Real.sqrt n) (A / inner + 1)).trans hM
    linarith
  have hA : A < inner * (graphGridSize d delta : ℝ) :=
    by simpa [mul_comm] using (div_lt_iff₀ hinner).mp hratio
  refine ⟨hmNat, hcap, ?_⟩
  have hdiv : A / (graphGridSize d delta : ℝ) < inner := by
    exact (div_lt_iff₀ hm).2 (by simpa [mul_comm] using hA)
  calc
    outer * (2 * Real.sqrt n / (graphGridSize d delta : ℝ)) =
        A / (graphGridSize d delta : ℝ) := by
      dsimp only [A]
      ring
    _ < inner := hdiv

end

end Erdos186.PZ.ConvexDensity
