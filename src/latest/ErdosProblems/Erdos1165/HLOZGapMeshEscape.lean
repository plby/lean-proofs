/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos1165.HLOZGapGuardedPointReturn
import ErdosProblems.Erdos1165.HLOZUpperEstimates

/-!
# A uniform point-before-return bound on one HLOZ spatial mesh cell

This file turns the exact logarithmic bound from `PointBeforeReturn` into a
deterministic escape chance depending only on the HLOZ mesh index.  It also
records the missing reverse comparison between Euclidean and Manhattan
distance on the integer lattice.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace Erdos1165.HLOZGapMeshEscape

open HLOZPathEvents PointBeforeReturn PotentialKernel

noncomputable section

/-- A proper value returned by `gapScaleOf` supplies its defining radial
upper bound. -/
theorem latticeDistance_le_meshRadius_of_gapScaleOf_eq
    {m : ℕ} {x y : Point} {a : GapScale}
    (ha : a ∈ properGapMesh) (hscale : gapScaleOf m x y = a) :
    latticeDistance x y ≤ meshRadius m a := by
  have hproper : HasProperGapScale m x y := by
    by_contra hnot
    have hoverflow := (gapScaleOf_eq_overflow_iff m x y).2 hnot
    have haNe : a ≠ overflowScale := by
      simpa only [properGapMesh, Finset.mem_erase, Finset.mem_univ,
        and_true] using ha
    exact haNe (hscale.symm.trans hoverflow)
  have hspec := (Nat.find_spec hproper).2
  unfold gapScaleOf at hscale
  rw [dif_pos hproper] at hscale
  have hval : Nat.find hproper = a := congrArg Fin.val hscale
  simpa only [hval] using hspec

/-- On the square lattice, the Manhattan norm is at most twice the ceiling
of the Euclidean norm.  The factor two is deliberately elementary and avoids
introducing a square-root constant into the later logarithm. -/
theorem manhattanNorm_sub_le_two_ceil_latticeDistance (x y : Point) :
    manhattanNorm (x - y) ≤ 2 * Nat.ceil (latticeDistance x y) := by
  let u : ℝ := ((x.1 - y.1 : ℤ) : ℝ)
  let v : ℝ := ((x.2 - y.2 : ℤ) : ℝ)
  let r : ℝ := Real.sqrt (u ^ 2 + v ^ 2)
  have huv : 0 ≤ u ^ 2 + v ^ 2 := by positivity
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrSq : r ^ 2 = u ^ 2 + v ^ 2 := by
    dsimp only [r]
    exact Real.sq_sqrt huv
  have hu : |u| ≤ r := by
    nlinarith [sq_nonneg v, sq_abs u, abs_nonneg u]
  have hv : |v| ≤ r := by
    nlinarith [sq_nonneg u, sq_abs v, abs_nonneg v]
  have hcastU : (((x.1 - y.1 : ℤ).natAbs : ℕ) : ℝ) = |u| := by
    simp [u]
  have hcastV : (((x.2 - y.2 : ℤ).natAbs : ℕ) : ℝ) = |v| := by
    simp [v]
  have hur : (((x.1 - y.1 : ℤ).natAbs : ℕ) : ℝ) ≤ r := by
    rw [hcastU]
    exact hu
  have hvr : (((x.2 - y.2 : ℤ).natAbs : ℕ) : ℝ) ≤ r := by
    rw [hcastV]
    exact hv
  have hceil : r ≤ (Nat.ceil r : ℝ) := Nat.le_ceil r
  have huceil : (x.1 - y.1 : ℤ).natAbs ≤ Nat.ceil r := by
    exact_mod_cast hur.trans hceil
  have hvceil : (x.2 - y.2 : ℤ).natAbs ≤ Nat.ceil r := by
    exact_mod_cast hvr.trans hceil
  change (x.1 - y.1 : ℤ).natAbs + (x.2 - y.2 : ℤ).natAbs ≤
    2 * Nat.ceil (latticeDistance x y)
  have hr : r = latticeDistance x y := by
    simp only [r, u, v, latticeDistance]
  rw [← hr]
  omega

/-- A natural logarithmic scale which dominates
`pointBeforeReturnLogScale (x-y)` throughout mesh cell `a`. -/
def meshPointBeforeReturnLogScale (m : ℕ) (a : GapScale) : ℕ :=
  24 * (4 * Nat.ceil (meshRadius m a) + 3) ^ 3

lemma meshPointBeforeReturnLogScale_pos (m : ℕ) (a : GapScale) :
    0 < meshPointBeforeReturnLogScale m a := by
  unfold meshPointBeforeReturnLogScale
  positivity

/-- The deterministic escape chance assigned to mesh cell `a`. -/
def meshPointEscapeChance (m : ℕ) (a : GapScale) : ℝ :=
  1 / (4 + 2 * Real.log (meshPointBeforeReturnLogScale m a : ℝ))

lemma pointBeforeReturnLogScale_le_meshPointBeforeReturnLogScale
    {m : ℕ} {x y : Point} {a : GapScale}
    (ha : a ∈ properGapMesh) (hscale : gapScaleOf m x y = a) :
    pointBeforeReturnLogScale (x - y) ≤
      meshPointBeforeReturnLogScale m a := by
  have hdist := latticeDistance_le_meshRadius_of_gapScaleOf_eq ha hscale
  have hceil : Nat.ceil (latticeDistance x y) ≤
      Nat.ceil (meshRadius m a) := Nat.ceil_mono hdist
  have hnorm : manhattanNorm (x - y) ≤
      2 * Nat.ceil (meshRadius m a) :=
    (manhattanNorm_sub_le_two_ceil_latticeDistance x y).trans
      (Nat.mul_le_mul_left 2 hceil)
  unfold pointBeforeReturnLogScale meshPointBeforeReturnLogScale
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  omega

lemma meshPointEscapeChance_pos (m : ℕ) (a : GapScale) :
    0 < meshPointEscapeChance m a := by
  unfold meshPointEscapeChance
  have hscale : (1 : ℝ) ≤ meshPointBeforeReturnLogScale m a := by
    exact_mod_cast (meshPointBeforeReturnLogScale_pos m a)
  have hlog : 0 ≤ Real.log (meshPointBeforeReturnLogScale m a : ℝ) :=
    Real.log_nonneg hscale
  positivity

lemma meshPointEscapeChance_le_one (m : ℕ) (a : GapScale) :
    meshPointEscapeChance m a ≤ 1 := by
  unfold meshPointEscapeChance
  have hscale : (1 : ℝ) ≤ meshPointBeforeReturnLogScale m a := by
    exact_mod_cast (meshPointBeforeReturnLogScale_pos m a)
  have hlog : 0 ≤ Real.log (meshPointBeforeReturnLogScale m a : ℝ) :=
    Real.log_nonneg hscale
  calc
    1 / (4 + 2 * Real.log (meshPointBeforeReturnLogScale m a : ℝ)) ≤
        1 / (1 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num)
        (by linarith : (1 : ℝ) ≤
          4 + 2 * Real.log (meshPointBeforeReturnLogScale m a : ℝ))
    _ = 1 := by norm_num

/-- Uniform sharp escape lower bound on a proper HLOZ mesh cell. -/
theorem meshPointEscapeChance_le_pointBeforeReturnProbability
    {m : ℕ} {x y : Point} {a : GapScale}
    (ha : a ∈ properGapMesh) (hscale : gapScaleOf m x y = a)
    (hxy : x ≠ y) :
    meshPointEscapeChance m a ≤ pointBeforeReturnProbability (x - y) := by
  have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hlogScale :=
    pointBeforeReturnLogScale_le_meshPointBeforeReturnLogScale ha hscale
  have hactualPos : (0 : ℝ) < pointBeforeReturnLogScale (x - y) := by
    exact_mod_cast pointBeforeReturnLogScale_pos (x - y)
  have huniformPos : (0 : ℝ) < meshPointBeforeReturnLogScale m a := by
    exact_mod_cast meshPointBeforeReturnLogScale_pos m a
  have hlog : Real.log (pointBeforeReturnLogScale (x - y) : ℝ) ≤
      Real.log (meshPointBeforeReturnLogScale m a : ℝ) :=
    Real.log_le_log hactualPos (by exact_mod_cast hlogScale)
  calc
    meshPointEscapeChance m a ≤
        1 / (4 + 2 * Real.log (pointBeforeReturnLogScale (x - y) : ℝ)) := by
      unfold meshPointEscapeChance
      apply one_div_le_one_div_of_le
      · have : 0 ≤ Real.log (pointBeforeReturnLogScale (x - y) : ℝ) :=
          Real.log_nonneg (by exact_mod_cast pointBeforeReturnLogScale_pos (x - y))
        linarith
      · linarith
    _ ≤ pointBeforeReturnProbability (x - y) :=
      pointBeforeReturnProbability_lower_log hne

end

end Erdos1165.HLOZGapMeshEscape
