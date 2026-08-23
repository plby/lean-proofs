/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceAlgebraicUniformBounds

/-!
# Static factors in the source-faithful algebraic majorant

The two support-cardinality factors and the Siegel coefficient height are
independent of the contour.  Together they consume only two thirds of the
standard source height unit.  Keeping this estimate separate lets the
integral, rational, and coprime contour arguments share it.
-/

noncomputable section

namespace Erdos240.BakerSourceAlgebraicStaticFactors

open Erdos240
open BakerLemma2Concrete
open BakerSourceMajorantClosedForm

/-- The initial support box consumes one sixth of the source height. -/
theorem initialSupportBound_le_exp_sixth {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements) :
    (initialSupportBound P : ℝ) ≤
      Real.exp ((1 / 6 : ℝ) * (P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld) := by
  simpa only [initialSupportBound] using
    initial_unknownCount_le_exp_heightScale P hreq

/-- The coefficient height is definitionally one third of the source
height unit. -/
theorem coeffHeight_eq_exp_third {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) :
    P.coeffHeight =
      Real.exp ((1 / 3 : ℝ) * (P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld) := by
  rfl

/-- Both support factors together with the coefficient height consume at
most two thirds of the source height unit. -/
theorem support_sq_mul_coeffHeight_le_exp_two_thirds {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements) :
    (initialSupportBound P : ℝ) *
        (P.coeffHeight * (initialSupportBound P : ℝ)) ≤
      Real.exp ((2 / 3 : ℝ) * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld)) := by
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  have hs : (initialSupportBound P : ℝ) ≤ Real.exp (H / 6) := by
    convert initialSupportBound_le_exp_sixth P hreq using 1
    congr 1
    dsimp only [H]
    ring
  have hc : P.coeffHeight = Real.exp (H / 3) := by
    rw [coeffHeight_eq_exp_third]
    dsimp only [H]
    congr 1
    ring
  have hinner :
      P.coeffHeight * (initialSupportBound P : ℝ) ≤
        Real.exp (H / 3) * Real.exp (H / 6) := by
    rw [hc]
    exact mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
  calc
    (initialSupportBound P : ℝ) *
        (P.coeffHeight * (initialSupportBound P : ℝ)) ≤
      Real.exp (H / 6) *
        (Real.exp (H / 3) * Real.exp (H / 6)) := by
      exact mul_le_mul hs hinner
        (mul_nonneg P.coeffHeight_pos.le (Nat.cast_nonneg _))
        (Real.exp_pos _).le
    _ = Real.exp ((2 / 3 : ℝ) * H) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos240.BakerSourceAlgebraicStaticFactors

#print axioms
  Erdos240.BakerSourceAlgebraicStaticFactors.initialSupportBound_le_exp_sixth
#print axioms
  Erdos240.BakerSourceAlgebraicStaticFactors.support_sq_mul_coeffHeight_le_exp_two_thirds
