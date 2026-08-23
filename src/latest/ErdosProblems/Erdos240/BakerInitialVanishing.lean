/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerAuxiliary
import ErdosProblems.Erdos240.BakerLemma3

/-!
# From the Lemma 2 equations to initial auxiliary-function vanishing

This module identifies the corrected rational row coefficient in
`BakerAuxiliary` with the level-zero algebraic auxiliary function in
`BakerLemma3`.  It is the first concrete constructor layer needed by the
source induction.
-/

open scoped BigOperators Polynomial

noncomputable section

namespace Erdos240.BakerInitialVanishing

open Finset
open Erdos240
open Erdos240.BakerAuxiliary
open Erdos240.BakerLemma3

attribute [local instance] Matrix.seminormedAddCommGroup

/-- Canonical source-coordinate projections on the Lemma 2 coefficient box. -/
def lambdaBoxCoordinates {oldRank : ℕ} {L : BoxShape oldRank} :
    SourceCoordinates oldRank (LambdaBox L) where
  shift := LambdaBox.shift
  deltaIndex := LambdaBox.deltaIndex
  oldExponent := LambdaBox.oldExponent
  lastExponent := LambdaBox.lastExponent

/-- Turn the source row's distinguished derivative coordinate and old
coordinates into the canonical `Fin (oldRank+1)` multi-index. -/
def rowMultiIndex {oldRank radius budget : ℕ}
    (row : ConstraintRow oldRank radius budget) :
    VDPLMultiIndex (oldRank + 1) :=
  Fin.cases (row.order none) (fun r ↦ row.order (some r))

@[simp] theorem rowMultiIndex_zero {oldRank radius budget : ℕ}
    (row : ConstraintRow oldRank radius budget) :
    rowMultiIndex row 0 = row.order none := rfl

@[simp] theorem rowMultiIndex_succ {oldRank radius budget : ℕ}
    (row : ConstraintRow oldRank radius budget) (r : Fin oldRank) :
    rowMultiIndex row r.succ = row.order (some r) := rfl

theorem rowMultiIndex_weight {oldRank radius budget : ℕ}
    (row : ConstraintRow oldRank radius budget) :
    VDPLMultiIndex.weight (rowMultiIndex row) = row.weight := by
  simp [VDPLMultiIndex.weight, ConstraintRow.weight, rowMultiIndex,
    Fin.sum_univ_succ]

theorem rowMultiIndex_weight_le {oldRank radius budget : ℕ}
    (row : ConstraintRow oldRank radius budget) :
    VDPLMultiIndex.weight (rowMultiIndex row) ≤ budget := by
  rw [rowMultiIndex_weight]
  exact row.weight_le

/-- Positive integral bases turn the complex exponential in `g` into the
literal source power at integral points. -/
theorem exp_nat_log_mul_eq_pow (a e l : ℕ) (ha : 0 < a) :
    Complex.exp ((e : ℂ) * (Real.log (a : ℝ) : ℂ) * (l : ℂ)) =
      (a : ℂ) ^ (e * l) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  calc
    Complex.exp ((e : ℂ) * (Real.log (a : ℝ) : ℂ) * (l : ℂ)) =
        Complex.exp (((e * l : ℕ) : ℂ) * (Real.log (a : ℝ) : ℂ)) := by
      congr 1
      push_cast
      ring
    _ = Complex.exp (Real.log (a : ℝ) : ℂ) ^ (e * l) := by
      rw [Complex.exp_nat_mul]
    _ = (a : ℂ) ^ (e * l) := by
      rw [← Complex.ofReal_exp, Real.exp_log haR]
      norm_num

private theorem eval₂_eq_cast_eval_of_eq (p : ℚ[X]) (xC : ℂ) (xQ : ℚ)
    (hx : xC = (xQ : ℂ)) :
    Polynomial.eval₂ (algebraMap ℚ ℂ) xC p = ((p.eval xQ : ℚ) : ℂ) := by
  rw [hx]
  exact Polynomial.eval₂_at_apply _ _

/-- At an integral row point, the corrected Lemma 3 Delta factor is exactly
the complex cast of the corrected Lemma 2 rational Delta factor. -/
theorem auxiliaryFactor_at_row
    {oldRank radius budget : ℕ} {L : BoxShape oldRank}
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (row : ConstraintRow oldRank radius budget) (lambda : LambdaBox L) :
    auxiliaryFactor lambdaBoxCoordinates h b bLast lambda (row.point : ℂ)
        (rowMultiIndex row) =
      (sourceDeltaFactor h b bLast row lambda : ℂ) := by
  simp only [auxiliaryFactor, lambdaBoxCoordinates, rowMultiIndex_zero,
    rowMultiIndex_succ, sourceDeltaFactor, poweredDeltaHasseEval,
    LambdaBox.shift, LambdaBox.deltaIndex, LambdaBox.oldExponent,
    LambdaBox.lastExponent]
  push_cast
  congr 1
  · apply eval₂_eq_cast_eval_of_eq
    norm_num
  · apply Finset.prod_congr rfl
    intro r _
    apply eval₂_eq_cast_eval_of_eq
    norm_num

/-- At a natural integral point, the algebraic exponential rate is the
literal product of the source bases to the `lambda_i * l` powers. -/
theorem exp_algebraicRate_mul_nat_eq
    {oldRank : ℕ} {I : Type*} (coord : SourceCoordinates oldRank I)
    (alpha : Fin oldRank → ℕ) (alphaLast : ℕ)
    (halpha : ∀ r, 0 < alpha r) (halphaLast : 0 < alphaLast)
    (lambda : I) (l : ℕ) :
    Complex.exp
        (algebraicRate coord
          (fun r ↦ (Real.log (alpha r : ℝ) : ℂ))
          (Real.log (alphaLast : ℝ) : ℂ) lambda * (l : ℂ)) =
      ((∏ r, (alpha r : ℂ) ^ (coord.oldExponent lambda r * l)) *
        (alphaLast : ℂ) ^ (coord.lastExponent lambda * l)) := by
  rw [algebraicRate, add_mul, Complex.exp_add]
  rw [Finset.sum_mul, Complex.exp_sum]
  congr 1
  · apply Finset.prod_congr rfl
    intro r _
    simpa only [mul_assoc] using
      exp_nat_log_mul_eq_pow (alpha r) (coord.oldExponent lambda r) l (halpha r)
  · simpa only [mul_assoc] using
      exp_nat_log_mul_eq_pow alphaLast (coord.lastExponent lambda) l halphaLast

/-- The corrected Lemma 3 function at a Lemma 2 row is the complex cast of
the literal rational constraint sum. -/
theorem vdplG_at_row_eq_cast_constraintSum
    {oldRank radius budget : ℕ} {L : BoxShape oldRank}
    (p : LambdaBox L → ℤ) (h : ℕ)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (alpha : Fin oldRank → ℕ) (alphaLast : ℕ)
    (halpha : ∀ r, 0 < alpha r) (halphaLast : 0 < alphaLast)
    (row : ConstraintRow oldRank radius budget) :
    vdplG lambdaBoxCoordinates Finset.univ p h b bLast
        (fun r ↦ (Real.log (alpha r : ℝ) : ℂ))
        (Real.log (alphaLast : ℝ) : ℂ) 1 0 (row.point : ℂ)
        (rowMultiIndex row) =
      ((∑ lambda, (p lambda : ℚ) *
        rationalConstraintEntry h b bLast
          (fun r ↦ (alpha r : ℤ)) (alphaLast : ℤ) row lambda : ℚ) : ℂ) := by
  rw [vdplG_eq_sum]
  simp only [sourceCoefficient, scaledArgument, pow_zero, Nat.cast_one, div_one]
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro lambda _
  rw [auxiliaryFactor_at_row]
  rw [exp_algebraicRate_mul_nat_eq lambdaBoxCoordinates alpha alphaLast
    halpha halphaLast lambda row.point]
  simp only [rationalConstraintEntry]
  push_cast
  simp only [lambdaBoxCoordinates, Nat.mul_comm]
  ring

/-- Package an arbitrary allowed derivative multi-index as a Lemma 2 row
multi-index. -/
def boundedMultiIndexOf {oldRank budget : ℕ}
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ budget) :
    BoundedMultiIndex oldRank budget where
  coordinate
    | none => ⟨m 0, Nat.lt_succ_of_le
        ((VDPLMultiIndex.component_le_weight m 0).trans hm)⟩
    | some r => ⟨m r.succ, Nat.lt_succ_of_le
        ((VDPLMultiIndex.component_le_weight m r.succ).trans hm)⟩
  weight_le := by
    simpa [VDPLMultiIndex.weight, Fin.sum_univ_succ] using hm

/-- The source constraint row attached to an allowed integral point and
derivative multi-index. -/
def constraintRowOf {oldRank radius budget l : ℕ}
    (hl : 1 ≤ l) (hlR : l ≤ radius)
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ budget) :
    ConstraintRow oldRank radius budget where
  pointIndex := ⟨l - 1, by omega⟩
  multiIndex := boundedMultiIndexOf m hm

@[simp] theorem constraintRowOf_point {oldRank radius budget l : ℕ}
    (hl : 1 ≤ l) (hlR : l ≤ radius)
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ budget) :
    (constraintRowOf hl hlR m hm).point = l := by
  simp [constraintRowOf, ConstraintRow.point]
  omega

@[simp] theorem rowMultiIndex_constraintRowOf
    {oldRank radius budget l : ℕ}
    (hl : 1 ≤ l) (hlR : l ≤ radius)
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ budget) :
    rowMultiIndex (constraintRowOf hl hlR m hm) = m := by
  funext i
  refine Fin.cases ?_ (fun r ↦ ?_) i
  · rfl
  · rfl

/-- The corrected Lemma 2 row equations give initial integral-grid vanishing
of the corrected Lemma 3 algebraic auxiliary function. -/
theorem initialVanishesOn_of_constraintEquations
    {oldRank radius budget : ℕ} {L : BoxShape oldRank}
    (p : LambdaBox L → ℤ) (h : ℕ)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (alpha : Fin oldRank → ℕ) (alphaLast : ℕ)
    (halpha : ∀ r, 0 < alpha r) (halphaLast : 0 < alphaLast)
    (hequations : ∀ row : ConstraintRow oldRank radius budget,
      ∑ lambda, (p lambda : ℚ) *
        rationalConstraintEntry h b bLast
          (fun r ↦ (alpha r : ℤ)) (alphaLast : ℤ) row lambda = 0) :
    VanishesOn
      (vdplG lambdaBoxCoordinates Finset.univ p h b bLast
        (fun r ↦ (Real.log (alpha r : ℝ) : ℂ))
        (Real.log (alphaLast : ℝ) : ℂ) 1 0)
      1 radius budget := by
  intro l hl hlR m hm
  let row : ConstraintRow oldRank radius budget :=
    constraintRowOf hl hlR m hm
  have hvalue := vdplG_at_row_eq_cast_constraintSum p h b bLast
    alpha alphaLast halpha halphaLast row
  rw [hequations row] at hvalue
  have hzero :
      vdplG lambdaBoxCoordinates Finset.univ p h b bLast
        (fun r ↦ (Real.log (alpha r : ℝ) : ℂ))
        (Real.log (alphaLast : ℝ) : ℂ) 1 0 (row.point : ℂ)
        (rowMultiIndex row) = 0 := by
    simpa using hvalue
  simpa only [Nat.cast_one, div_one, row, constraintRowOf_point,
    rowMultiIndex_constraintRowOf] using hzero

/-- Direct constructor from an integral Lemma 2 matrix kernel vector to the
initial vanishing hypothesis consumed by the source induction. -/
theorem initialVanishesOn_of_mulVec_eq_zero
    {oldRank radius budget : ℕ} {L : BoxShape oldRank}
    {h : ℕ} {b : Fin oldRank → ℤ} {bLast : ℤ}
    {alpha : Fin oldRank → ℕ} {alphaLast : ℕ}
    (model : IntegralConstraintModel (radius := radius) (budget := budget)
      (L := L) h b bLast (fun r ↦ (alpha r : ℤ)) (alphaLast : ℤ))
    (p : LambdaBox L → ℤ) (hp : model.matrix.mulVec p = 0)
    (halpha : ∀ r, 0 < alpha r) (halphaLast : 0 < alphaLast) :
    VanishesOn
      (vdplG lambdaBoxCoordinates Finset.univ p h b bLast
        (fun r ↦ (Real.log (alpha r : ℝ) : ℂ))
        (Real.log (alphaLast : ℝ) : ℂ) 1 0)
      1 radius budget := by
  apply initialVanishesOn_of_constraintEquations p h b bLast alpha alphaLast
    halpha halphaLast
  exact rational_equations_of_mulVec_eq_zero model p hp

/-- Concrete Lemma 2 base constructor after the two remaining numerical
matrix estimates (dimension slack and height) have been supplied.  The sharp
integral model itself is constructed unconditionally from the corrected
source rows. -/
theorem exists_initialAuxiliary
    {oldRank radius budget : ℕ} {L : BoxShape oldRank}
    (h : ℕ) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (alpha : Fin oldRank → ℕ) (alphaLast : ℕ)
    (halpha : ∀ r, 0 < alpha r) (halphaLast : 0 < alphaLast)
    (heightScale : ℝ) (hscale : 0 ≤ heightScale)
    (hradius : 0 < radius)
    (hslack : 2 * Fintype.card (ConstraintRow oldRank radius budget) ≤
      Fintype.card (LambdaBox L))
    (hunknown : (Fintype.card (LambdaBox L) : ℝ) ≤ Real.exp heightScale)
    (hmatrix :
      ‖(IntegralConstraintModel.ofSourceData h b bLast
        (fun r ↦ (alpha r : ℤ)) (alphaLast : ℤ) :
          IntegralConstraintModel (radius := radius) (budget := budget)
            (L := L) h b bLast (fun r ↦ (alpha r : ℤ))
              (alphaLast : ℤ)).matrix‖ ≤ Real.exp heightScale) :
    ∃ p : LambdaBox L → ℤ, p ≠ 0 ∧
      VanishesOn
        (vdplG lambdaBoxCoordinates Finset.univ p h b bLast
          (fun r ↦ (Real.log (alpha r : ℝ) : ℂ))
          (Real.log (alphaLast : ℝ) : ℂ) 1 0)
        1 radius budget ∧
      ‖p‖ ≤ Real.exp (2 * heightScale) := by
  let model : IntegralConstraintModel (radius := radius) (budget := budget)
      (L := L) h b bLast (fun r ↦ (alpha r : ℤ)) (alphaLast : ℤ) :=
    IntegralConstraintModel.ofSourceData h b bLast
      (fun r ↦ (alpha r : ℤ)) (alphaLast : ℤ)
  obtain ⟨p, hpne, hequations, hpheight⟩ :=
    exists_vdpl_auxiliary_coefficients model heightScale hscale hradius
      hslack hunknown (by simpa only [model] using hmatrix)
  refine ⟨p, hpne, ?_, hpheight⟩
  exact initialVanishesOn_of_constraintEquations p h b bLast alpha alphaLast
    halpha halphaLast hequations

#print axioms Erdos240.BakerInitialVanishing.initialVanishesOn_of_mulVec_eq_zero
#print axioms Erdos240.BakerInitialVanishing.exists_initialAuxiliary

end Erdos240.BakerInitialVanishing
