/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.BombieriVaaler

/-!
# Weighted integral kernel vectors

This is the column-scaled consequence of Bombieri--Vaaler used for
progression step matrices.  If the `j`th coefficient is allowed a range
proportional to a positive integer weight `w j`, scale the `j`th column by
`w j`, apply the unweighted theorem, and scale the resulting coefficient
back.  The output is a relation for the original matrix with the desired
coordinatewise weighted bound.
-/

namespace Erdos186.CFP.Bilu.WeightedKernel

open scoped BigOperators
open Erdos186.CFP.Bilu.BombieriVaaler

variable {r n d : ℕ}

/-- Scale column `j` of an integral matrix by the positive integer weight
`w j`. -/
def scaleColumns (A : Matrix (Fin r) (Fin n) ℤ) (w : Fin n → ℕ) :
    Matrix (Fin r) (Fin n) ℤ :=
  fun i j ↦ A i j * (w j : ℤ)

@[simp]
theorem scaleColumns_apply (A : Matrix (Fin r) (Fin n) ℤ)
    (w : Fin n → ℕ) (i : Fin r) (j : Fin n) :
    scaleColumns A w i j = A i j * (w j : ℤ) := rfl

/-- Scale an integral coefficient vector by the same coordinate weights. -/
def scaleVector (w : Fin n → ℕ) (y : Fin n → ℤ) : Fin n → ℤ :=
  fun j ↦ (w j : ℤ) * y j

@[simp]
theorem scaleVector_apply (w : Fin n → ℕ) (y : Fin n → ℤ) (j : Fin n) :
    scaleVector w y j = (w j : ℤ) * y j := rfl

/-- Column scaling commutes with matrix-vector multiplication. -/
theorem mulVec_scaleColumns (A : Matrix (Fin r) (Fin n) ℤ)
    (w : Fin n → ℕ) (y : Fin n → ℤ) :
    Matrix.mulVec (scaleColumns A w) y = Matrix.mulVec A (scaleVector w y) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, scaleColumns_apply, scaleVector_apply]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Positive coordinate weights preserve nonzeroness. -/
theorem scaleVector_ne_zero {w : Fin n → ℕ} (hw : ∀ j, 0 < w j)
    {y : Fin n → ℤ} (hy : y ≠ 0) : scaleVector w y ≠ 0 := by
  intro hzero
  apply hy
  funext j
  have hj := congrFun hzero j
  simp only [scaleVector_apply, Pi.zero_apply] at hj
  exact (mul_eq_zero.mp hj).resolve_left (by exact_mod_cast (hw j).ne')

/-- Absolute-value identity for a coordinate of a scaled vector. -/
theorem abs_scaleVector_cast (w : Fin n → ℕ) (y : Fin n → ℤ) (j : Fin n) :
    ((|scaleVector w y j| : ℤ) : ℝ) =
      (w j : ℝ) * ((|y j| : ℤ) : ℝ) := by
  simp [scaleVector, abs_mul]

/-- **Weighted Bombieri--Vaaler kernel theorem.**

The selected nonsingular minor and unused coordinate refer to the
column-scaled matrix.  The returned nonzero integral vector is killed by
the original matrix, and coordinate `j` is bounded by `w j` times the row
covolume of the scaled matrix. -/
theorem exists_ne_zero_mulVec_eq_zero_abs_cast_le_weight_mul_rowCovolume
    (A : Matrix (Fin r) (Fin n) ℤ) (w : Fin n → ℕ)
    (hw : ∀ j, 0 < w j)
    (f : Fin r → Fin n) (hf : Function.Injective f)
    (j₀ : Fin n) (hj₀ : j₀ ∉ Set.range f)
    (hdet : (coordinateMinor (scaleColumns A w) f).det ≠ 0) :
    ∃ a : Fin n → ℤ, a ≠ 0 ∧ Matrix.mulVec A a = 0 ∧
      ∀ j, ((|a j| : ℤ) : ℝ) ≤
        (w j : ℝ) * rowCovolume (scaleColumns A w) := by
  obtain ⟨y, hy0, hyker, hybound⟩ :=
    exists_ne_zero_mulVec_eq_zero_abs_cast_le_rowCovolume
      (scaleColumns A w) f hf j₀ hj₀ hdet
  refine ⟨scaleVector w y, scaleVector_ne_zero hw hy0, ?_, ?_⟩
  · rw [← mulVec_scaleColumns, hyker]
  · intro j
    rw [abs_scaleVector_cast]
    exact mul_le_mul_of_nonneg_left (hybound j) (Nat.cast_nonneg (w j))

/-- Square-root-of-Gram version of the weighted kernel theorem. -/
theorem exists_ne_zero_mulVec_eq_zero_abs_cast_le_weight_mul_sqrt_det_gram
    (A : Matrix (Fin r) (Fin n) ℤ) (w : Fin n → ℕ)
    (hw : ∀ j, 0 < w j)
    (f : Fin r → Fin n) (hf : Function.Injective f)
    (j₀ : Fin n) (hj₀ : j₀ ∉ Set.range f)
    (hdet : (coordinateMinor (scaleColumns A w) f).det ≠ 0) :
    ∃ a : Fin n → ℤ, a ≠ 0 ∧ Matrix.mulVec A a = 0 ∧
      ∀ j, ((|a j| : ℤ) : ℝ) ≤ (w j : ℝ) *
        Real.sqrt (Matrix.gram ℝ (realRow (scaleColumns A w))).det := by
  simpa [rowCovolume_eq_sqrt_det_gram] using
    exists_ne_zero_mulVec_eq_zero_abs_cast_le_weight_mul_rowCovolume
      A w hw f hf j₀ hj₀ hdet

/-- Matrix multiplication by the transpose is row-relation (`vecMul`)
multiplication. -/
theorem transpose_mulVec_eq_vecMul (M : Matrix (Fin n) (Fin d) ℤ)
    (a : Fin n → ℤ) :
    Matrix.mulVec M.transpose a = Matrix.vecMul a M := by
  funext j
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Weighted row-relation form, directly matching a progression step
matrix. -/
theorem exists_ne_zero_vecMul_eq_zero_abs_cast_le_weight_mul_rowCovolume
    (M : Matrix (Fin n) (Fin r) ℤ) (w : Fin n → ℕ)
    (hw : ∀ j, 0 < w j)
    (f : Fin r → Fin n) (hf : Function.Injective f)
    (j₀ : Fin n) (hj₀ : j₀ ∉ Set.range f)
    (hdet : (coordinateMinor (scaleColumns M.transpose w) f).det ≠ 0) :
    ∃ a : Fin n → ℤ, a ≠ 0 ∧ Matrix.vecMul a M = 0 ∧
      ∀ j, ((|a j| : ℤ) : ℝ) ≤
        (w j : ℝ) * rowCovolume (scaleColumns M.transpose w) := by
  obtain ⟨a, ha0, haker, habound⟩ :=
    exists_ne_zero_mulVec_eq_zero_abs_cast_le_weight_mul_rowCovolume
      M.transpose w hw f hf j₀ hj₀ hdet
  exact ⟨a, ha0, by simpa only [transpose_mulVec_eq_vecMul] using haker, habound⟩

/-- If the row covolume of the scaled transpose is at most the natural
dilation parameter `k`, the weighted kernel vector lies strictly inside
the corresponding integral coefficient box.  The final `+ 1` is the
integer rounding step used to contradict properness of a dilated
progression. -/
theorem exists_ne_zero_vecMul_eq_zero_abs_lt_weight_mul_add_one
    (M : Matrix (Fin n) (Fin r) ℤ) (w : Fin n → ℕ)
    (hw : ∀ j, 0 < w j) (k : ℕ)
    (f : Fin r → Fin n) (hf : Function.Injective f)
    (j₀ : Fin n) (hj₀ : j₀ ∉ Set.range f)
    (hdet : (coordinateMinor (scaleColumns M.transpose w) f).det ≠ 0)
    (hcov : rowCovolume (scaleColumns M.transpose w) ≤ (k : ℝ)) :
    ∃ a : Fin n → ℤ, a ≠ 0 ∧ Matrix.vecMul a M = 0 ∧
      ∀ j, |a j| < ((w j * k + 1 : ℕ) : ℤ) := by
  obtain ⟨a, ha0, haker, habound⟩ :=
    exists_ne_zero_vecMul_eq_zero_abs_cast_le_weight_mul_rowCovolume
      M w hw f hf j₀ hj₀ hdet
  refine ⟨a, ha0, haker, ?_⟩
  intro j
  have hreal : ((|a j| : ℤ) : ℝ) ≤ (w j : ℝ) * (k : ℝ) :=
    (habound j).trans
      (mul_le_mul_of_nonneg_left hcov (Nat.cast_nonneg (w j)))
  have hint : (|a j| : ℤ) ≤ ((w j * k : ℕ) : ℤ) := by
    exact_mod_cast hreal
  omega

end Erdos186.CFP.Bilu.WeightedKernel

#print axioms Erdos186.CFP.Bilu.WeightedKernel.exists_ne_zero_vecMul_eq_zero_abs_cast_le_weight_mul_rowCovolume
#print axioms Erdos186.CFP.Bilu.WeightedKernel.exists_ne_zero_vecMul_eq_zero_abs_lt_weight_mul_add_one
