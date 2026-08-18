/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Real.Basic

/-!
# The determinantal core of the Bombieri--Vaaler lemma

Bilu's proof of Freiman's theorem uses the following geometry-of-numbers
fact (Bilu, Lemma 6.10).  If `L` is a proper rational subspace of
`R^n` and `Gamma = L ∩ Z^n`, then `Lᵌ ∩ Z^n` contains a nonzero vector
whose sup norm is at most the determinant of `Gamma`.

This file proves the exact integer-linear-algebra core of that statement.
Given a full-rank integer row matrix, a nonsingular coordinate minor, and
one coordinate outside that minor, Cramer's rule constructs a nonzero
integer vector in the kernel.  Every coordinate of the vector is itself a
full-rank minor.  Consequently any common bound for the full-rank minors
is a sup-norm bound for the kernel vector.
-/

namespace Erdos186.CFP.Bilu.BombieriVaaler

open scoped BigOperators
open RealInnerProductSpace

variable {r n : ℕ}

/-- Replace the `i`th selected coordinate by the extra coordinate `j₀`. -/
def replaceCoordinate (f : Fin r → Fin n) (j₀ : Fin n) (i : Fin r) :
    Fin r → Fin n :=
  Function.update f i j₀

theorem replaceCoordinate_injective (f : Fin r → Fin n)
    (hf : Function.Injective f) (j₀ : Fin n)
    (hj₀ : j₀ ∉ Set.range f) (i : Fin r) :
    Function.Injective (replaceCoordinate f j₀ i) := by
  intro a b hab
  by_cases hai : a = i
  · subst a
    by_cases hbi : b = i
    · exact hbi.symm
    · have : j₀ = f b := by simpa [replaceCoordinate, hbi] using hab
      exact False.elim (hj₀ ⟨b, this.symm⟩)
  · by_cases hbi : b = i
    · subst b
      have : f a = j₀ := by simpa [replaceCoordinate, hai] using hab
      exact False.elim (hj₀ ⟨a, this⟩)
    · exact hf (by simpa [replaceCoordinate, hai, hbi] using hab)

/-- The square coordinate minor selected by `f`. -/
def coordinateMinor (A : Matrix (Fin r) (Fin n) ℤ)
    (f : Fin r → Fin n) : Matrix (Fin r) (Fin r) ℤ :=
  A.submatrix id f

@[simp]
theorem coordinateMinor_apply (A : Matrix (Fin r) (Fin n) ℤ)
    (f : Fin r → Fin n) (i k : Fin r) :
    coordinateMinor A f i k = A i (f k) := rfl

/-- The ambient integral vector supplied by Cramer's rule. -/
noncomputable def cramerKernelVector (A : Matrix (Fin r) (Fin n) ℤ)
    (f : Fin r → Fin n) (j₀ : Fin n) : Fin n → ℤ :=
  fun j ↦
    (if j = j₀ then (coordinateMinor A f).det else 0) -
      ∑ i : Fin r, if f i = j then
        Matrix.cramer (coordinateMinor A f) (fun a ↦ A a j₀) i else 0

@[simp]
theorem cramerKernelVector_extra (A : Matrix (Fin r) (Fin n) ℤ)
    (f : Fin r → Fin n) (j₀ : Fin n) (hj₀ : j₀ ∉ Set.range f) :
    cramerKernelVector A f j₀ j₀ = (coordinateMinor A f).det := by
  rw [cramerKernelVector]
  have hsum : (∑ i : Fin r, if f i = j₀ then
      Matrix.cramer (coordinateMinor A f) (fun a ↦ A a j₀) i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only [ite_eq_right_iff]
    exact fun h ↦ False.elim (hj₀ ⟨i, h⟩)
  rw [hsum, sub_zero]
  simp

@[simp]
theorem cramerKernelVector_selected (A : Matrix (Fin r) (Fin n) ℤ)
    (f : Fin r → Fin n) (hf : Function.Injective f)
    (j₀ : Fin n) (hj₀ : j₀ ∉ Set.range f) (i : Fin r) :
    cramerKernelVector A f j₀ (f i) =
      -Matrix.cramer (coordinateMinor A f) (fun a ↦ A a j₀) i := by
  rw [cramerKernelVector]
  simp only [if_neg (fun h ↦ hj₀ ⟨i, h⟩), zero_sub]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hbi
    simp [hf.eq_iff, hbi]
  · simp

theorem cramer_eq_replaced_minor (A : Matrix (Fin r) (Fin n) ℤ)
    (f : Fin r → Fin n) (j₀ : Fin n) (i : Fin r) :
    Matrix.cramer (coordinateMinor A f) (fun a ↦ A a j₀) i =
      (coordinateMinor A (replaceCoordinate f j₀ i)).det := by
  rw [Matrix.cramer_apply]
  congr 1
  ext a b
  by_cases hbi : b = i
  · subst b
    simp [coordinateMinor, replaceCoordinate]
  · simp [coordinateMinor, replaceCoordinate, hbi]

/-! ## Euclidean determinant and the minor bound -/

/-- The `i`th integer row, regarded as a vector in Euclidean space. -/
noncomputable def realRow (A : Matrix (Fin r) (Fin n) ℤ) (i : Fin r) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j ↦ (A i j : ℝ)

@[simp]
theorem realRow_apply (A : Matrix (Fin r) (Fin n) ℤ) (i : Fin r) (j : Fin n) :
    realRow A i j = (A i j : ℝ) := rfl

/-- The Euclidean covolume of the row parallelepiped.  This is the norm of
the exterior product, hence the square root of the Gram determinant. -/
noncomputable def rowCovolume (A : Matrix (Fin r) (Fin n) ℤ) : ℝ :=
  ‖exteriorPower.ιMulti ℝ r (realRow A)‖

theorem rowCovolume_nonneg (A : Matrix (Fin r) (Fin n) ℤ) :
    0 ≤ rowCovolume A := norm_nonneg _

/-- The square of the row covolume is the Gram determinant. -/
theorem rowCovolume_sq_eq_det_gram (A : Matrix (Fin r) (Fin n) ℤ) :
    rowCovolume A ^ 2 = (Matrix.gram ℝ (realRow A)).det := by
  rw [rowCovolume, ← real_inner_self_eq_norm_sq]
  exact exteriorPower.inner_ιMulti_self (realRow A)

/-- The row covolume is literally the nonnegative square root of the Gram
determinant. -/
theorem rowCovolume_eq_sqrt_det_gram (A : Matrix (Fin r) (Fin n) ℤ) :
    rowCovolume A = Real.sqrt (Matrix.gram ℝ (realRow A)).det := by
  rw [← rowCovolume_sq_eq_det_gram]
  exact (Real.sqrt_sq (rowCovolume_nonneg A)).symm

/-- Every full-rank coordinate minor is bounded by the Euclidean row
covolume.  This is the one-coefficient inequality in the Cauchy--Binet
identity, proved here from the inner-product structure on exterior powers. -/
theorem abs_coordinateMinor_cast_le_rowCovolume
    (A : Matrix (Fin r) (Fin n) ℤ) (g : Fin r → Fin n)
    (hg : Function.Injective g) :
    ((|(coordinateMinor A g).det| : ℤ) : ℝ) ≤ rowCovolume A := by
  let e : Fin r → EuclideanSpace ℝ (Fin n) :=
    fun i ↦ EuclideanSpace.single (g i) 1
  let u := exteriorPower.ιMulti ℝ r e
  let v := exteriorPower.ιMulti ℝ r (realRow A)
  have he : Orthonormal ℝ e :=
    EuclideanSpace.orthonormal_single.comp g hg
  have hgram : Matrix.gram ℝ e = 1 :=
    Matrix.gram_eq_one_iff_orthonormal.mpr he
  have hu_inner : ⟪u, u⟫ = (1 : ℝ) := by
    dsimp only [u]
    rw [exteriorPower.inner_ιMulti_self, hgram, Matrix.det_one]
  have hu_norm : ‖u‖ = 1 := by
    rw [real_inner_self_eq_norm_sq] at hu_inner
    nlinarith [norm_nonneg u]
  have huv : ⟪u, v⟫ = ((coordinateMinor A g).det : ℝ) := by
    dsimp only [u, v]
    rw [exteriorPower.inner_ιMulti_ιMulti]
    have hmatrix :
        (Matrix.of fun i j ↦ ⟪e j, realRow A i⟫) =
          (coordinateMinor A g).map (Int.castRingHom ℝ) := by
      ext i j
      simp [e, realRow, coordinateMinor, EuclideanSpace.inner_single_left]
    rw [hmatrix]
    exact ((Int.castRingHom ℝ).map_det (coordinateMinor A g)).symm
  have hcs := abs_real_inner_le_norm u v
  rw [huv, hu_norm, one_mul] at hcs
  simpa [rowCovolume, v, Int.cast_abs] using hcs

/-- The Cramer vector is orthogonal to every row of the original matrix. -/
theorem mulVec_cramerKernelVector (A : Matrix (Fin r) (Fin n) ℤ)
    (f : Fin r → Fin n) (j₀ : Fin n) :
    Matrix.mulVec A (cramerKernelVector A f j₀) = 0 := by
  funext a
  rw [Matrix.mulVec]
  change (∑ j : Fin n, A a j *
    ((if j = j₀ then (coordinateMinor A f).det else 0) -
      ∑ i : Fin r, if f i = j then
        Matrix.cramer (coordinateMinor A f) (fun b ↦ A b j₀) i else 0)) = 0
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hfirst :
      (∑ j : Fin n, A a j *
        (if j = j₀ then (coordinateMinor A f).det else 0)) =
      A a j₀ * (coordinateMinor A f).det := by
    simp
  rw [hfirst]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hselected (i : Fin r) :
      ∑ j : Fin n, A a j * (if f i = j then
          Matrix.cramer (coordinateMinor A f) (fun b ↦ A b j₀) i else 0) =
        A a (f i) * Matrix.cramer (coordinateMinor A f) (fun b ↦ A b j₀) i := by
    simp [eq_comm]
  simp_rw [hselected]
  have hcramer := congrFun
    (Matrix.mulVec_cramer (coordinateMinor A f) (fun b ↦ A b j₀)) a
  simp only [Matrix.mulVec, coordinateMinor_apply, Pi.smul_apply, smul_eq_mul] at hcramer
  change (∑ x : Fin r, A a (f x) *
    Matrix.cramer (coordinateMinor A f) (fun b ↦ A b j₀) x) =
      (coordinateMinor A f).det * A a j₀ at hcramer
  rw [hcramer]
  ring

/-- A nonsingular selected minor makes the Cramer kernel vector nonzero. -/
theorem cramerKernelVector_ne_zero (A : Matrix (Fin r) (Fin n) ℤ)
    (f : Fin r → Fin n) (j₀ : Fin n) (hj₀ : j₀ ∉ Set.range f)
    (hdet : (coordinateMinor A f).det ≠ 0) :
    cramerKernelVector A f j₀ ≠ 0 := by
  intro hzero
  have h := congrFun hzero j₀
  exact hdet (by simpa [cramerKernelVector_extra A f j₀ hj₀] using h)

/-- Exact determinantal form of the integer-kernel small-vector lemma. -/
theorem exists_ne_zero_mulVec_eq_zero_abs_le
    (A : Matrix (Fin r) (Fin n) ℤ)
    (f : Fin r → Fin n) (hf : Function.Injective f)
    (j₀ : Fin n) (hj₀ : j₀ ∉ Set.range f)
    (hdet : (coordinateMinor A f).det ≠ 0)
    (D : ℤ) (hminor : ∀ g : Fin r → Fin n,
      Function.Injective g → |(coordinateMinor A g).det| ≤ D) :
    ∃ x : Fin n → ℤ, x ≠ 0 ∧ Matrix.mulVec A x = 0 ∧ ∀ j, |x j| ≤ D := by
  refine ⟨cramerKernelVector A f j₀,
    cramerKernelVector_ne_zero A f j₀ hj₀ hdet,
    mulVec_cramerKernelVector A f j₀, ?_⟩
  intro j
  by_cases hj : j = j₀
  · subst j
    rw [cramerKernelVector_extra A f j₀ hj₀]
    exact hminor f hf
  · by_cases hjf : j ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hjf
      rw [cramerKernelVector_selected A f hf j₀ hj₀ i,
        abs_neg, cramer_eq_replaced_minor]
      exact hminor _ (replaceCoordinate_injective f hf j₀ hj₀ i)
    · have hzero : cramerKernelVector A f j₀ j = 0 := by
        rw [cramerKernelVector]
        simp only [if_neg hj, zero_sub, neg_eq_zero]
        apply Finset.sum_eq_zero
        intro i _
        simp only [ite_eq_right_iff]
        exact fun h ↦ False.elim (hjf ⟨i, h⟩)
      rw [hzero, abs_zero]
      exact (abs_nonneg (coordinateMinor A f).det).trans (hminor f hf)

/-- Real-valued form convenient for comparison with lattice covolume. -/
theorem exists_ne_zero_mulVec_eq_zero_abs_cast_le
    (A : Matrix (Fin r) (Fin n) ℤ)
    (f : Fin r → Fin n) (hf : Function.Injective f)
    (j₀ : Fin n) (hj₀ : j₀ ∉ Set.range f)
    (hdet : (coordinateMinor A f).det ≠ 0)
    (D : ℝ) (hminor : ∀ g : Fin r → Fin n,
      Function.Injective g →
        ((|(coordinateMinor A g).det| : ℤ) : ℝ) ≤ D) :
    ∃ x : Fin n → ℤ, x ≠ 0 ∧ Matrix.mulVec A x = 0 ∧
      ∀ j, ((|x j| : ℤ) : ℝ) ≤ D := by
  let x := cramerKernelVector A f j₀
  refine ⟨x, cramerKernelVector_ne_zero A f j₀ hj₀ hdet,
    mulVec_cramerKernelVector A f j₀, ?_⟩
  intro j
  by_cases hj : j = j₀
  · subst j
    rw [show x j₀ = (coordinateMinor A f).det from
      cramerKernelVector_extra A f j₀ hj₀]
    exact hminor f hf
  · by_cases hjf : j ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hjf
      rw [show x (f i) =
          -Matrix.cramer (coordinateMinor A f) (fun a ↦ A a j₀) i from
        cramerKernelVector_selected A f hf j₀ hj₀ i,
        abs_neg, cramer_eq_replaced_minor]
      exact hminor _ (replaceCoordinate_injective f hf j₀ hj₀ i)
    · have hzero : x j = 0 := by
        dsimp only [x]
        rw [cramerKernelVector]
        simp only [if_neg hj, zero_sub, neg_eq_zero]
        apply Finset.sum_eq_zero
        intro i _
        simp only [ite_eq_right_iff]
        exact fun h ↦ False.elim (hjf ⟨i, h⟩)
      rw [hzero, abs_zero, Int.cast_zero]
      exact (show (0 : ℝ) ≤ ((|(coordinateMinor A f).det| : ℤ) : ℝ) by positivity).trans
        (hminor f hf)

/-- Bombieri--Vaaler's integer-normal-vector conclusion in matrix form.

The selected nonsingular minor certifies full row rank, while `j₀` certifies
that the ambient dimension is larger.  The resulting nonzero integral
kernel vector has sup norm at most the Euclidean covolume of the row
lattice, equivalently the square root of its Gram determinant. -/
theorem exists_ne_zero_mulVec_eq_zero_abs_cast_le_rowCovolume
    (A : Matrix (Fin r) (Fin n) ℤ)
    (f : Fin r → Fin n) (hf : Function.Injective f)
    (j₀ : Fin n) (hj₀ : j₀ ∉ Set.range f)
    (hdet : (coordinateMinor A f).det ≠ 0) :
    ∃ x : Fin n → ℤ, x ≠ 0 ∧ Matrix.mulVec A x = 0 ∧
      ∀ j, ((|x j| : ℤ) : ℝ) ≤ rowCovolume A := by
  exact exists_ne_zero_mulVec_eq_zero_abs_cast_le A f hf j₀ hj₀ hdet
    (rowCovolume A) (abs_coordinateMinor_cast_le_rowCovolume A)

/-- Square-root-of-Gram formulation of the same theorem, matching the
usual determinant notation in the statement of Bilu's Lemma 6.10. -/
theorem exists_ne_zero_mulVec_eq_zero_abs_cast_le_sqrt_det_gram
    (A : Matrix (Fin r) (Fin n) ℤ)
    (f : Fin r → Fin n) (hf : Function.Injective f)
    (j₀ : Fin n) (hj₀ : j₀ ∉ Set.range f)
    (hdet : (coordinateMinor A f).det ≠ 0) :
    ∃ x : Fin n → ℤ, x ≠ 0 ∧ Matrix.mulVec A x = 0 ∧
      ∀ j, ((|x j| : ℤ) : ℝ) ≤
        Real.sqrt (Matrix.gram ℝ (realRow A)).det := by
  simpa [rowCovolume_eq_sqrt_det_gram] using
    exists_ne_zero_mulVec_eq_zero_abs_cast_le_rowCovolume A f hf j₀ hj₀ hdet

end Erdos186.CFP.Bilu.BombieriVaaler

#print axioms Erdos186.CFP.Bilu.BombieriVaaler.exists_ne_zero_mulVec_eq_zero_abs_cast_le_sqrt_det_gram
