/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.PadicSubspaceDefs

/-!
# The determinant gap principle at the places `infinity`, `2`, and `3`

This file contains the elementary determinant part of the rational
Subspace-Theorem argument.  It is independent of the auxiliary-polynomial
and Roth-index arguments: a sufficiently small local box cannot contain a
full rational basis of integral points.

The estimates are deliberately kept in product form.  Thus they can be fed
either radii from approximation domains or radii obtained by comparing all
local form values with one strong-inequality solution.
-/

namespace Erdos407.PadicSubspace

open scoped BigOperators Matrix

/-! ## Coordinate, point, and evaluation matrices -/

/-- The coefficient matrix of the basis of forms at a place. -/
def formMatrix {n : ℕ} (L : Place23 → Fin n → RatLinearForm n)
    (v : Place23) : Matrix (Fin n) (Fin n) ℚ :=
  fun i k ↦ L v i (Pi.single k 1)

/-- The integral matrix whose `j`-th column is the point `x j`. -/
def integralPointMatrix {n : ℕ} (x : Fin n → Fin n → ℤ) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i j ↦ x j i

/-- The same point matrix over `ℚ`. -/
def pointMatrix {n : ℕ} (x : Fin n → Fin n → ℤ) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun i j ↦ (x j i : ℚ)

/-- The matrix obtained by evaluating every local form on every point. -/
def evaluationMatrix {n : ℕ} (L : Place23 → Fin n → RatLinearForm n)
    (v : Place23) (x : Fin n → Fin n → ℤ) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun i j ↦ L v i (intCastVec (x j))

theorem linearForm_eq_sum_coeff {n : ℕ} (f : RatLinearForm n)
    (y : Fin n → ℚ) :
    f y = ∑ k, f (Pi.single k 1) * y k := by
  have hy : y = ∑ k, y k • Pi.single k (1 : ℚ) := by
    funext j
    simp [Pi.single_apply]
  calc
    f y = f (∑ k, y k • Pi.single k (1 : ℚ)) := congrArg f hy
    _ = ∑ k, f (y k • Pi.single k (1 : ℚ)) := by rw [map_sum]
    _ = ∑ k, f (Pi.single k 1) * y k := by
      apply Finset.sum_congr rfl
      intro k _
      simp [mul_comm]

/-- Evaluation is exactly left multiplication by the local coefficient
matrix. -/
theorem evaluationMatrix_eq_mul {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (v : Place23)
    (x : Fin n → Fin n → ℤ) :
    evaluationMatrix L v x = formMatrix L v * pointMatrix x := by
  ext i j
  change L v i (intCastVec (x j)) =
    ∑ k, L v i (Pi.single k 1) * (x j k : ℚ)
  exact linearForm_eq_sum_coeff (L v i) (intCastVec (x j))

/-- Exact determinant change of coordinates at one place. -/
theorem det_evaluationMatrix {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (v : Place23)
    (x : Fin n → Fin n → ℤ) :
    (evaluationMatrix L v x).det =
      (formMatrix L v).det * (pointMatrix x).det := by
  rw [evaluationMatrix_eq_mul, Matrix.det_mul]

/-- The rational point determinant is the cast of the integral one. -/
theorem det_pointMatrix {n : ℕ} (x : Fin n → Fin n → ℤ) :
    (pointMatrix x).det = ((integralPointMatrix x).det : ℚ) := by
  rw [Int.cast_det]
  rfl

/-- Exact normed determinant change of coordinates at one place. -/
theorem placeNorm_det_evaluationMatrix {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (v : Place23)
    (x : Fin n → Fin n → ℤ) :
    placeNorm v (evaluationMatrix L v x).det =
      placeNorm v (formMatrix L v).det *
        placeNorm v ((integralPointMatrix x).det : ℚ) := by
  rw [det_evaluationMatrix, det_pointMatrix, placeNorm_mul]

/-! ## Nonsingularity and the three-place product formula -/

/-- The linear coordinate map taking a form to its coefficient row. -/
def formCoeffLinearMap {n : ℕ} : RatLinearForm n →ₗ[ℚ] (Fin n → ℚ) where
  toFun f k := f (Pi.single k 1)
  map_add' f g := by ext k; simp
  map_smul' q f := by ext k; simp

/-- Taking the coefficient row of a linear form is injective. -/
theorem form_coeff_injective {n : ℕ} :
    Function.Injective (formCoeffLinearMap (n := n)) := by
  intro f g h
  apply LinearMap.ext
  intro y
  rw [linearForm_eq_sum_coeff, linearForm_eq_sum_coeff]
  apply Finset.sum_congr rfl
  intro k _
  have hk := congrFun h k
  change f (Pi.single k 1) = g (Pi.single k 1) at hk
  rw [hk]

/-- A nonsingular local family has nonzero coefficient determinant. -/
theorem formMatrix_det_ne_zero {n : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    (hL : IsNonsingularFamily L) (v : Place23) :
    (formMatrix L v).det ≠ 0 := by
  have hrows : LinearIndependent ℚ (fun i ↦ formMatrix L v i) :=
    (hL v).map' formCoeffLinearMap
      (LinearMap.ker_eq_bot.mpr form_coeff_injective)
  have hunit : IsUnit (formMatrix L v) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  exact ((formMatrix L v).isUnit_iff_isUnit_det.mp hunit).ne_zero

instance placeNorm_isAbsoluteValue (v : Place23) : IsAbsoluteValue (placeNorm v) := by
  fin_cases v
  · change IsAbsoluteValue (fun q : ℚ ↦ |q|)
    infer_instance
  · change IsAbsoluteValue (padicNorm 2)
    infer_instance
  · change IsAbsoluteValue (padicNorm 3)
    infer_instance

/-- Product of the local determinant norms of the three form bases. -/
def formDetProduct {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) : ℚ :=
  ∏ v, placeNorm v (formMatrix L v).det

theorem formDetProduct_nonneg {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) :
    0 ≤ formDetProduct L := by
  exact Finset.prod_nonneg fun v _ ↦ placeNorm_nonneg v _

theorem formDetProduct_pos {n : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    (hL : IsNonsingularFamily L) : 0 < formDetProduct L := by
  apply Finset.prod_pos
  intro v _
  exact (IsAbsoluteValue.abv_pos (placeNorm v)).2 (formMatrix_det_ne_zero hL v)

/-- Exact three-place determinant change of coordinates. -/
theorem prod_placeNorm_det_evaluationMatrix {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (x : Fin n → Fin n → ℤ) :
    (∏ v, placeNorm v (evaluationMatrix L v x).det) =
      formDetProduct L *
        PadicProduct.normProduct23 ((integralPointMatrix x).det : ℚ) := by
  simp_rw [placeNorm_det_evaluationMatrix]
  rw [Finset.prod_mul_distrib, prod_placeNorm_eq_threePlaceProduct]
  rfl

/-- The restricted three-place norm product of a nonzero integer is at least
one. -/
theorem one_le_prod_placeNorm_int {z : ℤ} (hz : z ≠ 0) :
    1 ≤ ∏ v : Place23, placeNorm v (z : ℚ) := by
  rw [prod_placeNorm_eq_threePlaceProduct]
  exact one_le_threePlaceProduct_int hz

/-! ## Local determinant bounds and rank drop -/

/-- Product of all `3n` local radii. -/
def localRadiiProduct {n : ℕ} (c : Place23 → Fin n → ℚ) : ℚ :=
  ∏ v, ∏ i, c v i

/-- Row-wise Leibniz bound for a determinant at any of the three places. -/
theorem placeNorm_det_le_rowProduct {n : ℕ} (v : Place23)
    (M : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ)
    (_hc : ∀ i, 0 ≤ c i) (hM : ∀ i j, placeNorm v (M i j) ≤ c i) :
    placeNorm v M.det ≤ (Nat.factorial n : ℚ) * ∏ i, c i := by
  let abv : AbsoluteValue ℚ ℚ :=
    IsAbsoluteValue.toAbsoluteValue (placeNorm v)
  change abv M.det ≤ _
  rw [← Matrix.det_transpose, Matrix.det_apply]
  calc
    abv (∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
        ∏ i, Mᵀ (σ i) i) ≤
        ∑ σ : Equiv.Perm (Fin n),
          abv (Equiv.Perm.sign σ • ∏ i, Mᵀ (σ i) i) :=
      abv.sum_le _ _
    _ = ∑ _σ : Equiv.Perm (Fin n), ∏ i, placeNorm v (M i (_σ i)) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [abv.map_units_int_smul, abv.map_prod]
      rfl
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), ∏ i, c i := by
      apply Finset.sum_le_sum
      intro σ _
      apply Finset.prod_le_prod
      · intro i _
        exact placeNorm_nonneg v _
      · intro i _
        exact hM i (σ i)
    _ = (Nat.factorial n : ℚ) * ∏ i, c i := by
      simp [Fintype.card_perm]

/-- Product-form bound for the evaluated determinants of points in one
local box. -/
theorem prod_placeNorm_det_evaluationMatrix_le {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (x : Fin n → Fin n → ℤ) (c : Place23 → Fin n → ℚ)
    (hc : ∀ v i, 0 ≤ c v i)
    (hx : ∀ j v i, placeNorm v (L v i (intCastVec (x j))) ≤ c v i) :
    (∏ v, placeNorm v (evaluationMatrix L v x).det) ≤
      (Nat.factorial n : ℚ) ^ 3 * localRadiiProduct c := by
  calc
    (∏ v, placeNorm v (evaluationMatrix L v x).det) ≤
        ∏ v, ((Nat.factorial n : ℚ) * ∏ i, c v i) := by
      apply Finset.prod_le_prod
      · intro v _
        exact placeNorm_nonneg v _
      · intro v _
        apply placeNorm_det_le_rowProduct v (evaluationMatrix L v x) (c v)
        · exact hc v
        · intro i j
          exact hx j v i
    _ = (Nat.factorial n : ℚ) ^ 3 * localRadiiProduct c := by
      simp [localRadiiProduct, Finset.prod_mul_distrib]

/-- If the product of the local box radii is smaller than the determinant
of the three changes of basis (including the Leibniz constants), the point
determinant vanishes. -/
theorem det_integralPointMatrix_eq_zero_of_local_bounds {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (x : Fin n → Fin n → ℤ) (c : Place23 → Fin n → ℚ)
    (hc : ∀ v i, 0 ≤ c v i)
    (hx : ∀ j v i, placeNorm v (L v i (intCastVec (x j))) ≤ c v i)
    (hsmall : (Nat.factorial n : ℚ) ^ 3 * localRadiiProduct c <
      formDetProduct L) :
    (integralPointMatrix x).det = 0 := by
  by_contra hdet
  have hprod := one_le_prod_placeNorm_int hdet
  have hchange := prod_placeNorm_det_evaluationMatrix L x
  have hbound := prod_placeNorm_det_evaluationMatrix_le L x c hc hx
  have hleft : formDetProduct L ≤
      formDetProduct L *
        PadicProduct.normProduct23 ((integralPointMatrix x).det : ℚ) := by
    apply le_mul_of_one_le_right (formDetProduct_nonneg L)
    simpa [prod_placeNorm_eq_threePlaceProduct] using hprod
  rw [← hchange] at hleft
  exact (not_lt_of_ge (hleft.trans hbound)) hsmall

/-- The same gap principle stated as rational linear dependence. -/
theorem not_linearIndependent_of_local_bounds {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (x : Fin n → Fin n → ℤ) (c : Place23 → Fin n → ℚ)
    (hc : ∀ v i, 0 ≤ c v i)
    (hx : ∀ j v i, placeNorm v (L v i (intCastVec (x j))) ≤ c v i)
    (hsmall : (Nat.factorial n : ℚ) ^ 3 * localRadiiProduct c <
      formDetProduct L) :
    ¬ LinearIndependent ℚ (fun j ↦ intCastVec (x j)) := by
  intro hlin
  have hcols : LinearIndependent ℚ (pointMatrix x).col := by
    change LinearIndependent ℚ (fun j i ↦ (x j i : ℚ)) at hlin ⊢
    exact hlin
  have hunit : IsUnit (pointMatrix x) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  have hdetQ : (pointMatrix x).det ≠ 0 :=
    ((pointMatrix x).isUnit_iff_isUnit_det.mp hunit).ne_zero
  rw [det_pointMatrix,
    det_integralPointMatrix_eq_zero_of_local_bounds L x c hc hx hsmall,
    Int.cast_zero] at hdetQ
  exact hdetQ rfl

/-- In the gap range all points lie on one proper rational hyperplane. -/
theorem exists_hyperplane_of_local_bounds {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (x : Fin n → Fin n → ℤ) (c : Place23 → Fin n → ℚ)
    (hc : ∀ v i, 0 ≤ c v i)
    (hx : ∀ j v i, placeNorm v (L v i (intCastVec (x j))) ≤ c v i)
    (hsmall : (Nat.factorial n : ℚ) ^ 3 * localRadiiProduct c <
      formDetProduct L) :
    ∃ b : Fin n → ℚ, b ≠ 0 ∧ ∀ j, OnHyperplane b (x j) := by
  have hdetZ := det_integralPointMatrix_eq_zero_of_local_bounds L x c hc hx hsmall
  have hdetQ : (pointMatrix x).det = 0 := by rw [det_pointMatrix, hdetZ, Int.cast_zero]
  obtain ⟨b, hb, hmul⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdetQ
  refine ⟨b, hb, fun j ↦ ?_⟩
  have hj := congrFun hmul j
  simpa [OnHyperplane, Matrix.vecMul, dotProduct, pointMatrix] using hj

/-! ## Comparable strong-inequality solutions -/

/-- The radii obtained by multiplying every anchor value by one comparison
factor. -/
def comparisonRadii {n : ℕ} (L : Place23 → Fin n → RatLinearForm n)
    (C : ℚ) (a : Fin n → ℤ) : Place23 → Fin n → ℚ :=
  fun v i ↦ C * placeNorm v (L v i (intCastVec a))

theorem localRadiiProduct_comparisonRadii {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (C : ℚ)
    (a : Fin n → ℤ) :
    localRadiiProduct (comparisonRadii L C a) =
      C ^ (3 * n) * localFormProduct L (intCastVec a) := by
  simp only [localRadiiProduct, comparisonRadii, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, localFormProduct]
  congr 1
  rw [← pow_mul, Nat.mul_comm]

/-- A quantitatively comparable `n`-tuple of strong-inequality solutions is
linearly dependent once the anchor height clears the explicit determinant
threshold. -/
theorem not_linearIndependent_of_comparable_strong_solutions {n : ℕ}
    [NeZero n] (L : Place23 → Fin n → RatLinearForm n)
    (x : Fin n → Fin n → ℤ) (C : ℚ)
    (hC : 0 ≤ C) (hx0 : x 0 ≠ 0)
    (hstrong : SatisfiesStrongInequality L (x 0))
    (hcomp : ∀ j v i,
      placeNorm v (L v i (intCastVec (x j))) ≤
        C * placeNorm v (L v i (intCastVec (x 0))))
    (hheight : (Nat.factorial n : ℚ) ^ 3 * C ^ (3 * n) <
      formDetProduct L * boxHeight (x 0)) :
    ¬ LinearIndependent ℚ (fun j ↦ intCastVec (x j)) := by
  let A : ℚ := (Nat.factorial n : ℚ) ^ 3 * C ^ (3 * n)
  let P : ℚ := localFormProduct L (intCastVec (x 0))
  let H : ℚ := boxHeight (x 0)
  have hA : 0 ≤ A := by positivity
  have hH : 0 < H := by
    dsimp [H]
    exact_mod_cast boxHeight_pos hx0
  have hP : P ≤ 1 / H := by
    apply (le_div_iff₀ hH).2
    simpa [P, H, SatisfiesStrongInequality] using hstrong
  have hAH : A / H < formDetProduct L := by
    apply (div_lt_iff₀ hH).2
    simpa [A, H, mul_comm] using hheight
  have hAP : A * P < formDetProduct L :=
    (mul_le_mul_of_nonneg_left hP hA).trans_lt (by simpa [div_eq_mul_inv] using hAH)
  apply not_linearIndependent_of_local_bounds L x (comparisonRadii L C (x 0))
  · intro v i
    exact mul_nonneg hC (placeNorm_nonneg v _)
  · exact hcomp
  · rw [localRadiiProduct_comparisonRadii]
    simpa [A, P, mul_assoc] using hAP

/-- Hyperplane form of the comparable strong-solution gap principle. -/
theorem exists_hyperplane_of_comparable_strong_solutions {n : ℕ}
    [NeZero n] (L : Place23 → Fin n → RatLinearForm n)
    (x : Fin n → Fin n → ℤ) (C : ℚ)
    (hC : 0 ≤ C) (hx0 : x 0 ≠ 0)
    (hstrong : SatisfiesStrongInequality L (x 0))
    (hcomp : ∀ j v i,
      placeNorm v (L v i (intCastVec (x j))) ≤
        C * placeNorm v (L v i (intCastVec (x 0))))
    (hheight : (Nat.factorial n : ℚ) ^ 3 * C ^ (3 * n) <
      formDetProduct L * boxHeight (x 0)) :
    ∃ b : Fin n → ℚ, b ≠ 0 ∧ ∀ j, OnHyperplane b (x j) := by
  have hlin := not_linearIndependent_of_comparable_strong_solutions
    L x C hC hx0 hstrong hcomp hheight
  have hdet : (pointMatrix x).det = 0 := by
    by_contra hne
    exact hlin (by
      have hcols := Matrix.linearIndependent_cols_of_det_ne_zero hne
      change LinearIndependent ℚ (fun j i ↦ (x j i : ℚ)) at hcols ⊢
      exact hcols)
  obtain ⟨b, hb, hmul⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  refine ⟨b, hb, fun j ↦ ?_⟩
  have hj := congrFun hmul j
  simpa [OnHyperplane, Matrix.vecMul, dotProduct, pointMatrix] using hj

end Erdos407.PadicSubspace
