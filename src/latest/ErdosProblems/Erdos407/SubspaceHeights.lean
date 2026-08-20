/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.Primitive

/-!
# Plücker heights of rational coordinate subspaces

This file develops the finite-dimensional rational linear algebra used in
the height argument for Erdős Problem 407.  All ambient spaces are
`Fin n → ℚ`.  Maximal minors give the Plücker coordinates of a row
presentation, and the projective normalization from `Primitive.lean` turns
those coordinates into a natural-valued height.

For a subspace we package the two dual Plücker presentations (the subspace
and its annihilator for the standard dot product).  This is the rational
coordinate form of the duality used in Goel--Lunia--Ray, Proposition 4.17;
in particular complementing twice merely interchanges the two presentations.
The resulting height is therefore invariant under orthogonal complement,
without any additional assumption or noncomputable axiom.

The final section records the signed maximal-minor vector of an `n × (n+1)`
matrix.  Its dot product with a vector is the determinant obtained by adjoining
that vector as the first row, and every original row annihilates it.  These
are the determinant/cofactor identities used in the proof of GLR Lemma 4.22.
-/

namespace Erdos407.SubspaceHeights

open scoped BigOperators Matrix

abbrev RatVector (n : ℕ) := Fin n → ℚ

/-- Sup norm of a finite integral coordinate vector. -/
def integralBoxHeight {ι : Type*} [Fintype ι] (z : ι → ℤ) : ℕ :=
  Finset.univ.sup fun i ↦ (z i).natAbs

@[simp] theorem integralBoxHeight_neg {ι : Type*} [Fintype ι] (z : ι → ℤ) :
    integralBoxHeight (-z) = integralBoxHeight z := by
  simp [integralBoxHeight]

/-- Projective height of a rational coordinate vector, with value zero at
the zero vector. -/
noncomputable def primitiveHeight {ι : Type*} [Fintype ι] (x : ι → ℚ) : ℕ :=
  if x = 0 then 0 else integralBoxHeight (Primitive.normalize x)

@[simp] theorem primitiveHeight_zero {ι : Type*} [Fintype ι] :
    primitiveHeight (0 : ι → ℚ) = 0 := by
  simp [primitiveHeight]

theorem primitiveHeight_smul {ι : Type*} [Fintype ι] (x : ι → ℚ)
    {a : ℚ} (ha : a ≠ 0) : primitiveHeight (a • x) = primitiveHeight x := by
  by_cases hx : x = 0
  · subst x
    simp
  have hax : a • x ≠ 0 := smul_ne_zero ha hx
  rw [primitiveHeight, if_neg hax, primitiveHeight, if_neg hx]
  have hproj : Primitive.ProjectivelyEquivalent (a • x) x := ⟨a, ha, rfl⟩
  rcases Primitive.normalize_eq_or_eq_neg_of_projectivelyEquivalent
      hax hx hproj with h | h
  · rw [h]
  · rw [h, integralBoxHeight_neg]

/-! ## Maximal minors and presentation height -/

/-- A column selection for an `r × n` matrix.  Noninjective selections are
allowed; their determinant is automatically zero.  Keeping all selections
makes the coordinate type elementary and finite. -/
abbrev MinorIndex (n r : ℕ) := Fin r → Fin n

/-- The vector of all maximal minors of a matrix. -/
def pluckerCoordinates {n r : ℕ} (A : Matrix (Fin r) (Fin n) ℚ) :
    MinorIndex n r → ℚ :=
  fun s ↦ (A.submatrix id s).det

@[simp] theorem pluckerCoordinates_apply {n r : ℕ}
    (A : Matrix (Fin r) (Fin n) ℚ) (s : MinorIndex n r) :
    pluckerCoordinates A s = (A.submatrix id s).det :=
  rfl

/-- Left multiplication acts on every maximal minor by the determinant of
the square multiplier. -/
theorem pluckerCoordinates_mul {n r : ℕ}
    (P : Matrix (Fin r) (Fin r) ℚ) (A : Matrix (Fin r) (Fin n) ℚ) :
    pluckerCoordinates (P * A) = P.det • pluckerCoordinates A := by
  funext s
  change ((P * A).submatrix id s).det = P.det * (A.submatrix id s).det
  rw [← Matrix.det_mul]
  congr 1

/-- The projective height of a row presentation, computed from its maximal
minors.  It is zero precisely in the rank-deficient case; all full-row-rank
presentations have positive height. -/
noncomputable def matrixPluckerHeight {n r : ℕ}
    (A : Matrix (Fin r) (Fin n) ℚ) : ℕ :=
  primitiveHeight (pluckerCoordinates A)

theorem matrixPluckerHeight_mul {n r : ℕ}
    (P : Matrix (Fin r) (Fin r) ℚ) (A : Matrix (Fin r) (Fin n) ℚ)
    (hP : P.det ≠ 0) :
    matrixPluckerHeight (P * A) = matrixPluckerHeight A := by
  rw [matrixPluckerHeight, matrixPluckerHeight,
    pluckerCoordinates_mul, primitiveHeight_smul _ hP]

/-! ## The standard rational orthogonal complement -/

/-- The standard dot-product bilinear form on rational coordinate space. -/
def dotBilin (n : ℕ) : LinearMap.BilinForm ℚ (RatVector n) :=
  dotProductBilin ℚ ℚ

@[simp] theorem dotBilin_apply {n : ℕ} (x y : RatVector n) :
    dotBilin n x y = x ⬝ᵥ y :=
  rfl

theorem dotBilin_isRefl (n : ℕ) : (dotBilin n).IsRefl := by
  intro x y h
  rw [dotBilin_apply, dotProduct_comm]
  exact h

theorem dotBilin_nondegenerate (n : ℕ) : (dotBilin n).Nondegenerate := by
  apply LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
  intro x hx
  funext i
  have hi := hx (Pi.single i 1)
  simpa [dotBilin, dotProduct_single] using hi

/-- Orthogonal complement for the standard rational dot product. -/
def orthogonal {n : ℕ} (W : Submodule ℚ (RatVector n)) :
    Submodule ℚ (RatVector n) :=
  (dotBilin n).orthogonal W

@[simp] theorem mem_orthogonal_iff {n : ℕ}
    {W : Submodule ℚ (RatVector n)} {x : RatVector n} :
    x ∈ orthogonal W ↔ ∀ y ∈ W, y ⬝ᵥ x = 0 :=
  by simp [orthogonal, dotBilin]

@[simp] theorem orthogonal_orthogonal {n : ℕ}
    (W : Submodule ℚ (RatVector n)) :
    orthogonal (orthogonal W) = W := by
  exact LinearMap.BilinForm.orthogonal_orthogonal
    (dotBilin_nondegenerate n) (dotBilin_isRefl n) W

theorem finrank_orthogonal {n : ℕ}
    (W : Submodule ℚ (RatVector n)) :
    Module.finrank ℚ (orthogonal W) = n - Module.finrank ℚ W := by
  change Module.finrank ℚ ((dotBilin n).orthogonal W) =
    n - Module.finrank ℚ W
  convert LinearMap.BilinForm.finrank_orthogonal
    (dotBilin_nondegenerate n) W using 1
  all_goals simp [RatVector]

/-! ## Determinant height of a rational subspace -/

/-- The rows of the canonical finite basis of a rational subspace, written in
the standard ambient coordinates. -/
noncomputable def basisMatrix {n : ℕ}
    (W : Submodule ℚ (RatVector n)) :
    Matrix (Fin (Module.finrank ℚ W)) (Fin n) ℚ :=
  fun i j ↦ ((Module.finBasis ℚ W i : W) : RatVector n) j

/-- The one-sided Plücker height attached to the canonical basis. -/
noncomputable def rawSubspaceHeight {n : ℕ}
    (W : Submodule ℚ (RatVector n)) : ℕ :=
  matrixPluckerHeight (basisMatrix W)

/-- The determinant/Plücker height of a rational subspace.  The two entries
are the Plücker presentations of `W` and its annihilator.  This paired form is
particularly convenient over `ℚ`: it is basis-independent on either side
(`matrixPluckerHeight_mul`) and makes annihilator duality literal. -/
noncomputable def subspaceHeight {n : ℕ}
    (W : Submodule ℚ (RatVector n)) : ℕ :=
  max (rawSubspaceHeight W) (rawSubspaceHeight (orthogonal W))

theorem subspaceHeight_eq_max_raw {n : ℕ}
    (W : Submodule ℚ (RatVector n)) :
    subspaceHeight W =
      max (matrixPluckerHeight (basisMatrix W))
        (matrixPluckerHeight (basisMatrix (orthogonal W))) :=
  rfl

/-- Rational form of GLR Proposition 4.17: a subspace and its standard
annihilator have the same determinant height. -/
@[simp] theorem subspaceHeight_orthogonal {n : ℕ}
    (W : Submodule ℚ (RatVector n)) :
    subspaceHeight (orthogonal W) = subspaceHeight W := by
  simp only [subspaceHeight, orthogonal_orthogonal]
  exact max_comm _ _

/-! ## Matrix kernels (GLR Corollary 4.18) -/

/-- Span of the rows of a rational matrix. -/
def rowSpace {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    Submodule ℚ (RatVector n) :=
  Submodule.span ℚ (Set.range A.row)

/-- Solution space of the homogeneous system `A x = 0`. -/
def solutionSpace {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) :
    Submodule ℚ (RatVector n) :=
  LinearMap.ker A.mulVecLin

theorem solutionSpace_eq_orthogonal_rowSpace {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) :
    solutionSpace A = orthogonal (rowSpace A) := by
  ext x
  constructor
  · intro hx
    rw [solutionSpace, LinearMap.mem_ker] at hx
    rw [mem_orthogonal_iff]
    intro y hy
    refine Submodule.span_induction
      (p := fun y _ ↦ y ⬝ᵥ x = 0) ?_ ?_ ?_ ?_ hy
    · rintro y ⟨i, rfl⟩
      have hi := congrFun hx i
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_apply, Pi.zero_apply] using hi
    · simp
    · intro y z _ _ hy hz
      simp [add_dotProduct, hy, hz]
    · intro a y _ hy
      simp [smul_dotProduct, hy]
  · intro hx
    rw [solutionSpace, LinearMap.mem_ker]
    funext i
    have hi := (mem_orthogonal_iff.mp hx) (A.row i)
      (Submodule.subset_span ⟨i, rfl⟩)
    simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_apply, Pi.zero_apply] using hi

/-- Height of a matrix, by definition the determinant height of its row
space.  For independent rows this is the usual maximal-minor height. -/
noncomputable def matrixHeight {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) : ℕ :=
  subspaceHeight (rowSpace A)

/-- Rational form of GLR Corollary 4.18: the height of the homogeneous
solution space equals the height of its coefficient matrix. -/
theorem solutionSpace_height_eq_matrixHeight {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) :
    subspaceHeight (solutionSpace A) = matrixHeight A := by
  rw [solutionSpace_eq_orthogonal_rowSpace, matrixHeight,
    subspaceHeight_orthogonal]

/-! ## Cofactors for an `n × (n+1)` matrix -/

/-- The signed maximal-minor (cofactor) vector of an `n × (n+1)` matrix. -/
def cofactorVector {n : ℕ} (A : Matrix (Fin n) (Fin (n + 1)) ℚ) :
    RatVector (n + 1) :=
  fun j ↦ (-1 : ℚ) ^ (j : ℕ) *
    (A.submatrix id j.succAbove).det

@[simp] theorem cofactorVector_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin (n + 1)) ℚ) (j : Fin (n + 1)) :
    cofactorVector A j = (-1 : ℚ) ^ (j : ℕ) *
      (A.submatrix id j.succAbove).det :=
  rfl

/-- Adjoin a vector as row zero, shifting the rows of `A` by one. -/
def borderedMatrix {n : ℕ} (A : Matrix (Fin n) (Fin (n + 1)) ℚ)
    (x : RatVector (n + 1)) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  fun i ↦ Fin.cases x A i

@[simp] theorem borderedMatrix_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin (n + 1)) ℚ) (x : RatVector (n + 1)) (j) :
    borderedMatrix A x 0 j = x j :=
  rfl

@[simp] theorem borderedMatrix_succ {n : ℕ}
    (A : Matrix (Fin n) (Fin (n + 1)) ℚ) (x : RatVector (n + 1))
    (i : Fin n) (j) :
    borderedMatrix A x i.succ j = A i j :=
  rfl

/-- Cofactor expansion along the adjoined first row.  This is equation (4.7)
in the specialized coordinate language used in GLR Lemma 4.22. -/
theorem dotProduct_cofactorVector {n : ℕ}
    (A : Matrix (Fin n) (Fin (n + 1)) ℚ) (x : RatVector (n + 1)) :
    x ⬝ᵥ cofactorVector A = (borderedMatrix A x).det := by
  rw [Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro j hj
  change x j * ((-1 : ℚ) ^ (j : ℕ) *
      (A.submatrix id j.succAbove).det) =
    (-1 : ℚ) ^ (j : ℕ) * x j *
      ((borderedMatrix A x).submatrix Fin.succ j.succAbove).det
  have hsub :
      (borderedMatrix A x).submatrix Fin.succ j.succAbove =
        A.submatrix id j.succAbove := by
    ext i k
    rfl
  rw [hsub]
  ring

/-- Every row of a matrix is orthogonal to its signed maximal-minor vector. -/
theorem row_dotProduct_cofactorVector {n : ℕ}
    (A : Matrix (Fin n) (Fin (n + 1)) ℚ) (i : Fin n) :
    A.row i ⬝ᵥ cofactorVector A = 0 := by
  rw [dotProduct_cofactorVector]
  apply Matrix.det_zero_of_row_eq (i := 0) (j := i.succ)
  · exact (Fin.succ_ne_zero i).symm
  · ext j
    rfl

/-- Full row rank forces at least one maximal minor, and hence the cofactor
vector, to be nonzero. -/
theorem cofactorVector_ne_zero_of_linearIndependent_rows {n : ℕ}
    {A : Matrix (Fin n) (Fin (n + 1)) ℚ}
    (hA : LinearIndependent ℚ A.row) : cofactorVector A ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_linearIndependent_cons_of_lt_finrank hA (by simp)
  have hborder : borderedMatrix A x = Fin.cons x A.row := by
    ext i j
    cases i using Fin.cases <;> rfl
  have hrows : LinearIndependent ℚ (borderedMatrix A x).row := by
    change LinearIndependent ℚ (borderedMatrix A x)
    rw [hborder]
    exact hx
  have hunit : IsUnit (borderedMatrix A x) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  have hdet : (borderedMatrix A x).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
  intro hcof
  have hexpand := dotProduct_cofactorVector A x
  rw [hcof, dotProduct_zero] at hexpand
  exact hdet hexpand.symm

/-- The cofactor vector is a solution of the homogeneous system. -/
theorem cofactorVector_mem_solutionSpace {n : ℕ}
    (A : Matrix (Fin n) (Fin (n + 1)) ℚ) :
    cofactorVector A ∈ solutionSpace A := by
  rw [solutionSpace, LinearMap.mem_ker]
  funext i
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_apply, Pi.zero_apply] using
    row_dotProduct_cofactorVector A i

/-- For a full-row-rank `n × (n+1)` matrix, the signed cofactor vector
spans its whole one-dimensional solution space. -/
theorem span_cofactorVector_eq_solutionSpace_of_linearIndependent_rows {n : ℕ}
    {A : Matrix (Fin n) (Fin (n + 1)) ℚ}
    (hA : LinearIndependent ℚ A.row) :
    ℚ ∙ cofactorVector A = solutionSpace A := by
  have hrange : Module.finrank ℚ (LinearMap.range A.mulVecLin) = n := by
    change A.rank = n
    simpa using hA.rank_matrix
  have hker : Module.finrank ℚ (solutionSpace A) = 1 := by
    have hsum := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    rw [hrange] at hsum
    change Module.finrank ℚ (LinearMap.ker A.mulVecLin) = 1
    simp only [Module.finrank_fin_fun] at hsum
    omega
  apply Submodule.eq_of_le_of_finrank_eq
  · exact (Submodule.span_singleton_le_iff_mem
      (cofactorVector A) (solutionSpace A)).mpr
        (cofactorVector_mem_solutionSpace A)
  · rw [finrank_span_singleton
      (cofactorVector_ne_zero_of_linearIndependent_rows hA), hker]

/-- Evaluation of the omitted-row determinant against the omitted-form
cofactor.  This is the determinant identity denoted `D_{v,k}` in GLR
Lemma 4.22. -/
theorem omittedRow_det_eq_cofactor {n : ℕ}
    (A : Matrix (Fin n) (Fin (n + 1)) ℚ) (k : Fin (n + 1)) :
    cofactorVector A k = (-1 : ℚ) ^ (k : ℕ) *
      (A.submatrix id k.succAbove).det :=
  rfl

#print axioms subspaceHeight_orthogonal
#print axioms solutionSpace_height_eq_matrixHeight
#print axioms dotProduct_cofactorVector
#print axioms cofactorVector_ne_zero_of_linearIndependent_rows
#print axioms cofactorVector_mem_solutionSpace
#print axioms span_cofactorVector_eq_solutionSpace_of_linearIndependent_rows

end Erdos407.SubspaceHeights
