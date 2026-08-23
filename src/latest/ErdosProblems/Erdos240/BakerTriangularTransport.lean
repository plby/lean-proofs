/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Ring

/-!
# Triangular transport for the inner descent in Baker's method

On p. 51 of van der Poorten--Loxton, the factors left after the radical
descent form, in each old exponential coordinate, a one-variable polynomial
family of consecutive degrees.  A triangular change of basis replaces these
factors first by their leading monomials and then by the canonical factors of
the successor level.

This file isolates that algebraic argument.  A family `P 0, ..., P n` with
`natDegree (P j) = j` and nonzero leading coefficients has an invertible
upper-triangular coefficient matrix.  Tensor products of such matrices are
again invertible.  We therefore obtain a reversible transport between any
two tensor-product polynomial families, with arbitrary data outside the
transported coordinates treated as spectator parameters.

No analytic estimate and no source-specific vanishing statement is assumed
here.  The only hypotheses are the exact polynomial degrees and the nonzero
leading coefficients which make the triangular argument valid.
-/

open scoped BigOperators Matrix Polynomial

noncomputable section

namespace Erdos240.BakerTriangularTransport

open Finset Polynomial

universe u v

/-! ## One-variable triangular families -/

/-- A finite one-variable family with consecutive exact degrees and nonzero
leading coefficients.  Monicity is not required. -/
structure PolynomialFamily (K : Type v) [Field K] (n : ℕ) where
  polynomial : Fin (n + 1) → K[X]
  degree : ∀ j, (polynomial j).natDegree = (j : ℕ)
  leadingCoeff_ne_zero : ∀ j, (polynomial j).leadingCoeff ≠ 0

namespace PolynomialFamily

variable {K : Type v} [Field K] {n : ℕ}

/-- Rows are monomial degrees and columns are members of the polynomial
family.  Thus multiplying this matrix by a column of family coefficients
returns the corresponding monomial coefficient column. -/
def coefficientMatrix (P : PolynomialFamily K n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  Matrix.of fun r c ↦ (P.polynomial c).coeff r

theorem coefficientMatrix_isUpperTriangular (P : PolynomialFamily K n) :
    P.coefficientMatrix.IsUpperTriangular := by
  exact Matrix.matrixOfPolynomials_blockTriangular P.polynomial
    (fun j ↦ Nat.le_of_eq (P.degree j))

theorem coefficientMatrix_diagonal (P : PolynomialFamily K n)
    (j : Fin (n + 1)) :
    P.coefficientMatrix j j = (P.polynomial j).leadingCoeff := by
  rw [coefficientMatrix, Matrix.of_apply, ← P.degree j]
  exact coeff_natDegree

/-- The coefficient matrix is nonsingular because it is triangular with the
specified nonzero leading coefficients on its diagonal. -/
theorem det_coefficientMatrix_ne_zero (P : PolynomialFamily K n) :
    P.coefficientMatrix.det ≠ 0 := by
  rw [Matrix.det_of_isUpperTriangular P.coefficientMatrix_isUpperTriangular]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  rw [P.coefficientMatrix_diagonal]
  exact P.leadingCoeff_ne_zero j

/-- A finite linear combination of a polynomial family. -/
def linearCombination (P : PolynomialFamily K n)
    (c : Fin (n + 1) → K) : K[X] :=
  ∑ j, C (c j) * P.polynomial j

theorem coeff_linearCombination (P : PolynomialFamily K n)
    (c : Fin (n + 1) → K) (r : Fin (n + 1)) :
    (P.linearCombination c).coeff r = P.coefficientMatrix.mulVec c r := by
  simp [linearCombination, coefficientMatrix, Matrix.mulVec, dotProduct,
    mul_comm]

theorem natDegree_linearCombination_le (P : PolynomialFamily K n)
    (c : Fin (n + 1) → K) :
    (P.linearCombination c).natDegree ≤ n := by
  unfold linearCombination
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_C_mul_le _ _).trans (by
    rw [P.degree j]
    exact Nat.lt_succ_iff.mp j.isLt)

/-- The change-of-basis matrix from `P`-coefficients to `Q`-coefficients. -/
def changeMatrix (P Q : PolynomialFamily K n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  Q.coefficientMatrix⁻¹ * P.coefficientMatrix

/-- Transport coefficients from the `P` family to the `Q` family. -/
def transport (P Q : PolynomialFamily K n) (c : Fin (n + 1) → K) :
    Fin (n + 1) → K :=
  (P.changeMatrix Q).mulVec c

theorem coefficientMatrix_mulVec_transport (P Q : PolynomialFamily K n)
    (c : Fin (n + 1) → K) :
    Q.coefficientMatrix.mulVec (P.transport Q c) =
      P.coefficientMatrix.mulVec c := by
  unfold transport changeMatrix
  calc
    Q.coefficientMatrix *ᵥ
        (Q.coefficientMatrix⁻¹ * P.coefficientMatrix) *ᵥ c =
        (Q.coefficientMatrix *
          (Q.coefficientMatrix⁻¹ * P.coefficientMatrix)).mulVec c :=
      Matrix.mulVec_mulVec c Q.coefficientMatrix
        (Q.coefficientMatrix⁻¹ * P.coefficientMatrix)
    _ =
        (Q.coefficientMatrix * Q.coefficientMatrix⁻¹ *
          P.coefficientMatrix).mulVec c := by
            exact congrArg (fun M ↦ M.mulVec c)
              (Matrix.mul_assoc Q.coefficientMatrix
                Q.coefficientMatrix⁻¹ P.coefficientMatrix).symm
    _ = P.coefficientMatrix.mulVec c := by
      rw [Matrix.mul_nonsing_inv Q.coefficientMatrix
        (isUnit_iff_ne_zero.mpr Q.det_coefficientMatrix_ne_zero),
        Matrix.one_mul]

/-- Transport does not change the represented polynomial. -/
theorem linearCombination_transport (P Q : PolynomialFamily K n)
    (c : Fin (n + 1) → K) :
    Q.linearCombination (P.transport Q c) = P.linearCombination c := by
  ext k
  by_cases hk : k < n + 1
  · let r : Fin (n + 1) := ⟨k, hk⟩
    change (Q.linearCombination (P.transport Q c)).coeff (r : ℕ) =
      (P.linearCombination c).coeff (r : ℕ)
    rw [Q.coeff_linearCombination, P.coeff_linearCombination]
    exact congrFun (P.coefficientMatrix_mulVec_transport Q c) r
  · have hnk : n < k := by omega
    rw [coeff_eq_zero_of_natDegree_lt
          ((Q.natDegree_linearCombination_le _).trans_lt hnk),
      coeff_eq_zero_of_natDegree_lt
          ((P.natDegree_linearCombination_le _).trans_lt hnk)]

theorem changeMatrix_det_ne_zero (P Q : PolynomialFamily K n) :
    (P.changeMatrix Q).det ≠ 0 := by
  have hQinv : Q.coefficientMatrix⁻¹.det ≠ 0 :=
    (Matrix.isUnit_nonsing_inv_det Q.coefficientMatrix
      (isUnit_iff_ne_zero.mpr Q.det_coefficientMatrix_ne_zero)).ne_zero
  rw [changeMatrix, Matrix.det_mul]
  exact mul_ne_zero hQinv P.det_coefficientMatrix_ne_zero

/-- Triangular transport is injective, so in particular it preserves a
nonzero coefficient family. -/
theorem transport_injective (P Q : PolynomialFamily K n) :
    Function.Injective (P.transport Q) := by
  unfold transport
  exact Matrix.mulVec_injective_of_det_ne_zero (P.changeMatrix_det_ne_zero Q)

theorem transport_ne_zero_iff (P Q : PolynomialFamily K n)
    (c : Fin (n + 1) → K) :
    P.transport Q c ≠ 0 ↔ c ≠ 0 := by
  constructor
  · intro ht hc
    apply ht
    subst c
    simp [transport]
  · intro hc hzero
    apply hc
    apply P.transport_injective Q
    simpa [transport] using hzero

/-- The inverse triangular basis change is the transport in the opposite
direction. -/
theorem transport_symm_transport (P Q : PolynomialFamily K n)
    (c : Fin (n + 1) → K) :
    Q.transport P (P.transport Q c) = c := by
  apply Matrix.mulVec_injective_of_det_ne_zero P.det_coefficientMatrix_ne_zero
  calc
    P.coefficientMatrix.mulVec (Q.transport P (P.transport Q c)) =
        Q.coefficientMatrix.mulVec (P.transport Q c) :=
      Q.coefficientMatrix_mulVec_transport P (P.transport Q c)
    _ = P.coefficientMatrix.mulVec c :=
      P.coefficientMatrix_mulVec_transport Q c

/-- The monomial family `1, X, ..., X^n`. -/
def monomial (K : Type v) [Field K] (n : ℕ) : PolynomialFamily K n where
  polynomial j := X ^ (j : ℕ)
  degree j := by simp
  leadingCoeff_ne_zero j := by simp

@[simp] theorem monomial_polynomial (j : Fin (n + 1)) :
    (monomial K n).polynomial j = X ^ (j : ℕ) := rfl

/-- Compose every family member with the nonconstant affine polynomial
`a*X+b`.  Exact consecutive degrees and nonzero leading coefficients are
preserved.  This packages the affine residue lift `Y ↦ qY+c` on p. 51. -/
def affineComp (P : PolynomialFamily K n) (a b : K) (ha : a ≠ 0) :
    PolynomialFamily K n where
  polynomial j := (P.polynomial j).comp (C a * X + C b)
  degree j := by
    rw [Polynomial.natDegree_comp, P.degree j,
      Polynomial.natDegree_linear ha, Nat.mul_one]
  leadingCoeff_ne_zero j := by
    have hdegree : (C a * X + C b : K[X]).natDegree ≠ 0 := by
      rw [Polynomial.natDegree_linear ha]
      norm_num
    rw [Polynomial.leadingCoeff_comp hdegree,
      Polynomial.leadingCoeff_linear ha]
    exact mul_ne_zero (P.leadingCoeff_ne_zero j) (pow_ne_zero _ ha)

@[simp] theorem affineComp_polynomial (P : PolynomialFamily K n)
    (a b : K) (ha : a ≠ 0) (j : Fin (n + 1)) :
    (P.affineComp a b ha).polynomial j =
      (P.polynomial j).comp (C a * X + C b) := rfl

theorem eval_affineComp (P : PolynomialFamily K n)
    (a b : K) (ha : a ≠ 0) (j : Fin (n + 1)) (x : K) :
    ((P.affineComp a b ha).polynomial j).eval x =
      (P.polynomial j).eval (a * x + b) := by
  simp [affineComp, Polynomial.eval_comp]

end PolynomialFamily

/-! ## Simultaneous tensor transport -/

/-- A consecutive-degree polynomial family in every coordinate of a finite
box. -/
abbrev TensorFamily (K : Type v) [Field K]
    (I : Type u) (side : I → ℕ) :=
  ∀ i, PolynomialFamily K (side i)

/-- The dependent finite box of family indices (or monomial degrees). -/
abbrev Box {I : Type u} (side : I → ℕ) :=
  ∀ i, Fin (side i + 1)

namespace TensorFamily

variable {K : Type v} [Field K]
variable {I : Type u} [Fintype I] [DecidableEq I]
variable {side : I → ℕ}

/-- Tensor product of a family of matrices whose coordinate types are the
finite intervals prescribed by `side`.  This specialized definition avoids
any universe identification between `I` and the `Fin` coordinate types. -/
def boxMatrix
    (M : ∀ i, Matrix (Fin (side i + 1)) (Fin (side i + 1)) K) :
    Matrix (Box side) (Box side) K :=
  fun r c ↦ ∏ i, M i (r i) (c i)

theorem boxMatrix_mul
    (A B : ∀ i, Matrix (Fin (side i + 1)) (Fin (side i + 1)) K) :
    boxMatrix A * boxMatrix B = boxMatrix (fun i ↦ A i * B i) := by
  classical
  ext r c
  simp only [Matrix.mul_apply, boxMatrix]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.prod_mul_distrib]

omit [DecidableEq I] in
theorem boxMatrix_one :
    boxMatrix (fun i ↦ (1 : Matrix (Fin (side i + 1))
      (Fin (side i + 1)) K)) = 1 := by
  classical
  ext r c
  simp only [boxMatrix, Matrix.one_apply]
  by_cases h : r = c
  · subst c
    simp
  · have hcoord : ∃ i, r i ≠ c i := by
      by_contra hall
      apply h
      funext i
      by_contra hi
      exact hall ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hcoord
    have hprod : ∏ j, (if r j = c j then (1 : K) else 0) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    rw [hprod, if_neg h]

/-- Tensor product of all one-coordinate coefficient matrices. -/
def coefficientMatrix (P : TensorFamily K I side) :
    Matrix (Box side) (Box side) K :=
  boxMatrix fun i ↦ (P i).coefficientMatrix

theorem det_coefficientMatrix_ne_zero (P : TensorFamily K I side) :
    P.coefficientMatrix.det ≠ 0 := by
  classical
  let Minv : ∀ i, Matrix (Fin (side i + 1)) (Fin (side i + 1)) K :=
    fun i ↦ (P i).coefficientMatrix⁻¹
  apply Matrix.det_ne_zero_of_left_inverse
    (B := boxMatrix Minv)
  rw [coefficientMatrix, boxMatrix_mul]
  calc
    boxMatrix (fun i ↦ Minv i * (P i).coefficientMatrix) =
        boxMatrix (fun i ↦ (1 : Matrix (Fin (side i + 1))
          (Fin (side i + 1)) K)) := by
      congr 1
      funext i
      exact Matrix.nonsing_inv_mul (P i).coefficientMatrix
        (isUnit_iff_ne_zero.mpr (P i).det_coefficientMatrix_ne_zero)
    _ = 1 := boxMatrix_one

/-- The coefficient of the tensor monomial indexed by `r` in the tensor
product member indexed by `a`. -/
def productCoefficient (P : TensorFamily K I side)
    (r a : Box side) : K :=
  ∏ i, ((P i).polynomial (a i)).coeff (r i)

omit [DecidableEq I] in
@[simp] theorem coefficientMatrix_apply (P : TensorFamily K I side)
    (r a : Box side) :
    P.coefficientMatrix r a = P.productCoefficient r a := by
  rfl

/-- All tensor-product coefficient relations associated with a coefficient
column. -/
def relations (P : TensorFamily K I side) (c : Box side → K) :
    Box side → K :=
  P.coefficientMatrix.mulVec c

theorem relations_apply (P : TensorFamily K I side) (c : Box side → K)
    (r : Box side) :
    P.relations c r = ∑ a, P.productCoefficient r a * c a := by
  simp [relations, coefficientMatrix, boxMatrix, productCoefficient,
    PolynomialFamily.coefficientMatrix, Matrix.mulVec, dotProduct]

/-- Simultaneous triangular transport from tensor family `P` to tensor
family `Q`.  The definition may be applied pointwise in any additional
spectator parameter. -/
def transport (P Q : TensorFamily K I side) (c : Box side → K) :
    Box side → K :=
  Q.coefficientMatrix⁻¹.mulVec (P.coefficientMatrix.mulVec c)

/-- Tensor transport preserves every product-coefficient relation. -/
theorem relations_transport (P Q : TensorFamily K I side)
    (c : Box side → K) :
    Q.relations (P.transport Q c) = P.relations c := by
  unfold relations transport
  calc
    Q.coefficientMatrix *ᵥ Q.coefficientMatrix⁻¹ *ᵥ
        P.coefficientMatrix *ᵥ c =
        (Q.coefficientMatrix * Q.coefficientMatrix⁻¹).mulVec
          (P.coefficientMatrix.mulVec c) := by
            rw [Matrix.mulVec_mulVec]
    _ = P.coefficientMatrix.mulVec c := by
      rw [Matrix.mul_nonsing_inv Q.coefficientMatrix
        (isUnit_iff_ne_zero.mpr Q.det_coefficientMatrix_ne_zero),
        Matrix.one_mulVec]

theorem transport_injective (P Q : TensorFamily K I side) :
    Function.Injective (P.transport Q) := by
  intro c d h
  apply Matrix.mulVec_injective_of_det_ne_zero P.det_coefficientMatrix_ne_zero
  have hrel := congrArg (fun v ↦ Q.relations v) h
  rw [P.relations_transport Q c, P.relations_transport Q d] at hrel
  simpa only [relations] using hrel

theorem transport_ne_zero_iff (P Q : TensorFamily K I side)
    (c : Box side → K) :
    P.transport Q c ≠ 0 ↔ c ≠ 0 := by
  constructor
  · intro ht hc
    apply ht
    subst c
    simp [transport]
  · intro hc hzero
    apply hc
    apply P.transport_injective Q
    simpa [transport] using hzero

/-- The inverse tensor basis change is transport in the opposite direction. -/
theorem transport_symm_transport (P Q : TensorFamily K I side)
    (c : Box side → K) :
    Q.transport P (P.transport Q c) = c := by
  apply Matrix.mulVec_injective_of_det_ne_zero P.det_coefficientMatrix_ne_zero
  change P.relations (Q.transport P (P.transport Q c)) = P.relations c
  rw [Q.relations_transport P, P.relations_transport Q]

/-- Coordinatewise leading-monomial family. -/
def monomial (K : Type v) [Field K] (I : Type u) (side : I → ℕ) :
    TensorFamily K I side :=
  fun i ↦ PolynomialFamily.monomial K (side i)

/-- Replacing every factor by its leading monomial is a reversible
triangular change of coefficients preserving all product relations. -/
theorem exists_monomial_transport (P : TensorFamily K I side)
    (c : Box side → K) :
    ∃ d : Box side → K,
      (d ≠ 0 ↔ c ≠ 0) ∧
      (monomial K I side).relations d = P.relations c := by
  classical
  refine ⟨P.transport (monomial K I side) c, ?_, ?_⟩
  · exact P.transport_ne_zero_iff (monomial K I side) c
  · exact P.relations_transport (monomial K I side) c

/-- Spectator-parameter form used in source applications.  The same tensor
transport is performed independently at every spectator value. -/
theorem exists_transport_with_spectator
    {S : Type*} (P Q : TensorFamily K I side) (c : S → Box side → K) :
    ∃ d : S → Box side → K,
      (∀ s, d s ≠ 0 ↔ c s ≠ 0) ∧
      (∀ s, Q.relations (d s) = P.relations (c s)) := by
  refine ⟨fun s ↦ P.transport Q (c s), ?_, ?_⟩
  · intro s
    exact P.transport_ne_zero_iff Q (c s)
  · intro s
    exact P.relations_transport Q (c s)

/-! ## Evaluation of the transported product families -/

/-- Evaluation of the tensor-product family member indexed by `a`. -/
def productEval (P : TensorFamily K I side) (x : I → K)
    (a : Box side) : K :=
  ∏ i, ((P i).polynomial (a i)).eval (x i)

/-- Evaluation of a finite linear combination of tensor-product members. -/
def evaluatedRelation (P : TensorFamily K I side) (c : Box side → K)
    (x : I → K) : K :=
  ∑ a, c a * P.productEval x a

/-- Evaluation of the tensor monomial indexed by `r`. -/
def monomialEval (x : I → K) (r : Box side) : K :=
  ∏ i, x i ^ (r i : ℕ)

omit [Fintype I] [DecidableEq I] in
theorem polynomial_eval_eq_sum_coeff (P : TensorFamily K I side)
    (i : I) (a : Fin (side i + 1)) (x : K) :
    ((P i).polynomial a).eval x =
      ∑ r : Fin (side i + 1),
        ((P i).polynomial a).coeff r * x ^ (r : ℕ) := by
  have hdeg : ((P i).polynomial a).natDegree < side i + 1 := by
    rw [(P i).degree a]
    exact a.isLt
  rw [Polynomial.eval_eq_sum_range' hdeg x,
    ← Fin.sum_univ_eq_sum_range]

/-- Expansion of one tensor-product family member in the tensor monomial
basis. -/
theorem productEval_eq_sum_productCoefficient
    (P : TensorFamily K I side) (x : I → K) (a : Box side) :
    P.productEval x a =
      ∑ r, P.productCoefficient r a * monomialEval x r := by
  classical
  unfold productEval
  simp_rw [P.polynomial_eval_eq_sum_coeff]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.prod_mul_distrib]
  rfl

/-- The evaluated tensor-product sum is the finite monomial expansion whose
coefficient column is `relations P c`. -/
theorem evaluatedRelation_eq_sum_relations (P : TensorFamily K I side)
    (c : Box side → K) (x : I → K) :
    P.evaluatedRelation c x =
      ∑ r, P.relations c r * monomialEval x r := by
  classical
  unfold evaluatedRelation productEval
  simp_rw [P.polynomial_eval_eq_sum_coeff]
  simp_rw [Fintype.prod_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [P.relations_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.prod_mul_distrib]
  simp only [monomialEval, productCoefficient]
  ring

/-- The triangular coefficient transport preserves the actual evaluated
product sum at every tuple of variables. -/
theorem evaluatedRelation_transport (P Q : TensorFamily K I side)
    (c : Box side → K) (x : I → K) :
    Q.evaluatedRelation (P.transport Q c) x = P.evaluatedRelation c x := by
  rw [Q.evaluatedRelation_eq_sum_relations,
    P.evaluatedRelation_eq_sum_relations, P.relations_transport Q]

/-- Evaluation form with arbitrary spectator data.  Both the coefficient
column and the evaluation tuple may depend on the spectator parameter. -/
theorem evaluatedRelation_transport_with_spectator
    {S : Type*} [Fintype S] (P Q : TensorFamily K I side)
    (c : S → Box side → K) (x : S → I → K) (weight : S → K) :
    (∑ s, weight s * Q.evaluatedRelation (P.transport Q (c s)) (x s)) =
      ∑ s, weight s * P.evaluatedRelation (c s) (x s) := by
  apply Finset.sum_congr rfl
  intro s _
  rw [P.evaluatedRelation_transport Q]

/-- Existence form most convenient for source instantiations: a nonzero
coefficient column remains nonzero after replacing all factors by a second
consecutive-degree family, and every evaluated product identity is retained. -/
theorem exists_evaluated_transport_with_spectator
    {S : Type*} (P Q : TensorFamily K I side) (c : S → Box side → K) :
    ∃ d : S → Box side → K,
      (∀ s, d s ≠ 0 ↔ c s ≠ 0) ∧
      (∀ s x, Q.evaluatedRelation (d s) x =
        P.evaluatedRelation (c s) x) := by
  refine ⟨fun s ↦ P.transport Q (c s), ?_, ?_⟩
  · intro s
    exact P.transport_ne_zero_iff Q (c s)
  · intro s x
    exact P.evaluatedRelation_transport Q (c s) x

/-! ## Dual transport of a complete family of vanishing relations

The preceding transport changes the coefficient column while preserving a
single polynomial combination.  The source's inner induction uses the dual
statement: it has a *complete family of zero relations*, one for every
derivative row, and changes the row basis while leaving the arithmetic
coefficient weights untouched. -/

/-- Relations indexed by the product polynomial family.  `T` is an arbitrary
finite term index: it can include all exponent coordinates and every factor
which is not changed by the triangular argument. -/
def rowRelations {T : Type*} [Fintype T]
    (P : TensorFamily K I side) (weight : T → K) (point : T → I → K) :
    Box side → K :=
  fun a ↦ ∑ t, weight t * P.productEval (point t) a

/-- The monomial moments of the same coefficient weights and evaluation
points. -/
def monomialMoments {T : Type*} [Fintype T]
    (weight : T → K) (point : T → I → K) : Box side → K :=
  fun r ↦ ∑ t, weight t * monomialEval (point t) r

/-- The complete row-relation vector is the transpose coefficient matrix
applied to the monomial-moment vector. -/
theorem rowRelations_eq_transpose_mulVec
    {T : Type*} [Fintype T] (P : TensorFamily K I side)
    (weight : T → K) (point : T → I → K) :
    P.rowRelations weight point =
      P.coefficientMatrix.transpose.mulVec
        (monomialMoments weight point) := by
  classical
  funext a
  simp only [rowRelations, monomialMoments, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply]
  simp_rw [P.productEval_eq_sum_productCoefficient, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [P.coefficientMatrix_apply]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem det_transpose_coefficientMatrix_ne_zero
    (P : TensorFamily K I side) :
    P.coefficientMatrix.transpose.det ≠ 0 := by
  simpa only [Matrix.det_transpose] using P.det_coefficientMatrix_ne_zero

/-- Vanishing of all rows of one consecutive-degree tensor family is
equivalent to vanishing of all tensor monomial moments. -/
theorem rowRelations_eq_zero_iff_monomialMoments_eq_zero
    {T : Type*} [Fintype T] (P : TensorFamily K I side)
    (weight : T → K) (point : T → I → K) :
    P.rowRelations weight point = 0 ↔
      monomialMoments (side := side) weight point = 0 := by
  rw [P.rowRelations_eq_transpose_mulVec]
  constructor
  · exact Matrix.eq_zero_of_mulVec_eq_zero
      P.det_transpose_coefficientMatrix_ne_zero
  · intro h
    rw [h, Matrix.mulVec_zero]

/-- Source-faithful triangular row transport.  The coefficient weights are
literally unchanged: only the complete basis of relation rows is replaced. -/
theorem rowRelations_eq_zero_iff
    {T : Type*} [Fintype T] (P Q : TensorFamily K I side)
    (weight : T → K) (point : T → I → K) :
    P.rowRelations weight point = 0 ↔ Q.rowRelations weight point = 0 := by
  rw [P.rowRelations_eq_zero_iff_monomialMoments_eq_zero,
    Q.rowRelations_eq_zero_iff_monomialMoments_eq_zero]

/-- Directional form: replace an intermediate product family `P` by the
canonical family `Q` without changing a single coefficient weight. -/
theorem rowRelations_eq_zero_transport
    {T : Type*} [Fintype T] (P Q : TensorFamily K I side)
    (weight : T → K) (point : T → I → K)
    (hzero : P.rowRelations weight point = 0) :
    Q.rowRelations weight point = 0 :=
  (P.rowRelations_eq_zero_iff Q weight point).mp hzero

/-- Pointwise spectator form of the row transport. -/
theorem rowRelations_eq_zero_transport_with_spectator
    {T S : Type*} [Fintype T] (P Q : TensorFamily K I side)
    (weight : S → T → K) (point : S → T → I → K)
    (hzero : ∀ s, P.rowRelations (weight s) (point s) = 0) :
    ∀ s, Q.rowRelations (weight s) (point s) = 0 := by
  intro s
  exact P.rowRelations_eq_zero_transport Q (weight s) (point s) (hzero s)

/-! ## Row transport on a total-degree simplex

In the source argument the available relation rows do not fill the entire
box: only multiindices of total weight at most the derivative budget occur.
Triangularity is enough on this lower set.  The proof below first recovers the
monomial moments by induction on total weight and then expands the target
family in those monomials. -/

/-- Total degree of a multiindex in a constant-side box. -/
def totalDegree {S : ℕ} (a : I → Fin (S + 1)) : ℕ :=
  ∑ i, (a i : ℕ)

/-- A row relation is its finite expansion in the monomial moments. -/
theorem rowRelations_apply_eq_sum_productCoefficient_monomialMoments
    {T : Type*} [Fintype T] (P : TensorFamily K I side)
    (weight : T → K) (point : T → I → K) (a : Box side) :
    P.rowRelations weight point a =
      ∑ r, P.productCoefficient r a *
        monomialMoments (side := side) weight point r := by
  rw [P.rowRelations_eq_transpose_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    P.coefficientMatrix_apply]

/-- A nonzero coefficient of a tensor-product family member can only occur
at a coordinatewise smaller monomial. -/
theorem coordinate_le_of_productCoefficient_ne_zero
    (P : TensorFamily K I side) (r a : Box side)
    (h : P.productCoefficient r a ≠ 0) (i : I) :
    (r i : ℕ) ≤ (a i : ℕ) := by
  by_contra hle
  apply h
  unfold productCoefficient
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [(P i).degree (a i)]
  exact Nat.lt_of_not_ge hle

/-- The diagonal tensor coefficient is the product of the nonzero leading
coefficients and hence is nonzero. -/
theorem productCoefficient_diagonal_ne_zero
    (P : TensorFamily K I side) (a : Box side) :
    P.productCoefficient a a ≠ 0 := by
  unfold productCoefficient
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rw [← (P i).degree (a i), Polynomial.coeff_natDegree]
  exact (P i).leadingCoeff_ne_zero (a i)

/-- On the total-degree simplex, vanishing of the consecutive-degree family
rows forces vanishing of every monomial moment in the same simplex.  This is
the lower-triangular induction used implicitly on p. 51. -/
theorem monomialMoments_eq_zero_of_rowRelations_eq_zero_on_simplex
    {T : Type*} [Fintype T] {S : ℕ}
    (P : TensorFamily K I (fun _ ↦ S))
    (weight : T → K) (point : T → I → K)
    (hzero : ∀ a : I → Fin (S + 1), totalDegree a ≤ S →
      P.rowRelations weight point a = 0) :
    ∀ a : I → Fin (S + 1), totalDegree a ≤ S →
      monomialMoments (side := fun _ : I ↦ S) weight point a = 0 := by
  intro a ha
  generalize hn : totalDegree a = n
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
      have hrelation := hzero a ha
      rw [P.rowRelations_apply_eq_sum_productCoefficient_monomialMoments]
        at hrelation
      have hcollapse :
          (∑ r, P.productCoefficient r a *
            monomialMoments (side := fun _ : I ↦ S) weight point r) =
          P.productCoefficient a a *
            monomialMoments (side := fun _ : I ↦ S) weight point a := by
        apply Finset.sum_eq_single a
        · intro r _ hra
          by_cases hcoeff : P.productCoefficient r a = 0
          · simp [hcoeff]
          · have hcoord : ∀ i, (r i : ℕ) ≤ (a i : ℕ) :=
              fun i ↦ P.coordinate_le_of_productCoefficient_ne_zero
                r a hcoeff i
            have hexists : ∃ i, (r i : ℕ) < (a i : ℕ) := by
              by_contra hnone
              apply hra
              funext i
              exact Fin.ext (Nat.le_antisymm (hcoord i)
                (Nat.le_of_not_gt fun hi ↦ hnone ⟨i, hi⟩))
            have hdegree_lt : totalDegree r < totalDegree a := by
              apply Finset.sum_lt_sum
              · intro i _
                exact hcoord i
              · obtain ⟨i, hi⟩ := hexists
                exact ⟨i, Finset.mem_univ i, hi⟩
            have hdegree_le : totalDegree r ≤ S :=
              (Nat.le_of_lt hdegree_lt).trans ha
            have hmoment :
                monomialMoments (side := fun _ : I ↦ S)
                  weight point r = 0 := by
              apply ih (totalDegree r)
              · simpa only [hn] using hdegree_lt
              · exact hdegree_le
              · rfl
            simp [hmoment]
        · intro hnotmem
          exact False.elim (hnotmem (Finset.mem_univ a))
      rw [hcollapse] at hrelation
      exact (mul_eq_zero.mp hrelation).resolve_left
        (P.productCoefficient_diagonal_ne_zero a)

/-- Total-degree/simplex form of the p. 51 row transport.  It changes every
one-variable consecutive-degree family while leaving the term weights and
evaluation points literally unchanged, and it assumes only the rows whose
total derivative order is at most `S`. -/
theorem rowRelations_eq_zero_transport_on_simplex
    {T : Type*} [Fintype T] {S : ℕ}
    (P Q : TensorFamily K I (fun _ ↦ S))
    (weight : T → K) (point : T → I → K)
    (hzero : ∀ a : I → Fin (S + 1), totalDegree a ≤ S →
      P.rowRelations weight point a = 0) :
    ∀ a : I → Fin (S + 1), totalDegree a ≤ S →
      Q.rowRelations weight point a = 0 := by
  have hmom :=
    P.monomialMoments_eq_zero_of_rowRelations_eq_zero_on_simplex
      weight point hzero
  intro a ha
  rw [Q.rowRelations_apply_eq_sum_productCoefficient_monomialMoments]
  apply Finset.sum_eq_zero
  intro r _
  by_cases hcoeff : Q.productCoefficient r a = 0
  · simp [hcoeff]
  · have hcoord : ∀ i, (r i : ℕ) ≤ (a i : ℕ) :=
      fun i ↦ Q.coordinate_le_of_productCoefficient_ne_zero r a hcoeff i
    have hdegree_le : totalDegree r ≤ S :=
      (Finset.sum_le_sum fun i _ ↦ hcoord i).trans ha
    rw [hmom r hdegree_le, mul_zero]

/-- The simplex row-vanishing condition is independent of the chosen
consecutive-degree polynomial family. -/
theorem rowRelations_eq_zero_on_simplex_iff
    {T : Type*} [Fintype T] {S : ℕ}
    (P Q : TensorFamily K I (fun _ ↦ S))
    (weight : T → K) (point : T → I → K) :
    (∀ a : I → Fin (S + 1), totalDegree a ≤ S →
      P.rowRelations weight point a = 0) ↔
    (∀ a : I → Fin (S + 1), totalDegree a ≤ S →
      Q.rowRelations weight point a = 0) := by
  constructor
  · exact P.rowRelations_eq_zero_transport_on_simplex Q weight point
  · exact Q.rowRelations_eq_zero_transport_on_simplex P weight point

end TensorFamily

end Erdos240.BakerTriangularTransport

#print axioms Erdos240.BakerTriangularTransport.PolynomialFamily.det_coefficientMatrix_ne_zero
#print axioms Erdos240.BakerTriangularTransport.PolynomialFamily.linearCombination_transport
#print axioms Erdos240.BakerTriangularTransport.PolynomialFamily.transport_symm_transport
#print axioms Erdos240.BakerTriangularTransport.PolynomialFamily.eval_affineComp
#print axioms Erdos240.BakerTriangularTransport.TensorFamily.relations_transport
#print axioms Erdos240.BakerTriangularTransport.TensorFamily.transport_symm_transport
#print axioms Erdos240.BakerTriangularTransport.TensorFamily.exists_monomial_transport
#print axioms Erdos240.BakerTriangularTransport.TensorFamily.exists_transport_with_spectator
#print axioms Erdos240.BakerTriangularTransport.TensorFamily.evaluatedRelation_transport
#print axioms Erdos240.BakerTriangularTransport.TensorFamily.evaluatedRelation_transport_with_spectator
#print axioms Erdos240.BakerTriangularTransport.TensorFamily.exists_evaluated_transport_with_spectator
#print axioms Erdos240.BakerTriangularTransport.TensorFamily.rowRelations_eq_zero_iff
#print axioms Erdos240.BakerTriangularTransport.TensorFamily.rowRelations_eq_zero_transport
#print axioms Erdos240.BakerTriangularTransport.TensorFamily.rowRelations_eq_zero_transport_with_spectator
#print axioms Erdos240.BakerTriangularTransport.TensorFamily.rowRelations_eq_zero_transport_on_simplex
#print axioms Erdos240.BakerTriangularTransport.TensorFamily.rowRelations_eq_zero_on_simplex_iff
