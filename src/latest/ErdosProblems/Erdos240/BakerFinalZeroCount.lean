/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerAuxiliary
import ErdosProblems.Erdos240.BakerParameters
import ErdosProblems.Erdos240.ShiftedZeroCount
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The terminal zero count in the van der Poorten--Loxton argument

This file formalizes the algebraic argument on pp. 53--54 of van der
Poorten--Loxton.  Its input `TerminalEquation13` is the literal shape left by
Lemma 6: after grouping the old exponent coordinates, equation (13) is a
sequence of square polynomial-evaluation matrices occurring in (14).  A
matrix at one step may depend on the node and on all old indices not being
eliminated.  The matrices are proved nonsingular below from their consecutive
degrees, so repeated contextual determinant elimination gives (15), not an
assumed coefficient-extraction step.

The remaining one-variable polynomial is a sum of shifts of
`Delta(X;h)^(lambda_0+1)`.  The checked shifted-polynomial Lemma 7 removes the
largest `lambda_0` successively.  The rational grid used for (16) is made
explicit as complete nonzero residue blocks modulo `q`; its nodes are proved
injective and within the source radius.  Finally the source parameters imply
that their total Hasse multiplicity is strictly larger than
`h * (L_0+1)`, the degree bound.

The only input left visible is equation (13) itself together with the
source-specific consecutive-degree polynomial families used to write its
old-coordinate factors.  In the literal source these are the two-argument
polynomials `Delta(X;m)`, not the four-argument powered derivative used in
the head coordinate.  They may also carry the exponential column scale and
depend on the remaining indices.  Constructing equation (13) belongs to
Lemma 6; no zero-count, determinant, endpoint collapse, or numerical
inequality is hidden in that input.
-/

open scoped BigOperators Matrix Polynomial

noncomputable section

namespace Erdos240.BakerFinalZeroCount

open Erdos240
open Erdos240.BakerAuxiliary
open Erdos240.DeltaPower
open Polynomial

universe u

/-! ## Tensor-product determinant elimination -/

/-- The tensor product of a finite family of square matrices, written on the
dependent function type of coordinate choices. -/
def tensorMatrix {I : Type u} [Fintype I] [DecidableEq I]
    {kappa : I → Type u} [∀ i, Fintype (kappa i)]
    {K : Type*} [CommSemiring K]
    (M : ∀ i, Matrix (kappa i) (kappa i) K) :
    Matrix (∀ i, kappa i) (∀ i, kappa i) K :=
  fun r c ↦ ∏ i, M i (r i) (c i)

theorem tensorMatrix_mul {I : Type u} [Fintype I] [DecidableEq I]
    {kappa : I → Type u} [∀ i, Fintype (kappa i)]
    {K : Type*} [CommSemiring K]
    (A B : ∀ i, Matrix (kappa i) (kappa i) K) :
    tensorMatrix A * tensorMatrix B = tensorMatrix (fun i ↦ A i * B i) := by
  classical
  ext r c
  simp only [Matrix.mul_apply, tensorMatrix]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.prod_mul_distrib]

theorem tensorMatrix_one {I : Type u} [Fintype I] [DecidableEq I]
    {kappa : I → Type u} [∀ i, Fintype (kappa i)] [∀ i, DecidableEq (kappa i)]
    {K : Type*} [CommSemiring K] :
    tensorMatrix (fun i ↦ (1 : Matrix (kappa i) (kappa i) K)) = 1 := by
  classical
  ext r c
  simp only [tensorMatrix, Matrix.one_apply]
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

/-- If every coordinate matrix is nonsingular, so is their tensor product.
This is the formal repeated determinant elimination used between (14) and
(15). -/
theorem tensorMatrix_det_ne_zero {I : Type u} [Fintype I] [DecidableEq I]
    {kappa : I → Type u} [∀ i, Fintype (kappa i)] [∀ i, DecidableEq (kappa i)]
    {K : Type*} [Field K]
    (M : ∀ i, Matrix (kappa i) (kappa i) K)
    (hM : ∀ i, (M i).det ≠ 0) :
    (tensorMatrix M).det ≠ 0 := by
  classical
  let Minv : ∀ i, Matrix (kappa i) (kappa i) K := fun i ↦ (M i)⁻¹
  apply Matrix.det_ne_zero_of_left_inverse (B := tensorMatrix Minv)
  rw [tensorMatrix_mul]
  calc
    tensorMatrix (fun i ↦ Minv i * M i) =
        tensorMatrix (fun i ↦ (1 : Matrix (kappa i) (kappa i) K)) := by
      congr 1
      funext i
      exact Matrix.nonsing_inv_mul (M i) (isUnit_iff_ne_zero.mpr (hM i))
    _ = 1 := tensorMatrix_one

/-- Coefficient form of repeated determinant elimination. -/
theorem eq_zero_of_tensor_relations
    {I : Type u} [Fintype I] [DecidableEq I]
    {kappa : I → Type u} [∀ i, Fintype (kappa i)] [∀ i, DecidableEq (kappa i)]
    {K : Type*} [Field K]
    (M : ∀ i, Matrix (kappa i) (kappa i) K)
    (hM : ∀ i, (M i).det ≠ 0)
    (c : (∀ i, kappa i) → K)
    (hrel : ∀ r, ∑ x, tensorMatrix M r x * c x = 0) :
    c = 0 := by
  apply Matrix.eq_zero_of_mulVec_eq_zero (tensorMatrix_det_ne_zero M hM)
  funext r
  simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply] using hrel r

/-! ## The square matrices in equation (14) -/

/-- A source coordinate supplies a consecutive-degree polynomial family and
the same number of distinct evaluation nodes.  Monicity is merely a
normalization: multiplying a source column by a nonzero leading coefficient
does not affect determinant nonvanishing. -/
structure EliminationFamily (n : ℕ) where
  polynomial : Fin (n + 1) → ℂ[X]
  node : Fin (n + 1) → ℂ
  rowScale : Fin (n + 1) → ℂ
  columnScale : Fin (n + 1) → ℂ
  node_injective : Function.Injective node
  rowScale_ne_zero : ∀ j, rowScale j ≠ 0
  columnScale_ne_zero : ∀ j, columnScale j ≠ 0
  degree : ∀ j, (polynomial j).natDegree = (j : ℕ)
  monic : ∀ j, (polynomial j).Monic

namespace EliminationFamily

/-- The typical determinant in (14).  Rows are derivative/polynomial
indices and columns are exponent/evaluation nodes, matching the orientation
of the source relation (which sums over exponent columns).  The nonzero row
scale records the leading coefficient removed when the Hasse derivatives
are normalized to monic polynomials; the column scale records the
prime-power exponential monomial. -/
def matrix {n : ℕ} (E : EliminationFamily n) :
  Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun r c ↦
    E.rowScale r * (E.polynomial r).eval (E.node c) * E.columnScale c

theorem det_matrix_ne_zero {n : ℕ} (E : EliminationFamily n) :
    E.matrix.det ≠ 0 := by
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.of fun r c ↦ (E.polynomial r).eval (E.node c)
  let R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.diagonal E.rowScale
  let D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.diagonal E.columnScale
  have hA : A.det ≠ 0 := by
    change (Matrix.of fun r c ↦ (E.polynomial r).eval (E.node c)).det ≠ 0
    rw [show Matrix.of (fun r c ↦ (E.polynomial r).eval (E.node c)) =
        (Matrix.of fun r c ↦ (E.polynomial c).eval (E.node r))ᵀ by rfl,
      Matrix.det_transpose]
    rw [← Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
      E.node E.polynomial E.degree E.monic]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr E.node_injective
  have hD : D.det ≠ 0 := by
    simp only [D, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ E.columnScale_ne_zero j
  have hR : R.det ≠ 0 := by
    simp only [R, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ E.rowScale_ne_zero j
  have hmatrix : E.matrix = R * A * D := by
    ext r c
    rw [Matrix.mul_diagonal]
    change E.rowScale r * (E.polynomial r).eval (E.node c) *
      E.columnScale c = (R * A) r c * E.columnScale c
    congr 1
    rw [Matrix.diagonal_mul]
    rfl
  rw [hmatrix, Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero hR hA) hD

/-- A high Hasse derivative of a nonzero polynomial is nonzero as long as
the prescribed residual degree is within the original degree. -/
theorem topHasse_ne_zero (Q : ℂ[X]) {m j : ℕ}
    (hQ : Q ≠ 0) (hm : Q.natDegree = m) (hj : j ≤ m) :
    Q.hasseDeriv (m - j) ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun R : ℂ[X] ↦ R.coeff j) hzero
  rw [hasseDeriv_coeff, coeff_zero] at hcoeff
  have hadd : j + (m - j) = m := Nat.add_sub_of_le hj
  have hcoeffm : Q.coeff m = Q.leadingCoeff := by
    rw [← hm, coeff_natDegree]
  rw [hadd, hcoeffm] at hcoeff
  have hchooseNat : 0 < m.choose (m - j) :=
    Nat.choose_pos (Nat.sub_le m j)
  have hchoose : ((m.choose (m - j) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hchooseNat.ne'
  exact mul_ne_zero hchoose (leadingCoeff_ne_zero.mpr hQ) hcoeff

/-- Construct a consecutive-degree evaluation family from the top Hasse
derivatives of a fixed polynomial.  The row labelled `j` has complementary
order `m - j`, hence is a polynomial of degree `j`.  The derivatives are
normalized to monic polynomials; their removed leading coefficients are
retained as nonzero row scales.  This generic construction must only be used
when the derivatives in the relation really have complementary orders. -/
def ofTopHasse (Q : ℂ[X]) (m n : ℕ)
    (hQ : Q ≠ 0) (hm : Q.natDegree = m) (hn : n ≤ m)
    (node : Fin (n + 1) → ℂ) (node_injective : Function.Injective node)
    (columnScale : Fin (n + 1) → ℂ)
    (columnScale_ne_zero : ∀ j, columnScale j ≠ 0) :
    EliminationFamily n where
  polynomial j :=
    let q := Q.hasseDeriv (m - (j : ℕ))
    C (q.leadingCoeff⁻¹) * q
  node := node
  rowScale j := (Q.hasseDeriv (m - (j : ℕ))).leadingCoeff
  columnScale := columnScale
  node_injective := node_injective
  rowScale_ne_zero j := leadingCoeff_ne_zero.mpr
    (topHasse_ne_zero Q hQ hm ((Nat.le_of_lt_succ j.isLt).trans hn))
  columnScale_ne_zero := columnScale_ne_zero
  degree j := by
    have hj : (j : ℕ) ≤ m := (Nat.le_of_lt_succ j.isLt).trans hn
    have hne := topHasse_ne_zero Q hQ hm hj
    rw [natDegree_C_mul (inv_ne_zero (leadingCoeff_ne_zero.mpr hne)),
      natDegree_hasseDeriv, hm]
    omega
  monic j := by
    have hj : (j : ℕ) ≤ m := (Nat.le_of_lt_succ j.isLt).trans hn
    have hne := topHasse_ne_zero Q hQ hm hj
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    exact inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hne)

@[simp] theorem ofTopHasse_matrix_apply (Q : ℂ[X]) (m n : ℕ)
    (hQ : Q ≠ 0) (hm : Q.natDegree = m) (hn : n ≤ m)
    (node : Fin (n + 1) → ℂ) (node_injective : Function.Injective node)
    (columnScale : Fin (n + 1) → ℂ)
    (columnScale_ne_zero : ∀ j, columnScale j ≠ 0)
    (r c : Fin (n + 1)) :
    (ofTopHasse Q m n hQ hm hn node node_injective columnScale
      columnScale_ne_zero).matrix r c =
      (Q.hasseDeriv (m - (r : ℕ))).eval (node c) * columnScale c := by
  have hr : (r : ℕ) ≤ m := (Nat.le_of_lt_succ r.isLt).trans hn
  have hne := topHasse_ne_zero Q hQ hm hr
  simp only [matrix, ofTopHasse, Matrix.of_apply, eval_mul, eval_C]
  rw [← mul_assoc, mul_inv_cancel₀ (leadingCoeff_ne_zero.mpr hne), one_mul]

/-- Normalize any nonzero consecutive-degree polynomial family while
retaining its leading coefficients as row scales. -/
def ofConsecutive {n : ℕ} (Q : Fin (n + 1) → ℂ[X])
    (hQ : ∀ j, Q j ≠ 0) (hdegree : ∀ j, (Q j).natDegree = (j : ℕ))
    (node : Fin (n + 1) → ℂ) (node_injective : Function.Injective node)
    (columnScale : Fin (n + 1) → ℂ)
    (columnScale_ne_zero : ∀ j, columnScale j ≠ 0) :
    EliminationFamily n where
  polynomial j := C ((Q j).leadingCoeff⁻¹) * Q j
  node := node
  rowScale j := (Q j).leadingCoeff
  columnScale := columnScale
  node_injective := node_injective
  rowScale_ne_zero j := leadingCoeff_ne_zero.mpr (hQ j)
  columnScale_ne_zero := columnScale_ne_zero
  degree j := by
    rw [natDegree_C_mul
      (inv_ne_zero (leadingCoeff_ne_zero.mpr (hQ j))), hdegree]
  monic j := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    exact inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr (hQ j))

@[simp] theorem ofConsecutive_matrix_apply {n : ℕ}
    (Q : Fin (n + 1) → ℂ[X])
    (hQ : ∀ j, Q j ≠ 0) (hdegree : ∀ j, (Q j).natDegree = (j : ℕ))
    (node : Fin (n + 1) → ℂ) (node_injective : Function.Injective node)
    (columnScale : Fin (n + 1) → ℂ)
    (columnScale_ne_zero : ∀ j, columnScale j ≠ 0)
    (r c : Fin (n + 1)) :
    (ofConsecutive Q hQ hdegree node node_injective columnScale
      columnScale_ne_zero).matrix r c =
      (Q r).eval (node c) * columnScale c := by
  simp only [matrix, ofConsecutive, Matrix.of_apply, eval_mul, eval_C]
  rw [← mul_assoc,
    mul_inv_cancel₀ (leadingCoeff_ne_zero.mpr (hQ r)), one_mul]

end EliminationFamily

/-! ## Context-dependent repeated elimination

The matrices in the source's equation (14) are used one old exponent at a
time.  At a given step the matrix is allowed to depend on every exponent
which is not currently being eliminated (and, in applications, also on the
rational node and the remaining derivative indices).  Encoding that
dependence is important: a single fixed tensor product is stronger than the
source construction and is not needed for the argument. -/

/-- The exact datum needed by determinant elimination: a square matrix and
a proof that it is nonsingular.  Keeping this separate from
`EliminationFamily` allows source-specific collocation theorems whose rows
are not a generic consecutive-degree polynomial basis. -/
structure NonsingularFamily (n : ℕ) where
  matrix : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ
  det_ne_zero : matrix.det ≠ 0

namespace EliminationFamily

/-- Every consecutive-degree evaluation family supplies a nonsingular
matrix family. -/
def toNonsingular {n : ℕ} (E : EliminationFamily n) :
    NonsingularFamily n where
  matrix := E.matrix
  det_ne_zero := E.det_matrix_ne_zero

@[simp] theorem toNonsingular_matrix {n : ℕ} (E : EliminationFamily n) :
    E.toNonsingular.matrix = E.matrix := rfl

end EliminationFamily

/-- A consecutive-degree family for coordinate `i` which is constant when
only coordinate `i` is changed.  Thus `family row` may depend on all the
*other* coordinates. -/
structure ContextualEliminationFamily
    {I : Type u} [Fintype I] [DecidableEq I]
    (side : I → ℕ) (i : I) where
  family : (∀ j, Fin (side j + 1)) → NonsingularFamily (side i)
  matrix_update : ∀ (row : ∀ j, Fin (side j + 1))
      (a : Fin (side i + 1)),
    (family (Function.update row i a)).matrix = (family row).matrix

namespace ContextualEliminationFamily

/-- A fixed equation-(14) family is, in particular, contextual. -/
def const
    {I : Type u} [Fintype I] [DecidableEq I]
    {side : I → ℕ} {i : I} (E : EliminationFamily (side i)) :
    ContextualEliminationFamily side i where
  family := fun _ ↦ E.toNonsingular
  matrix_update := by intros; rfl

/-- A fixed source-specific nonsingular matrix is contextual. -/
def constNonsingular
    {I : Type u} [Fintype I] [DecidableEq I]
    {side : I → ℕ} {i : I} (E : NonsingularFamily (side i)) :
    ContextualEliminationFamily side i where
  family := fun _ ↦ E
  matrix_update := by intros; rfl

/-- Apply one equation-(14) matrix in coordinate `i`. -/
def eliminateCoordinate
    {I : Type u} [Fintype I] [DecidableEq I]
    {side : I → ℕ} {i : I}
    (E : ContextualEliminationFamily side i)
    (v : (∀ j, Fin (side j + 1)) → ℂ)
    (row : ∀ j, Fin (side j + 1)) : ℂ :=
  ∑ a : Fin (side i + 1),
    (E.family row).matrix (row i) a * v (Function.update row i a)

/-- One contextual equation-(14) elimination is injective. -/
theorem eq_zero_of_eliminateCoordinate_eq_zero
    {I : Type u} [Fintype I] [DecidableEq I]
    {side : I → ℕ} {i : I}
    (E : ContextualEliminationFamily side i)
    (v : (∀ j, Fin (side j + 1)) → ℂ)
    (hzero : eliminateCoordinate E v = 0) : v = 0 := by
  funext row
  let w : Fin (side i + 1) → ℂ :=
    fun a ↦ v (Function.update row i a)
  have hmul : (E.family row).matrix.mulVec w = 0 := by
    funext r
    have hr := congrFun hzero (Function.update row i r)
    simp only [eliminateCoordinate, Pi.zero_apply] at hr ⊢
    rw [E.matrix_update row r] at hr
    simpa only [Matrix.mulVec, dotProduct, w, Function.update_self,
      Function.update_idem] using hr
  have hw : w = 0 := Matrix.eq_zero_of_mulVec_eq_zero
    (E.family row).det_ne_zero hmul
  have hentry := congrFun hw (row i)
  simpa only [w, Function.update_eq_self, Pi.zero_apply] using hentry

@[simp] theorem eliminateCoordinate_zero
    {I : Type u} [Fintype I] [DecidableEq I]
    {side : I → ℕ} {i : I}
    (E : ContextualEliminationFamily side i) :
    eliminateCoordinate E (0 : (∀ j, Fin (side j + 1)) → ℂ) = 0 := by
  funext row
  simp [eliminateCoordinate]

end ContextualEliminationFamily

/-- Apply a list of contextual eliminations.  No commutativity between the
steps is assumed or needed. -/
def eliminateCoordinates
    {I : Type u} [Fintype I] [DecidableEq I]
    {side : I → ℕ}
    (E : ∀ i, ContextualEliminationFamily side i) :
    List I → ((∀ j, Fin (side j + 1)) → ℂ) →
      ((∀ j, Fin (side j + 1)) → ℂ)
  | [], v => v
  | i :: is, v => eliminateCoordinates E is
      ((E i).eliminateCoordinate v)

/-- Repeated contextual equation-(14) elimination is injective. -/
theorem eq_zero_of_eliminateCoordinates_eq_zero
    {I : Type u} [Fintype I] [DecidableEq I]
    {side : I → ℕ}
    (E : ∀ i, ContextualEliminationFamily side i)
    (order : List I) (v : (∀ j, Fin (side j + 1)) → ℂ)
    (hzero : eliminateCoordinates E order v = 0) : v = 0 := by
  induction order generalizing v with
  | nil => simpa only [eliminateCoordinates] using hzero
  | cons i is ih =>
      apply (E i).eq_zero_of_eliminateCoordinate_eq_zero
      exact ih ((E i).eliminateCoordinate v)
        (by simpa only [eliminateCoordinates] using hzero)

@[simp] theorem eliminateCoordinates_zero
    {I : Type u} [Fintype I] [DecidableEq I]
    {side : I → ℕ}
    (E : ∀ i, ContextualEliminationFamily side i) (order : List I) :
    eliminateCoordinates E order
      (0 : (∀ j, Fin (side j + 1)) → ℂ) = 0 := by
  induction order with
  | nil => rfl
  | cons i is ih =>
      simpa only [eliminateCoordinates,
        ContextualEliminationFamily.eliminateCoordinate_zero] using ih

/-! ## The corrected terminal box and equation (13) -/

/-- `floor(q^(-J) L)` for an integral side length. -/
def scaledSide (q J L : ℕ) : ℕ := L / q ^ J

/-- The level-`J` coefficient box.  In particular, the varying last exponent
is retained as `lastMax`; omitting it loses a whole source coordinate. -/
def terminalBox {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) (J : ℕ) : BoxShape (Fintype.card ι) where
  shiftMax := P.LminusOne
  deltaMax := P.Lzero
  oldMax := fun r ↦ scaledSide P.q J (P.LiZero ((Fintype.equivFin ι).symm r))
  lastMax := scaledSide P.q J P.LlastZero

@[simp] theorem terminalBox_shiftMax {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) (J : ℕ) :
    (terminalBox P J).shiftMax = P.LminusOne := rfl

@[simp] theorem terminalBox_deltaMax {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) (J : ℕ) :
    (terminalBox P J).deltaMax = P.Lzero := rfl

@[simp] theorem terminalBox_lastMax {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) (J : ℕ) :
    (terminalBox P J).lastMax = scaledSide P.q J P.LlastZero := rfl

/-- The source-faithful strict terminal lower bound collapses the varying
last exponent side.  This is deliberately stated using the real, unfloored
scale from the parameter choice. -/
theorem terminalBox_lastMax_eq_zero_of_scale_lt_qpow
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (P : VDPLParameters ι) {J : ℕ}
    (hterminal : P.LlastZeroScale < ((P.q ^ J : ℕ) : ℝ)) :
    (terminalBox P J).lastMax = 0 := by
  rw [terminalBox_lastMax]
  apply Nat.div_eq_of_lt
  exact_mod_cast lt_of_le_of_lt P.LlastZero_cast_le hterminal

abbrev TerminalOldExponent {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) (J : ℕ) :=
  ∀ r : Fin (Fintype.card ι), Fin ((terminalBox P J).oldMax r + 1)

abbrev TerminalLastExponent {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) (J : ℕ) :=
  Fin ((terminalBox P J).lastMax + 1)

/-- The canonical last exponent.  At the terminal level the collapse lemma
shows that it is the only one. -/
def terminalLastZero {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) (J : ℕ) : TerminalLastExponent P J :=
  ⟨0, Nat.succ_pos _⟩

theorem terminalLastExponent_eq_zero_of_scale_lt_qpow
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (P : VDPLParameters ι) {J : ℕ}
    (hterminal : P.LlastZeroScale < ((P.q ^ J : ℕ) : ℝ))
    (last : TerminalLastExponent P J) : last = terminalLastZero P J := by
  apply Fin.ext
  have hmax := terminalBox_lastMax_eq_zero_of_scale_lt_qpow P hterminal
  have hlt := last.isLt
  simp only [hmax, Nat.zero_add, Nat.lt_one_iff] at hlt
  exact hlt

def poweredDeltaComplex (h lambda : ℕ) : ℂ[X] :=
  (poweredDelta h lambda).map (algebraMap ℚ ℂ)

theorem natDegree_delta (h : ℕ) :
    (Erdos240Delta.delta h).natDegree = h := by
  unfold Erdos240Delta.delta Erdos240Delta.deltaNumerator
  rw [natDegree_C_mul (by positivity),
    natDegree_map_eq_of_injective Int.cast_injective,
    Erdos240Delta.natDegree_deltaNumeratorInt]

theorem natDegree_poweredDelta (h lambda : ℕ) :
    (poweredDelta h lambda).natDegree = h * lambda := by
  simp only [poweredDelta, natDegree_pow, natDegree_delta, Nat.mul_comm]

theorem natDegree_poweredDeltaComplex (h lambda : ℕ) :
    (poweredDeltaComplex h lambda).natDegree = h * lambda := by
  rw [poweredDeltaComplex,
    natDegree_map_eq_of_injective (algebraMap ℚ ℂ).injective,
    natDegree_poweredDelta]

/-- The source's two-argument old-coordinate polynomial
`Δ(X;m) = (X+1)⋯(X+m)/m!`, mapped to `ℂ`.  This is distinct from the
four-argument powered derivative used in the head coordinate. -/
def ordinaryDeltaComplex (m : ℕ) : ℂ[X] :=
  (Erdos240Delta.delta m).map (algebraMap ℚ ℂ)

theorem natDegree_ordinaryDeltaComplex (m : ℕ) :
    (ordinaryDeltaComplex m).natDegree = m := by
  rw [ordinaryDeltaComplex,
    natDegree_map_eq_of_injective (algebraMap ℚ ℂ).injective,
    natDegree_delta]

theorem ordinaryDeltaComplex_ne_zero (m : ℕ) :
    ordinaryDeltaComplex m ≠ 0 := by
  intro hzero
  cases m with
  | zero =>
      simpa [ordinaryDeltaComplex, Erdos240Delta.delta,
        Erdos240Delta.deltaNumerator, Erdos240Delta.deltaNumeratorInt] using hzero
  | succ m =>
      have hdegree := natDegree_ordinaryDeltaComplex (m + 1)
      rw [hzero, natDegree_zero] at hdegree
      omega

theorem poweredDeltaComplex_ne_zero_of_pos {h lambda : ℕ} (hh : 0 < h) :
    poweredDeltaComplex h lambda ≠ 0 := by
  intro hzero
  cases lambda with
  | zero =>
      simpa [poweredDeltaComplex, poweredDelta] using hzero
  | succ lambda =>
      have hdegree := natDegree_poweredDeltaComplex h (lambda + 1)
      rw [hzero, natDegree_zero] at hdegree
      have hpositive : 0 < h * (lambda + 1) :=
        Nat.mul_pos hh (Nat.succ_pos lambda)
      omega

namespace EliminationFamily

/-- The literal equation-(14) family.  Its row `m` is the ordinary
two-argument polynomial `Δ(X;m)`, evaluated at the arithmetic node
`bLast * lambda`; hence the rows have consecutive degrees `0,…,L` and the
matrix is a scaled Vandermonde matrix. -/
def ofOrdinaryDelta (L : ℕ) (bLast : ℂ) (hbLast : bLast ≠ 0)
    (columnScale : Fin (L + 1) → ℂ)
    (columnScale_ne_zero : ∀ j, columnScale j ≠ 0) :
    EliminationFamily L :=
  ofConsecutive (fun j ↦ ordinaryDeltaComplex (j : ℕ))
    (fun j ↦ ordinaryDeltaComplex_ne_zero (j : ℕ))
    (fun j ↦ natDegree_ordinaryDeltaComplex (j : ℕ))
    (fun j ↦ bLast * (j : ℕ))
    (by
      intro i j hij
      apply Fin.ext
      have hcast : (((i : ℕ) : ℂ)) = (((j : ℕ) : ℂ)) :=
        mul_left_cancel₀ hbLast hij
      exact_mod_cast hcast)
    columnScale columnScale_ne_zero

@[simp] theorem ofOrdinaryDelta_matrix_apply
    (L : ℕ) (bLast : ℂ) (hbLast : bLast ≠ 0)
    (columnScale : Fin (L + 1) → ℂ)
    (columnScale_ne_zero : ∀ j, columnScale j ≠ 0)
    (r c : Fin (L + 1)) :
    (ofOrdinaryDelta L bLast hbLast columnScale
      columnScale_ne_zero).matrix r c =
      (ordinaryDeltaComplex (r : ℕ)).eval (bLast * (c : ℕ)) *
        columnScale c := by
  exact ofConsecutive_matrix_apply
    (fun j : Fin (L + 1) ↦ ordinaryDeltaComplex (j : ℕ))
    (fun j ↦ ordinaryDeltaComplex_ne_zero (j : ℕ))
    (fun j ↦ natDegree_ordinaryDeltaComplex (j : ℕ))
    (fun j ↦ bLast * (j : ℕ))
    (by
      intro i j hij
      apply Fin.ext
      have hcast : (((i : ℕ) : ℂ)) = (((j : ℕ) : ℂ)) :=
        mul_left_cancel₀ hbLast hij
      exact_mod_cast hcast)
    columnScale columnScale_ne_zero r c

/-- The complementary-Hasse evaluation family for the fixed side power
`Δ(X;h)^L`.  Its row labelled `j` has Hasse order `h * L - j`, so its
residual degree is `j`.  The optional nonzero column scale can record an
additional exponential monomial. -/
def ofPoweredDeltaTopHasse (h L : ℕ) (hh : 0 < h)
    (node : Fin (L + 1) → ℂ) (node_injective : Function.Injective node)
    (columnScale : Fin (L + 1) → ℂ)
    (columnScale_ne_zero : ∀ j, columnScale j ≠ 0) :
    EliminationFamily L :=
  ofTopHasse (poweredDeltaComplex h L) (h * L) L
    (poweredDeltaComplex_ne_zero_of_pos hh)
    (natDegree_poweredDeltaComplex h L)
    (by
      calc
        L = 1 * L := by simp
        _ ≤ h * L := Nat.mul_le_mul_right L hh)
    node node_injective columnScale columnScale_ne_zero

@[simp] theorem ofPoweredDeltaTopHasse_matrix_apply
    (h L : ℕ) (hh : 0 < h)
    (node : Fin (L + 1) → ℂ) (node_injective : Function.Injective node)
    (columnScale : Fin (L + 1) → ℂ)
    (columnScale_ne_zero : ∀ j, columnScale j ≠ 0)
    (r c : Fin (L + 1)) :
    (ofPoweredDeltaTopHasse h L hh node node_injective columnScale
      columnScale_ne_zero).matrix r c =
      ((poweredDeltaComplex h L).hasseDeriv (h * L - (r : ℕ))).eval
        (node c) * columnScale c := by
  exact ofTopHasse_matrix_apply (poweredDeltaComplex h L) (h * L) L
    (poweredDeltaComplex_ne_zero_of_pos hh)
    (natDegree_poweredDeltaComplex h L)
    (by
      calc
        L = 1 * L := by simp
        _ ≤ h * L := Nat.mul_le_mul_right L hh)
    node node_injective columnScale columnScale_ne_zero r c

end EliminationFamily

/-- The one-variable polynomial denoted `P(z)` after all old-coordinate
determinants have been eliminated. -/
def terminalPolynomial {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) (J : ℕ)
    (c : LambdaBox (terminalBox P J) → ℂ)
    (old : TerminalOldExponent P J) (last : TerminalLastExponent P J) : ℂ[X] :=
  ∑ d : Fin (P.Lzero + 1), ∑ s : Fin (P.LminusOne + 1),
    c ⟨s, d, old, last⟩ • (poweredDeltaComplex P.h (d + 1)).taylor (s : ℂ)

/-- The active terminal coefficient box.  Lemma 6 may shrink the old sides
more than the canonical quotient in `terminalBox`; the final argument only
needs those actual sides.  The last side is a singleton after the terminal
collapse, while the shift and Delta-power sides retain their initial
values. -/
def activeTerminalBox {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι)
    (oldSide : Fin (Fintype.card ι) → ℕ) : BoxShape (Fintype.card ι) where
  shiftMax := P.LminusOne
  deltaMax := P.Lzero
  oldMax := oldSide
  lastMax := 0

abbrev ActiveTerminalOldExponent {ι : Type u} [Fintype ι]
    (oldSide : Fin (Fintype.card ι) → ℕ) :=
  ∀ r, Fin (oldSide r + 1)

def activeTerminalLastZero {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι)
    (oldSide : Fin (Fintype.card ι) → ℕ) :
    Fin ((activeTerminalBox P oldSide).lastMax + 1) :=
  ⟨0, by simp [activeTerminalBox]⟩

/-- The one-variable polynomial after the actual old sides have been
eliminated. -/
def activeTerminalPolynomial {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι)
    (oldSide : Fin (Fintype.card ι) → ℕ)
    (c : LambdaBox (activeTerminalBox P oldSide) → ℂ)
    (old : ActiveTerminalOldExponent oldSide) : ℂ[X] :=
  ∑ d : Fin (P.Lzero + 1), ∑ s : Fin (P.LminusOne + 1),
    c ⟨s, d, old, activeTerminalLastZero P oldSide⟩ •
      (poweredDeltaComplex P.h (d + 1)).taylor (s : ℂ)

/-! ## Lemma 7 removes the remaining shift/Delta box -/

/-- Lemma 7 with an arbitrary low-degree remainder in place of its monomial
coordinates. -/
theorem shifted_relation_with_low_degree
    {K : Type*} [Field K] [CharZero K]
    (Q R : K[X]) {m t : ℕ}
    (hm_pos : 0 < m) (hm : Q.natDegree = m) (ht : t ≤ m)
    (a : Fin (t + 1) → K) (hR : R.natDegree < m - t)
    (hrel : (∑ i, a i • Q.taylor (i : K)) + R = 0) :
    a = 0 ∧ R = 0 := by
  let b : Fin (m - t) → K := fun j ↦ R.coeff j
  have hRsum : ∑ j, b j • X ^ (j : ℕ) = R := by
    calc
      ∑ j, b j • X ^ (j : ℕ) =
          ∑ i ∈ Finset.range (m - t), C (R.coeff i) * X ^ i := by
        simpa only [b, smul_eq_C_mul] using
          (Fin.sum_univ_eq_sum_range
            (fun i ↦ C (R.coeff i) * X ^ i) (m - t))
      _ = R := (R.as_sum_range_C_mul_X_pow' hR).symm
  have h := shiftedPolynomial_relation Q hm_pos hm ht a b (by
    rwa [hRsum])
  refine ⟨h.1, ?_⟩
  rw [← hRsum, h.2]
  simp

/-- The final two coefficient coordinates are faithful: if the polynomial
formed from all shifts of all powered Deltas is zero, every coefficient is
zero.  The induction removes the largest Delta power using Lemma 7; all lower
powers form the permitted low-degree remainder. -/
theorem shifted_poweredDelta_coefficients_eq_zero
    (h t dMax : ℕ) (hh : 0 < h) (ht : t < h)
    (c : Fin (dMax + 1) → Fin (t + 1) → ℂ)
    (hzero : ∑ d, ∑ s, c d s •
      (poweredDeltaComplex h (d + 1)).taylor (s : ℂ) = 0) :
    c = 0 := by
  induction dMax with
  | zero =>
      have hdegree : (poweredDeltaComplex h 1).natDegree = h := by
        simpa using natDegree_poweredDeltaComplex h 1
      have hrel := shifted_relation_with_low_degree
        (poweredDeltaComplex h 1) 0 hh hdegree ht.le (fun s ↦ c 0 s)
        (by simp; omega) (by simpa using hzero)
      funext d s
      have hd : d = 0 := Fin.eq_zero d
      subst d
      exact congrFun hrel.1 s
  | succ d ih =>
      let top : Fin (d + 2) := Fin.last (d + 1)
      let lower : ℂ[X] :=
        ∑ j : Fin (d + 1), ∑ s : Fin (t + 1),
          c j.castSucc s •
            (poweredDeltaComplex h (j.castSucc + 1)).taylor (s : ℂ)
      have hlowerDegree : lower.natDegree ≤ h * (d + 1) := by
        unfold lower
        apply natDegree_sum_le_of_forall_le Finset.univ
        intro j _
        apply natDegree_sum_le_of_forall_le Finset.univ
        intro s _
        calc
          (c j.castSucc s •
              (poweredDeltaComplex h (j.castSucc + 1)).taylor (s : ℂ)).natDegree
              ≤ ((poweredDeltaComplex h (j.castSucc + 1)).taylor
                    (s : ℂ)).natDegree := natDegree_smul_le _ _
          _ = (poweredDeltaComplex h (j.castSucc + 1)).natDegree :=
            natDegree_taylor _ _
          _ = h * ((j : ℕ) + 1) := by
            rw [natDegree_poweredDeltaComplex]
            rfl
          _ ≤ h * (d + 1) := Nat.mul_le_mul_left h (Nat.succ_le_iff.mpr j.isLt)
      have htopDegree :
          (poweredDeltaComplex h (d + 2)).natDegree = h * (d + 2) :=
        natDegree_poweredDeltaComplex _ _
      have hlow : lower.natDegree < h * (d + 2) - t := by
        have hident : h * (d + 2) = h * (d + 1) + h := by ring
        have : h * (d + 1) < h * (d + 2) - t := by
          rw [Nat.lt_sub_iff_add_lt, hident]
          omega
        exact hlowerDegree.trans_lt this
      have hsplit :
          (∑ s : Fin (t + 1), c top s •
              (poweredDeltaComplex h (d + 2)).taylor (s : ℂ)) + lower = 0 := by
        have hzero' := hzero
        conv at hzero' =>
          lhs
          rw [Fin.sum_univ_castSucc]
        simpa only [lower, top, Fin.val_last, Fin.val_castSucc,
          Nat.add_assoc, Nat.reduceAdd, Nat.add_comm, Nat.add_left_comm,
          add_comm] using hzero'
      have htop := shifted_relation_with_low_degree
        (poweredDeltaComplex h (d + 2)) lower
        (Nat.mul_pos hh (by omega)) htopDegree
        (by omega : t ≤ h * (d + 2)) (fun s ↦ c top s) hlow hsplit
      let cLower : Fin (d + 1) → Fin (t + 1) → ℂ :=
        fun j s ↦ c j.castSucc s
      have hcLower : cLower = 0 := by
        apply ih cLower
        change (∑ j : Fin (d + 1), ∑ s : Fin (t + 1),
          c j.castSucc s •
            (poweredDeltaComplex h ((j : ℕ) + 1)).taylor (s : ℂ)) = 0
        simpa only [cLower, lower, Fin.val_castSucc] using htop.2
      funext j s
      refine Fin.lastCases ?_ (fun j ↦ ?_) j
      · exact congrFun htop.1 s
      · exact congrFun (congrFun hcLower j) s

/-- The degree bound used immediately before equation (16). -/
theorem natDegree_terminalPolynomial_le
    {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) (J : ℕ)
    (c : LambdaBox (terminalBox P J) → ℂ)
    (old : TerminalOldExponent P J) (last : TerminalLastExponent P J) :
    (terminalPolynomial P J c old last).natDegree ≤
      P.h * P.LzeroPlusOne := by
  unfold terminalPolynomial
  apply natDegree_sum_le_of_forall_le Finset.univ
  intro d _
  apply natDegree_sum_le_of_forall_le Finset.univ
  intro s _
  calc
    (c ⟨s, d, old, last⟩ •
        (poweredDeltaComplex P.h (d + 1)).taylor (s : ℂ)).natDegree ≤
        ((poweredDeltaComplex P.h (d + 1)).taylor (s : ℂ)).natDegree :=
      natDegree_smul_le _ _
    _ = (poweredDeltaComplex P.h (d + 1)).natDegree := natDegree_taylor _ _
    _ = P.h * ((d : ℕ) + 1) := by rw [natDegree_poweredDeltaComplex]
    _ ≤ P.h * P.LzeroPlusOne := by
      apply Nat.mul_le_mul_left
      simpa [P.Lzero_add_one_eq_LzeroPlusOne] using d.isLt

theorem natDegree_activeTerminalPolynomial_le
    {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι)
    (oldSide : Fin (Fintype.card ι) → ℕ)
    (c : LambdaBox (activeTerminalBox P oldSide) → ℂ)
    (old : ActiveTerminalOldExponent oldSide) :
    (activeTerminalPolynomial P oldSide c old).natDegree ≤
      P.h * P.LzeroPlusOne := by
  unfold activeTerminalPolynomial
  apply natDegree_sum_le_of_forall_le Finset.univ
  intro d _
  apply natDegree_sum_le_of_forall_le Finset.univ
  intro s _
  calc
    (c ⟨s, d, old, activeTerminalLastZero P oldSide⟩ •
        (poweredDeltaComplex P.h (d + 1)).taylor (s : ℂ)).natDegree ≤
        ((poweredDeltaComplex P.h (d + 1)).taylor (s : ℂ)).natDegree :=
      natDegree_smul_le _ _
    _ = (poweredDeltaComplex P.h (d + 1)).natDegree := natDegree_taylor _ _
    _ = P.h * ((d : ℕ) + 1) := by rw [natDegree_poweredDeltaComplex]
    _ ≤ P.h * P.LzeroPlusOne := by
      apply Nat.mul_le_mul_left
      simpa [P.Lzero_add_one_eq_LzeroPlusOne] using d.isLt

/-! ## The rational nodes and the exact multiplicity count (16) -/

/-- Complete nonzero residue blocks modulo `q` contained in the level-`N`
radius.  The assumption `0 < N` is obtained below from maximality. -/
abbrev TerminalNode {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) (N : ℕ) :=
  Fin (16 * P.q ^ (N - 1) * P.h) × Fin (P.q - 1)

def terminalNodeNumerator {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) {N : ℕ} (x : TerminalNode P N) : ℕ :=
  x.1 * P.q + (x.2 + 1)

def terminalNodeValue {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) {N : ℕ} (x : TerminalNode P N) : ℂ :=
  (terminalNodeNumerator P x : ℂ) / (P.q ^ N : ℕ)

theorem terminalNodeNumerator_pos {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) {N : ℕ} (x : TerminalNode P N) :
    0 < terminalNodeNumerator P x := by
  unfold terminalNodeNumerator
  omega

/-- Every displayed node lies in a nonzero residue class modulo the source
prime.  Thus it is among the `(ell,q)=1` points for which equation (13) is
available. -/
theorem q_not_dvd_terminalNodeNumerator {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) {N : ℕ} (x : TerminalNode P N) :
    ¬ P.q ∣ terminalNodeNumerator P x := by
  intro hdvd
  obtain ⟨a, ha⟩ := hdvd
  have hr : (x.2 : ℕ) < 12 := by
    simpa only [VDPLParameters.q, Nat.reduceSub] using x.2.isLt
  simp only [terminalNodeNumerator, VDPLParameters.q] at ha
  omega

theorem terminalNodeNumerator_coprime_q {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) {N : ℕ} (x : TerminalNode P N) :
    Nat.Coprime (terminalNodeNumerator P x) P.q := by
  rw [Nat.coprime_comm]
  by_contra hnot
  exact q_not_dvd_terminalNodeNumerator P x
    (P.q_prime.dvd_iff_not_coprime.mpr hnot)

theorem terminalNodeNumerator_le_radius
    {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) {N : ℕ} (hN : 0 < N)
    (x : TerminalNode P N) : terminalNodeNumerator P x ≤ P.R N := by
  have hres : (x.2 : ℕ) + 1 ≤ P.q := by
    have hx := x.2.isLt
    omega
  have hblock : (x.1 : ℕ) < 16 * P.q ^ (N - 1) * P.h := x.1.isLt
  have hqpos : 0 < P.q := Nat.zero_lt_of_lt P.one_lt_q
  have hmul : (x.1 : ℕ) * P.q + ((x.2 : ℕ) + 1) ≤
      (16 * P.q ^ (N - 1) * P.h) * P.q := by
    calc
      (x.1 : ℕ) * P.q + ((x.2 : ℕ) + 1) ≤
          (x.1 : ℕ) * P.q + P.q := Nat.add_le_add_left hres _
      _ = ((x.1 : ℕ) + 1) * P.q := by rw [Nat.add_mul, one_mul]
      _ ≤ (16 * P.q ^ (N - 1) * P.h) * P.q :=
        Nat.mul_le_mul_right P.q (Nat.succ_le_iff.mpr hblock)
  have hpow : P.q ^ N = P.q ^ (N - 1) * P.q := by
    conv_lhs => rw [show N = (N - 1) + 1 by omega]
    exact pow_succ _ _
  calc
    terminalNodeNumerator P x ≤
        (16 * P.q ^ (N - 1) * P.h) * P.q := hmul
    _ = P.R N := by
      unfold VDPLParameters.R
      rw [hpow]
      ac_rfl

theorem terminalNodeNumerator_injective
    {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) {N : ℕ} :
    Function.Injective (terminalNodeNumerator P : TerminalNode P N → ℕ) := by
  intro x y hxy
  have hx : (x.2 : ℕ) < 12 := by simpa [VDPLParameters.q] using x.2.isLt
  have hy : (y.2 : ℕ) < 12 := by simpa [VDPLParameters.q] using y.2.isLt
  simp only [terminalNodeNumerator, VDPLParameters.q] at hxy
  apply Prod.ext
  · apply Fin.ext
    omega
  · apply Fin.ext
    omega

theorem terminalNodeValue_injective
    {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) {N : ℕ} :
    Function.Injective (terminalNodeValue P : TerminalNode P N → ℂ) := by
  intro x y hxy
  apply terminalNodeNumerator_injective P
  unfold terminalNodeValue at hxy
  have hden : (P.q : ℂ) ^ N ≠ 0 :=
    pow_ne_zero N (by exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q))
  have hxy' : (terminalNodeNumerator P x : ℂ) / (P.q : ℂ) ^ N =
      (terminalNodeNumerator P y : ℂ) / (P.q : ℂ) ^ N := by
    simpa using hxy
  have hcast := (div_left_inj' hden).mp hxy'
  exact_mod_cast hcast

/-- The inclusive derivative range in (15). -/
def terminalMultiplicity {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) (N : ℕ) : ℕ :=
  ⌊P.levelScale N / 8⌋₊ + 1

theorem levelScale_div_eight_lt_terminalMultiplicity
    {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) [Nonempty ι] (N : ℕ) :
    P.levelScale N / 8 < terminalMultiplicity P N := by
  simpa only [terminalMultiplicity, Nat.cast_add, Nat.cast_one] using
    (Nat.lt_floor_add_one (P.levelScale N / 8))

theorem one_le_Omega {ι : Type u} [Fintype ι] [Nonempty ι]
    (P : VDPLParameters ι) : 1 ≤ P.Omega := by
  have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hOld : (2 : ℝ) ≤ P.OmegaOld := by
    have hpowNat : 2 ≤ 2 ^ Fintype.card ι := by
      exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hcard
    calc
      (2 : ℝ) ≤ (2 : ℝ) ^ Fintype.card ι := by exact_mod_cast hpowNat
      _ ≤ P.OmegaOld := P.two_pow_card_le_OmegaOld
  have hNew : (2 : ℝ) ≤ Real.log P.newHeight :=
    Real.exp_one_gt_two.le.trans P.exp_one_le_log_newHeight
  unfold VDPLParameters.Omega
  nlinarith [mul_le_mul hOld hNew (by norm_num : (0 : ℝ) ≤ 2)
    (P.OmegaOld_pos.le)]

theorem half_lt_Omega_mul_logOmegaOld
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (P : VDPLParameters ι) :
    (1 / 2 : ℝ) < P.Omega * Real.log P.OmegaOld := by
  have hlog : (1 / 2 : ℝ) < Real.log P.OmegaOld :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
      (Real.log_two_gt_d9.trans_le P.log_two_le_log_OmegaOld)
  calc
    (1 / 2 : ℝ) ≤ P.Omega * (1 / 2) := by
      nlinarith [one_le_Omega P]
    _ < P.Omega * Real.log P.OmegaOld :=
      mul_lt_mul_of_pos_left hlog P.Omega_pos

/-- Exact numerical content of (16): the displayed complete residue blocks,
each with the inclusive derivative range from (15), have total multiplicity
strictly larger than the degree bound `h*(L_0+1)`. -/
theorem terminal_degree_lt_count
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (P : VDPLParameters ι) {N : ℕ} (hN : 0 < N) :
    P.h * P.LzeroPlusOne <
      Fintype.card (TerminalNode P N) * terminalMultiplicity P N := by
  have hqpowNat : 0 < P.q ^ (N - 1) :=
    pow_pos (Nat.zero_lt_of_lt P.one_lt_q) _
  have hqpow : (0 : ℝ) < (P.q ^ (N - 1) : ℕ) := by exact_mod_cast hqpowNat
  have hh : (0 : ℝ) < P.h := by exact_mod_cast P.h_pos
  have hnodes : (0 : ℝ) < Fintype.card (TerminalNode P N) := by
    have hblocks : 0 < 16 * P.q ^ (N - 1) * P.h :=
      Nat.mul_pos (Nat.mul_pos (by norm_num) hqpowNat) P.h_pos
    have hres : 0 < P.q - 1 := Nat.sub_pos_of_lt P.one_lt_q
    simp only [TerminalNode, Fintype.card_prod, Fintype.card_fin]
    exact_mod_cast Nat.mul_pos hblocks hres
  have hmult := levelScale_div_eight_lt_terminalMultiplicity P N
  have hcountReal :
      (P.h : ℝ) * (P.k ^ (1 - P.sigma) * P.Omega / 8) <
        (Fintype.card (TerminalNode P N) : ℝ) *
          terminalMultiplicity P N := by
    have hkpow_le : P.k ^ (1 - P.sigma) ≤ P.k := by
      have hexp0 : 0 ≤ 1 - P.sigma := by
        linarith [P.sigma_add_epsilon_lt_one, P.epsilon_pos]
      calc
        P.k ^ (1 - P.sigma) ≤ P.k ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le P.one_le_k
            (sub_le_self 1 P.sigma_pos.le)
        _ = P.k := Real.rpow_one P.k
    have hlarge : P.k ^ (1 - P.sigma) * P.Omega / 8 <
        2 * ((P.q : ℝ) - 1) / P.q *
          P.k * P.Omega * Real.log P.OmegaOld := by
      rw [VDPLParameters.q]
      have hlog : (1 / 2 : ℝ) < Real.log P.OmegaOld :=
        (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
          (Real.log_two_gt_d9.trans_le P.log_two_le_log_OmegaOld)
      have hfactor : (1 / 8 : ℝ) <
          2 * ((13 : ℝ) - 1) / 13 * Real.log P.OmegaOld := by
        nlinarith
      have hkOmega : 0 < P.k * P.Omega := mul_pos P.k_pos P.Omega_pos
      calc
        P.k ^ (1 - P.sigma) * P.Omega / 8 ≤
            P.k * P.Omega / 8 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hkpow_le P.Omega_pos.le) (by norm_num)
        _ = (P.k * P.Omega) * (1 / 8 : ℝ) := by ring
        _ < (P.k * P.Omega) *
              (2 * ((13 : ℝ) - 1) / 13 * Real.log P.OmegaOld) :=
          mul_lt_mul_of_pos_left hfactor hkOmega
        _ = 2 * ((13 : ℝ) - 1) / 13 * P.k * P.Omega *
              Real.log P.OmegaOld := by ring
    have hscale :
        (Fintype.card (TerminalNode P N) : ℝ) *
            (P.levelScale N / 8) =
          (P.h : ℝ) *
            (2 * ((P.q : ℝ) - 1) / P.q *
              P.k * P.Omega * Real.log P.OmegaOld) := by
      simp only [TerminalNode, Fintype.card_prod, Fintype.card_fin,
        VDPLParameters.levelScale, VDPLParameters.qInvPow]
      push_cast
      have hpowNat : P.q ^ N = P.q ^ (N - 1) * P.q := by
        conv_lhs => rw [show N = (N - 1) + 1 by omega]
        exact pow_succ _ _
      have hpowReal : (P.q : ℝ) ^ N = (P.q : ℝ) ^ (N - 1) * P.q := by
        exact_mod_cast hpowNat
      rw [hpowReal]
      have hqR : (P.q : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_lt P.one_lt_q)
      have hqpowR : (P.q : ℝ) ^ (N - 1) ≠ 0 := pow_ne_zero _ hqR
      push_cast [Nat.cast_sub P.one_lt_q.le]
      field_simp [hqR, hqpowR]
      ring
    calc
      (P.h : ℝ) * (P.k ^ (1 - P.sigma) * P.Omega / 8) <
          (P.h : ℝ) *
            (2 * ((P.q : ℝ) - 1) / P.q * P.k * P.Omega *
              Real.log P.OmegaOld) := mul_lt_mul_of_pos_left hlarge hh
      _ = (Fintype.card (TerminalNode P N) : ℝ) *
            (P.levelScale N / 8) := hscale.symm
      _ < (Fintype.card (TerminalNode P N) : ℝ) *
          terminalMultiplicity P N := mul_lt_mul_of_pos_left hmult hnodes
  have hLzero : (P.LzeroPlusOne : ℝ) ≤
      P.k ^ (1 - P.sigma) * P.Omega / 8 := by
    calc
      (P.LzeroPlusOne : ℝ) ≤ P.LzeroScale := P.LzeroPlusOne_cast_le
      _ = (1 / 8 : ℝ) * P.k ^ (1 - P.sigma) * P.Omega := by
        unfold VDPLParameters.LzeroScale
        ring
      _ = P.k ^ (1 - P.sigma) * P.Omega / 8 := by ring
  exact_mod_cast (show (P.h : ℝ) * P.LzeroPlusOne <
      (Fintype.card (TerminalNode P N) : ℝ) * terminalMultiplicity P N by
    exact (mul_le_mul_of_nonneg_left hLzero hh.le).trans_lt hcountReal)

/-! ## Equations (13)--(16) and the terminal contradiction -/

/-- Source equation (13), with one contextual equation-(14) family for each
old exponent.  The family may depend on the rational node, the remaining
Hasse order, and all old exponents other than the coordinate being
eliminated.  The strict terminal endpoint is part of the data, and therefore
the last exponent occurring below is the unique canonical zero exponent. -/
structure TerminalEquation13
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (P : VDPLParameters ι) (N : ℕ)
    (oldSide : Fin (Fintype.card ι) → ℕ)
    (c : LambdaBox (activeTerminalBox P oldSide) → ℂ) where
  positive : 0 < N
  terminal : P.LlastZeroScale < ((P.q ^ N : ℕ) : ℝ)
  elimination : ∀ (x : TerminalNode P N) (m : ℕ),
    m < terminalMultiplicity P N →
      ∀ r : Fin (Fintype.card ι),
        ContextualEliminationFamily oldSide r
  equation13 : ∀ (x : TerminalNode P N) (m : ℕ)
      (hm : m < terminalMultiplicity P N),
    eliminateCoordinates (elimination x m hm) Finset.univ.toList
      (fun old : ActiveTerminalOldExponent oldSide ↦
        (hasseDeriv m
          (activeTerminalPolynomial P oldSide c old)).eval
            (terminalNodeValue P x)) = 0

namespace TerminalEquation13

/-- Tensor constructor requiring only source-specific nonsingular coordinate
matrices.  This is the interface used when equation (14) is established by
a special collocation theorem rather than the generic consecutive-degree
Vandermonde argument. -/
def ofNonsingularTensor
    {ι : Type u} [Fintype ι] [Nonempty ι]
    {P : VDPLParameters ι} {N : ℕ}
    {oldSide : Fin (Fintype.card ι) → ℕ}
    {c : LambdaBox (activeTerminalBox P oldSide) → ℂ}
    (hN : 0 < N)
    (hterminal : P.LlastZeroScale < ((P.q ^ N : ℕ) : ℝ))
    (E : ∀ (x : TerminalNode P N) (m : ℕ),
      m < terminalMultiplicity P N →
        ∀ r : Fin (Fintype.card ι), NonsingularFamily (oldSide r))
    (hrel : ∀ (x : TerminalNode P N) (m : ℕ)
      (hm : m < terminalMultiplicity P N)
      (row : ActiveTerminalOldExponent oldSide),
      ∑ old : ActiveTerminalOldExponent oldSide,
        tensorMatrix (fun r ↦ (E x m hm r).matrix) row old *
          (hasseDeriv m (activeTerminalPolynomial P oldSide c old)).eval
            (terminalNodeValue P x) = 0) :
    TerminalEquation13 P N oldSide c where
  positive := hN
  terminal := hterminal
  elimination x m hm r :=
    ContextualEliminationFamily.constNonsingular (E x m hm r)
  equation13 x m hm := by
    let v : ActiveTerminalOldExponent oldSide → ℂ := fun old ↦
      (hasseDeriv m (activeTerminalPolynomial P oldSide c old)).eval
        (terminalNodeValue P x)
    have hv : v = 0 := eq_zero_of_tensor_relations
      (fun r ↦ (E x m hm r).matrix)
      (fun r ↦ (E x m hm r).det_ne_zero) v
      (fun row ↦ hrel x m hm row)
    change eliminateCoordinates
      (fun r ↦ ContextualEliminationFamily.constNonsingular (E x m hm r))
        Finset.univ.toList v = 0
    rw [hv]
    exact eliminateCoordinates_zero _ _

/-- Constructor for the common source situation in which, after fixing the
rational node and the remaining Hasse order, the old-coordinate factors form
a literal tensor product.  The tensor determinant argument is carried out
here, and the resulting zero vector is then accepted by the more general
contextual-elimination interface. -/
def ofTensor
    {ι : Type u} [Fintype ι] [Nonempty ι]
    {P : VDPLParameters ι} {N : ℕ}
    {oldSide : Fin (Fintype.card ι) → ℕ}
    {c : LambdaBox (activeTerminalBox P oldSide) → ℂ}
    (hN : 0 < N)
    (hterminal : P.LlastZeroScale < ((P.q ^ N : ℕ) : ℝ))
    (E : ∀ (x : TerminalNode P N) (m : ℕ),
      m < terminalMultiplicity P N →
        ∀ r : Fin (Fintype.card ι), EliminationFamily (oldSide r))
    (hrel : ∀ (x : TerminalNode P N) (m : ℕ)
      (hm : m < terminalMultiplicity P N)
      (row : ActiveTerminalOldExponent oldSide),
      ∑ old : ActiveTerminalOldExponent oldSide,
        tensorMatrix (fun r ↦ (E x m hm r).matrix) row old *
          (hasseDeriv m (activeTerminalPolynomial P oldSide c old)).eval
            (terminalNodeValue P x) = 0) :
    TerminalEquation13 P N oldSide c where
  positive := hN
  terminal := hterminal
  elimination x m hm r := ContextualEliminationFamily.const (E x m hm r)
  equation13 x m hm := by
    let v : ActiveTerminalOldExponent oldSide → ℂ := fun old ↦
      (hasseDeriv m (activeTerminalPolynomial P oldSide c old)).eval
        (terminalNodeValue P x)
    have hv : v = 0 := eq_zero_of_tensor_relations
      (fun r ↦ (E x m hm r).matrix)
      (fun r ↦ (E x m hm r).det_matrix_ne_zero) v
      (fun row ↦ hrel x m hm row)
    change eliminateCoordinates
      (fun r ↦ ContextualEliminationFamily.const (E x m hm r))
        Finset.univ.toList v = 0
    rw [hv]
    exact eliminateCoordinates_zero _ _

/-- Repeated nonsingular determinant elimination turns (13)--(14) into the
individual vanishing assertions (15). -/
theorem equation15
    {ι : Type u} [Fintype ι] [Nonempty ι]
    {P : VDPLParameters ι} {N : ℕ}
    {oldSide : Fin (Fintype.card ι) → ℕ}
    {c : LambdaBox (activeTerminalBox P oldSide) → ℂ}
    (eq13 : TerminalEquation13 P N oldSide c)
    (old : ActiveTerminalOldExponent oldSide)
    (x : TerminalNode P N) (m : ℕ) (hm : m < terminalMultiplicity P N) :
    (hasseDeriv m
        (activeTerminalPolynomial P oldSide c old)).eval
      (terminalNodeValue P x) = 0 := by
  let v : ActiveTerminalOldExponent oldSide → ℂ := fun old ↦
    (hasseDeriv m
        (activeTerminalPolynomial P oldSide c old)).eval
      (terminalNodeValue P x)
  have hv : v = 0 := eq_zero_of_eliminateCoordinates_eq_zero
    (eq13.elimination x m hm) Finset.univ.toList v
    (by simpa only [v] using eq13.equation13 x m hm)
  exact congrFun hv old

/-- Equation (15), the count (16), and the Hasse multiplicity theorem force
every remaining one-variable polynomial to vanish identically. -/
theorem polynomial_eq_zero
    {ι : Type u} [Fintype ι] [Nonempty ι]
    {P : VDPLParameters ι} {N : ℕ}
    {oldSide : Fin (Fintype.card ι) → ℕ}
    {c : LambdaBox (activeTerminalBox P oldSide) → ℂ}
    (eq13 : TerminalEquation13 P N oldSide c)
    (old : ActiveTerminalOldExponent oldSide) :
    activeTerminalPolynomial P oldSide c old = 0 := by
  apply Multiplicity.eq_zero_of_hasseDeriv_eval_eq_zero_of_natDegree_lt_sum
    (terminalNodeValue P)
    (fun _ : TerminalNode P N ↦ terminalMultiplicity P N)
  · exact terminalNodeValue_injective P
  · have hdegree := natDegree_activeTerminalPolynomial_le P oldSide c old
    have hcount := terminal_degree_lt_count P eq13.positive
    simpa using hdegree.trans_lt hcount
  · intro x m hm
    exact eq13.equation15 old x m hm

/-- The final contradiction on p. 54: equation (13) is incompatible with a
nonzero Lemma-6 coefficient vector. -/
theorem false_of_nonzero
    {ι : Type u} [Fintype ι] [Nonempty ι]
    {P : VDPLParameters ι} {N : ℕ}
    {oldSide : Fin (Fintype.card ι) → ℕ}
    {c : LambdaBox (activeTerminalBox P oldSide) → ℂ} (hc : c ≠ 0)
    (eq13 : TerminalEquation13 P N oldSide c) : False := by
  apply hc
  funext lambda
  rcases lambda with ⟨shift, delta, old, last⟩
  have hlast : last = activeTerminalLastZero P oldSide := Fin.eq_zero last
  subst last
  let coeff : Fin (P.Lzero + 1) → Fin (P.LminusOne + 1) → ℂ :=
    fun d s ↦ c ⟨s, d, old, activeTerminalLastZero P oldSide⟩
  have hpoly : ∑ d, ∑ s, coeff d s •
      (poweredDeltaComplex P.h (d + 1)).taylor (s : ℂ) = 0 := by
    simpa only [activeTerminalPolynomial, coeff] using
      eq13.polynomial_eq_zero old
  have hcoeff : coeff = 0 :=
    shifted_poweredDelta_coefficients_eq_zero P.h P.LminusOne P.Lzero
      P.h_pos (by
        have heq := P.LminusOne_add_one_eq_h
        omega) coeff hpoly
  have hentry := congrFun (congrFun hcoeff delta) shift
  change c ⟨shift, delta, old, activeTerminalLastZero P oldSide⟩ = 0 at hentry
  exact hentry

end TerminalEquation13

/-- At the source terminal level, every nonzero coefficient family satisfying
equation (13) yields `False`.  The chosen level lies strictly above the real
last-coordinate scale and satisfies the corrected nonstrict upper bound. -/
theorem exists_terminal_level_contradiction
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (P : VDPLParameters ι) :
    ∃ N : ℕ,
      0 < N ∧ P.LlastZeroScale < ((P.q ^ N : ℕ) : ℝ) ∧
      P.LevelOK N ∧ P.LevelWithin N ∧
      ∀ (oldSide : Fin (Fintype.card ι) → ℕ)
        (c : LambdaBox (activeTerminalBox P oldSide) → ℂ), c ≠ 0 →
        TerminalEquation13 P N oldSide c → False := by
  obtain ⟨N, hNpos, hterminal, hN⟩ := P.exists_terminal_level_pos
  exact ⟨N, hNpos, hterminal, hN, hN.levelWithin,
    fun oldSide c hc eq13 ↦ eq13.false_of_nonzero hc⟩

end Erdos240.BakerFinalZeroCount

#print axioms Erdos240.BakerFinalZeroCount.tensorMatrix_det_ne_zero
#print axioms Erdos240.BakerFinalZeroCount.EliminationFamily.det_matrix_ne_zero
#print axioms Erdos240.BakerFinalZeroCount.EliminationFamily.ofOrdinaryDelta_matrix_apply
#print axioms Erdos240.BakerFinalZeroCount.eq_zero_of_eliminateCoordinates_eq_zero
#print axioms Erdos240.BakerFinalZeroCount.shifted_poweredDelta_coefficients_eq_zero
#print axioms Erdos240.BakerFinalZeroCount.terminal_degree_lt_count
#print axioms Erdos240.BakerFinalZeroCount.TerminalEquation13.ofTensor
#print axioms Erdos240.BakerFinalZeroCount.TerminalEquation13.false_of_nonzero
#print axioms Erdos240.BakerFinalZeroCount.exists_terminal_level_contradiction
