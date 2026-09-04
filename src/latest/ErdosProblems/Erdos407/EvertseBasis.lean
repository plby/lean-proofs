/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.AdelicMinkowski
import ErdosProblems.Erdos407.DeterminantGap
import ErdosProblems.Erdos407.SIntegerApproximation

/-!
# Evertse's three-place basis lemma

This file contains the rational `S = {infinity, 2, 3}` specialization of
Evertse's basis lemma (GLR, Lemma 5.2).  The proof follows Evertse's
dimension induction.  The cofactor construction below is the exact
finite-dimensional replacement for the informal choice of a relation of
maximum local coefficient.
-/

namespace Erdos407.PadicSubspace

open scoped BigOperators Matrix

namespace EvertseBasis

/-! ## The cofactor relation on a codimension-one prefix -/

/-- Evaluation matrix of a basis of vectors against one local basis of
forms. -/
def basisEvaluationMatrix {n : ℕ}
    (L : Fin n → RatLinearForm n) (x : Fin n → Fin n → ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun i j ↦ L i (x j)

theorem basisEvaluationMatrix_det_ne_zero {n : ℕ}
    {L : Fin n → RatLinearForm n} {x : Fin n → Fin n → ℚ}
    (hL : LinearIndependent ℚ L) (hx : LinearIndependent ℚ x) :
    (basisEvaluationMatrix L x).det ≠ 0 := by
  let LL : Place23 → Fin n → RatLinearForm n := fun _ ↦ L
  let X : Matrix (Fin n) (Fin n) ℚ := fun j i ↦ x j i
  have hF : (formMatrix LL Place23.infinite).det ≠ 0 :=
    formMatrix_det_ne_zero (fun _ ↦ hL) Place23.infinite
  have hXunit : IsUnit X := by
    apply Matrix.linearIndependent_rows_iff_isUnit.mp
    exact hx
  have hX : X.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det X).mp hXunit).ne_zero
  have heq : basisEvaluationMatrix L x =
      formMatrix LL Place23.infinite * X.transpose := by
    ext i j
    simp only [basisEvaluationMatrix, Matrix.mul_apply, Matrix.transpose_apply, X, LL,
      formMatrix]
    exact linearForm_eq_sum_coeff (L i) (x j)
  rw [heq, Matrix.det_mul, Matrix.det_transpose]
  exact mul_ne_zero hF hX

/-- The signed maximal minor obtained by deleting row `i` and the final
column. -/
def prefixCofactor {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (i : Fin (n + 1)) : ℚ :=
  (-1 : ℚ) ^ (i + Fin.last n : ℕ) *
    (M.submatrix i.succAbove (Fin.last n).succAbove).det

theorem det_eq_sum_prefixCofactor_mul_last {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) :
    M.det = ∑ i, prefixCofactor M i * M i (Fin.last n) := by
  rw [Matrix.det_succ_column M (Fin.last n)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [prefixCofactor]
  ring

/-- Expansion after replacing the last column by a prefix column. -/
theorem sum_prefixCofactor_mul_prefix_eq_zero {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (j : Fin n) :
    ∑ i, prefixCofactor M i * M i (Fin.castSucc j) = 0 := by
  let M' := M.updateCol (Fin.last n) (fun i ↦ M i (Fin.castSucc j))
  have hcols : ∀ i, M' i (Fin.castSucc j) = M' i (Fin.last n) := by
    intro i
    simp [M', Matrix.updateCol, Fin.castSucc_ne_last]
  have hdet : M'.det = 0 := Matrix.det_zero_of_column_eq
    (Fin.castSucc_ne_last j) hcols
  rw [Matrix.det_succ_column M' (Fin.last n)] at hdet
  rw [← hdet]
  apply Finset.sum_congr rfl
  intro i hi
  have hlast : M' i (Fin.last n) = M i (Fin.castSucc j) := by simp [M']
  have hsub :
      (M'.submatrix i.succAbove (Fin.last n).succAbove).det =
        (M.submatrix i.succAbove (Fin.last n).succAbove).det := by
    apply congrArg Matrix.det
    ext a b
    simp only [Matrix.submatrix_apply]
    have hne : ((i.succAbove a), ((Fin.last n).succAbove b)) ≠
        ((i.succAbove a), Fin.last n) := by
      intro h
      exact (Fin.succAbove_ne (Fin.last n) b) (congrArg Prod.snd h)
    simp [M', Matrix.updateCol, hne]
  simp only [prefixCofactor]
  rw [hlast, hsub]
  ring

theorem exists_prefixCofactor_ne_zero {n : ℕ}
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ} (hM : M.det ≠ 0) :
    ∃ i, prefixCofactor M i ≠ 0 := by
  by_contra h
  push Not at h
  have hz : ∑ i, prefixCofactor M i * M i (Fin.last n) = 0 := by simp [h]
  rw [← det_eq_sum_prefixCofactor_mul_last] at hz
  exact hM hz

/-- A row where the local norm of the cofactor vector is maximal. -/
noncomputable def maximalCofactorRow {n : ℕ}
    (v : Place23) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) : Fin (n + 1) :=
  Classical.choose (Finset.exists_max_image (Finset.univ : Finset (Fin (n + 1)))
    (fun i ↦ placeNorm v (prefixCofactor M i)) (by simp))

theorem le_maximalCofactorRow {n : ℕ}
    (v : Place23) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (i : Fin (n + 1)) :
    placeNorm v (prefixCofactor M i) ≤
      placeNorm v (prefixCofactor M (maximalCofactorRow v M)) := by
  exact (Classical.choose_spec (Finset.exists_max_image
    (Finset.univ : Finset (Fin (n + 1)))
    (fun i ↦ placeNorm v (prefixCofactor M i)) (by simp))).2 i (by simp)

theorem maximalCofactorRow_ne_zero {n : ℕ}
    (v : Place23) {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ}
    (hM : M.det ≠ 0) : prefixCofactor M (maximalCofactorRow v M) ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_prefixCofactor_ne_zero hM
  intro hz
  have hpos : 0 < placeNorm v (prefixCofactor M i) :=
    (placeNorm_pos_iff v _).mpr hi
  have hle := le_maximalCofactorRow v M i
  rw [hz, placeNorm_zero] at hle
  exact (not_lt_of_ge hle) hpos

/-- Coefficients expressing the omitted restricted form in terms of all the
other restricted forms. -/
noncomputable def restrictionCoefficient {n : ℕ}
    (v : Place23) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (i : Fin n) : ℚ :=
  -prefixCofactor M ((maximalCofactorRow v M).succAbove i) /
    prefixCofactor M (maximalCofactorRow v M)

theorem placeNorm_restrictionCoefficient_le_one {n : ℕ}
    (v : Place23) {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ}
    (hM : M.det ≠ 0) (i : Fin n) :
    placeNorm v (restrictionCoefficient v M i) ≤ 1 := by
  have hden := maximalCofactorRow_ne_zero v hM
  have hle := le_maximalCofactorRow v M
    ((maximalCofactorRow v M).succAbove i)
  let abv : AbsoluteValue ℚ ℚ :=
    IsAbsoluteValue.toAbsoluteValue (placeNorm v)
  change abv (-prefixCofactor M ((maximalCofactorRow v M).succAbove i) /
    prefixCofactor M (maximalCofactorRow v M)) ≤ 1
  rw [map_div₀ abv, map_neg_eq_map]
  exact (div_le_one ((placeNorm_pos_iff _ _).mpr hden)).mpr hle

/-- Exact relation (5.8) on the prefix span. -/
theorem omittedForm_eq_sum_restrictionCoefficient {n : ℕ}
    (v : Place23) {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ}
    (hM : M.det ≠ 0) (j : Fin n) :
    M (maximalCofactorRow v M) (Fin.castSucc j) =
      ∑ i : Fin n, restrictionCoefficient v M i *
        M ((maximalCofactorRow v M).succAbove i) (Fin.castSucc j) := by
  let r := maximalCofactorRow v M
  have hrel := sum_prefixCofactor_mul_prefix_eq_zero M j
  rw [Fin.sum_univ_succAbove
    (fun i ↦ prefixCofactor M i * M i (Fin.castSucc j)) r] at hrel
  have hr := maximalCofactorRow_ne_zero v hM
  have hrearrange :
      prefixCofactor M r * M r (Fin.castSucc j) =
        ∑ i : Fin n, -prefixCofactor M (r.succAbove i) *
          M (r.succAbove i) (Fin.castSucc j) := by
    calc
      _ = -(∑ i : Fin n, prefixCofactor M (r.succAbove i) *
          M (r.succAbove i) (Fin.castSucc j)) :=
        eq_neg_of_add_eq_zero_left hrel
      _ = _ := by
        let f : Fin n → ℚ := fun i ↦
          prefixCofactor M (r.succAbove i) *
            M (r.succAbove i) (Fin.castSucc j)
        calc
          -(∑ i, prefixCofactor M (r.succAbove i) *
              M (r.succAbove i) (Fin.castSucc j)) = ∑ i, -f i := by
            simpa [f] using (Finset.sum_neg_distrib :
              -(∑ i : Fin n, f i) = ∑ i : Fin n, -f i)
          _ = _ := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [f]
  simp only [restrictionCoefficient]
  calc
    M (maximalCofactorRow v M) (Fin.castSucc j) =
        (prefixCofactor M (maximalCofactorRow v M) *
          M (maximalCofactorRow v M) (Fin.castSucc j)) /
            prefixCofactor M (maximalCofactorRow v M) := by
      field_simp
    _ = (∑ i : Fin n, -prefixCofactor M
          ((maximalCofactorRow v M).succAbove i) *
            M ((maximalCofactorRow v M).succAbove i) (Fin.castSucc j)) /
          prefixCofactor M (maximalCofactorRow v M) := by rw [hrearrange]
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-! ## Restriction to the span of the prefix -/

/-- A rational linear form with prescribed coefficients. -/
def coefficientLinearForm {n : ℕ} (a : Fin n → ℚ) : RatLinearForm n where
  toFun y := ∑ j, a j * y j
  map_add' y z := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' q y := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    change a j * (q * y j) = q * (a j * y j)
    ring

@[simp] theorem coefficientLinearForm_apply {n : ℕ} (a y : Fin n → ℚ) :
    coefficientLinearForm a y = ∑ j, a j * y j := rfl

@[simp] theorem coefficientVector_coefficientLinearForm {n : ℕ} (a : Fin n → ℚ) :
    coefficientVector (coefficientLinearForm a) = a := by
  funext i
  simp [coefficientVector, coefficientLinearForm, Pi.single_apply]

/-- Restrict all forms except the maximal-cofactor row to the span of the
first `n` vectors, expressed in the coordinate basis of that span. -/
noncomputable def restrictedForms {n : ℕ}
    (L : Place23 → Fin (n + 1) → RatLinearForm (n + 1))
    (x : Fin (n + 1) → Fin (n + 1) → ℚ) :
    Place23 → Fin n → RatLinearForm n :=
  fun v i ↦ coefficientLinearForm fun j ↦
    L v ((maximalCofactorRow v (basisEvaluationMatrix (L v) x)).succAbove i)
      (x (Fin.castSucc j))

@[simp] theorem restrictedForms_basis_apply {n : ℕ}
    (L : Place23 → Fin (n + 1) → RatLinearForm (n + 1))
    (x : Fin (n + 1) → Fin (n + 1) → ℚ)
    (v : Place23) (i j : Fin n) :
    restrictedForms L x v i (Pi.basisFun ℚ (Fin n) j) =
      L v ((maximalCofactorRow v
        (basisEvaluationMatrix (L v) x)).succAbove i) (x (Fin.castSucc j)) := by
  classical
  simp [restrictedForms, coefficientLinearForm, Pi.single_apply]

theorem restrictedForms_nonsingular {n : ℕ}
    {L : Place23 → Fin (n + 1) → RatLinearForm (n + 1)}
    {x : Fin (n + 1) → Fin (n + 1) → ℚ}
    (hL : IsNonsingularFamily L) (hx : LinearIndependent ℚ x) :
    IsNonsingularFamily (restrictedForms L x) := by
  intro v
  let M := basisEvaluationMatrix (L v) x
  let r := maximalCofactorRow v M
  have hM : M.det ≠ 0 := basisEvaluationMatrix_det_ne_zero (hL v) hx
  have hminor : (M.submatrix r.succAbove (Fin.last n).succAbove).det ≠ 0 := by
    have hcof := maximalCofactorRow_ne_zero v hM
    simp only [prefixCofactor, mul_ne_zero_iff, ne_eq] at hcof
    exact hcof.2
  have hrows : LinearIndependent ℚ
      (fun i ↦ (M.submatrix r.succAbove (Fin.last n).succAbove) i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hminor
  have hcoeff : LinearIndependent ℚ
      (fun i ↦ coefficientVector (restrictedForms L x v i)) := by
    have heq : (fun i ↦ coefficientVector (restrictedForms L x v i)) =
        (fun i j ↦ M (r.succAbove i) (Fin.castSucc j)) := by
      funext i j
      simp [restrictedForms, basisEvaluationMatrix, M, r]
    rw [heq]
    have heqrows :
        (fun i ↦ (M.submatrix r.succAbove (Fin.last n).succAbove) i) =
          (fun i j ↦ M (r.succAbove i) (Fin.castSucc j)) := by
      funext i j
      simp [Matrix.submatrix_apply, Fin.succAbove_last]
    rw [heqrows] at hrows
    exact hrows
  apply LinearIndependent.of_comp formCoeffLinearMap
  change LinearIndependent ℚ (fun i ↦ coefficientVector (restrictedForms L x v i))
  exact hcoeff

/-! ## Reindexing the inductive permutation -/

/-- Insert the omitted row at the final index and use `π` on the prefix. -/
def insertOmittedPerm {n : ℕ} (r : Fin (n + 1)) (pi : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' (Fin.last n)).trans <|
    (Equiv.optionCongr pi).trans (finSuccEquiv' r).symm

@[simp] theorem insertOmittedPerm_last {n : ℕ}
    (r : Fin (n + 1)) (pi : Equiv.Perm (Fin n)) :
    insertOmittedPerm r pi (Fin.last n) = r := by
  simp [insertOmittedPerm]

@[simp] theorem insertOmittedPerm_castSucc {n : ℕ}
    (r : Fin (n + 1)) (pi : Equiv.Perm (Fin n)) (i : Fin n) :
    insertOmittedPerm r pi (Fin.castSucc i) = r.succAbove (pi i) := by
  simp [insertOmittedPerm, finSuccEquiv'_last_apply_castSucc]

/-! ## Output package -/

/-- A unit lower-triangular rational change of basis. -/
def IsUnitLowerTriangular {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  A.IsLowerTriangular ∧ ∀ i, A i i = 1

/-- Apply the rows of a change-of-basis matrix to a tuple of vectors. -/
def transformBasis {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → Fin n → ℚ)
    (i : Fin n) : Fin n → ℚ :=
  ∑ j, A i j • x j

@[simp] theorem transformBasis_basisFun {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) :
    transformBasis A (Pi.basisFun ℚ (Fin n)) i = A i := by
  classical
  ext j
  simp [transformBasis, Pi.basisFun, Pi.single_apply]

/-- Embed prefix coordinates in the original vector space using the first
`n` input vectors. -/
def prefixVector {n : ℕ} (x : Fin (n + 1) → Fin (n + 1) → ℚ)
    (y : Fin n → ℚ) : Fin (n + 1) → ℚ :=
  ∑ j, y j • x (Fin.castSucc j)

/-- Add a final vector to a lower-triangular change of basis.  The final row
is `x_last + sum_i xi_i u_i`. -/
def liftMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (xi : Fin n → ℚ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  fun i j ↦ Fin.lastCases
    (Fin.lastCases 1 (fun k ↦ ∑ h, xi h * A h k) j)
    (fun r ↦ Fin.lastCases 0 (fun k ↦ A r k) j) i

@[simp] theorem liftMatrix_prefix_prefix {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (xi : Fin n → ℚ) (i j : Fin n) :
    liftMatrix A xi (Fin.castSucc i) (Fin.castSucc j) = A i j := by
  simp [liftMatrix]

@[simp] theorem liftMatrix_prefix_last {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (xi : Fin n → ℚ) (i : Fin n) :
    liftMatrix A xi (Fin.castSucc i) (Fin.last n) = 0 := by
  simp [liftMatrix]

@[simp] theorem liftMatrix_last_prefix {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (xi : Fin n → ℚ) (j : Fin n) :
    liftMatrix A xi (Fin.last n) (Fin.castSucc j) = ∑ h, xi h * A h j := by
  simp [liftMatrix]

@[simp] theorem liftMatrix_last_last {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (xi : Fin n → ℚ) :
    liftMatrix A xi (Fin.last n) (Fin.last n) = 1 := by
  simp [liftMatrix]

theorem liftMatrix_unitLower {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℚ} (xi : Fin n → ℚ)
    (hA : IsUnitLowerTriangular A) :
    IsUnitLowerTriangular (liftMatrix A xi) := by
  constructor
  · intro i j hij
    revert j
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · intro j hij
      have hfalse : ¬ Fin.last n < j := not_lt_of_ge (Fin.le_last j)
      exact False.elim (hfalse (by simpa using hij))
    · intro j
      refine Fin.lastCases ?_ (fun j ↦ ?_) j
      · intro hij
        simp
      · intro hij
        rw [liftMatrix_prefix_prefix]
        apply hA.1
        exact (Fin.castSucc_lt_castSucc_iff.mp (by
          change Fin.castSucc i < Fin.castSucc j at hij
          exact hij))
  · intro i
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · simp
    · simpa using hA.2 i

theorem inZOneSixScalar_fin_sum {n : ℕ} (f : Fin n → ℚ)
    (hf : ∀ i, SIntegerApproximation.InZOneSixScalar (f i)) :
    SIntegerApproximation.InZOneSixScalar (∑ i, f i) := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simpa using SIntegerApproximation.InZOneSixScalar.zero
  | @insert i s his ih =>
      rw [Finset.sum_insert his]
      exact SIntegerApproximation.InZOneSixScalar.add (hf i) ih

theorem liftMatrix_inZOneSix {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℚ} {xi : Fin n → ℚ}
    (hA : ∀ i j, SIntegerApproximation.InZOneSixScalar (A i j))
    (hxi : ∀ i, SIntegerApproximation.InZOneSixScalar (xi i)) :
    ∀ i j, SIntegerApproximation.InZOneSixScalar (liftMatrix A xi i j) := by
  intro i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · intro j
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · simpa using SIntegerApproximation.InZOneSixScalar.intCast 1
    · simp only [liftMatrix_last_prefix]
      exact inZOneSixScalar_fin_sum _ fun h ↦
        SIntegerApproximation.InZOneSixScalar.mul (hxi h) (hA h j)
  · intro j
    refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · simpa using SIntegerApproximation.InZOneSixScalar.zero
    · simpa using hA i j

@[simp] theorem transformBasis_liftMatrix_prefix {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (xi : Fin n → ℚ)
    (x : Fin (n + 1) → Fin (n + 1) → ℚ) (i : Fin n) :
    transformBasis (liftMatrix A xi) x (Fin.castSucc i) =
      prefixVector x (A i) := by
  classical
  rw [transformBasis, Fin.sum_univ_castSucc]
  simp only [liftMatrix_prefix_last, zero_smul, add_zero,
    liftMatrix_prefix_prefix]
  rfl

@[simp] theorem transformBasis_liftMatrix_last {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (xi : Fin n → ℚ)
    (x : Fin (n + 1) → Fin (n + 1) → ℚ) :
    transformBasis (liftMatrix A xi) x (Fin.last n) =
      x (Fin.last n) + ∑ i, xi i • prefixVector x (A i) := by
  classical
  rw [transformBasis, Fin.sum_univ_castSucc]
  simp only [liftMatrix_last_last, one_smul, liftMatrix_last_prefix]
  simp only [prefixVector, Finset.smul_sum, Finset.sum_smul]
  have hsum :
      (∑ j : Fin n, ∑ i : Fin n, (xi i * A i j) • x (Fin.castSucc j)) =
        ∑ i : Fin n, ∑ j : Fin n, xi i • A i j • x (Fin.castSucc j) := by
    calc
      _ = ∑ i : Fin n, ∑ j : Fin n,
          (xi i * A i j) • x (Fin.castSucc j) := Finset.sum_comm
      _ = _ := by simp [smul_smul]
  calc
    (∑ j : Fin n, ∑ i : Fin n, (xi i * A i j) • x (Fin.castSucc j)) +
          x (Fin.last n) =
        x (Fin.last n) +
          (∑ j : Fin n, ∑ i : Fin n,
            (xi i * A i j) • x (Fin.castSucc j)) := add_comm _ _
    _ = x (Fin.last n) +
        ∑ i : Fin n, ∑ j : Fin n,
          xi i • A i j • x (Fin.castSucc j) :=
      congrArg (x (Fin.last n) + ·) hsum

@[simp] theorem linearForm_transformBasis_liftMatrix_prefix {n : ℕ}
    (f : RatLinearForm (n + 1))
    (A : Matrix (Fin n) (Fin n) ℚ) (xi : Fin n → ℚ)
    (x : Fin (n + 1) → Fin (n + 1) → ℚ) (i : Fin n) :
    f (transformBasis (liftMatrix A xi) x (Fin.castSucc i)) =
      f (prefixVector x (A i)) := by
  rw [transformBasis_liftMatrix_prefix]

@[simp] theorem linearForm_transformBasis_liftMatrix_last {n : ℕ}
    (f : RatLinearForm (n + 1))
    (A : Matrix (Fin n) (Fin n) ℚ) (xi : Fin n → ℚ)
    (x : Fin (n + 1) → Fin (n + 1) → ℚ) :
    f (transformBasis (liftMatrix A xi) x (Fin.last n)) =
      f (x (Fin.last n)) +
        ∑ i, xi i * f (prefixVector x (A i)) := by
  rw [transformBasis_liftMatrix_last]
  simp only [map_add, map_sum, map_smul, smul_eq_mul]

/-! ## Quantitative constants and elementary norm bounds -/

/-- A deliberately generous dimension-only constant for the induction. -/
def basisConstant : ℕ → ℝ
  | 0 => 1
  | n + 1 => ((n : ℝ) + 2) ^ 2 * (basisConstant n + 1)

theorem one_le_basisConstant : ∀ n, (1 : ℝ) ≤ basisConstant n := by
  intro n
  induction n with
  | zero => simp [basisConstant]
  | succ n ih =>
      simp only [basisConstant]
      have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have hsq : (1 : ℝ) ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith
      have hsum : (1 : ℝ) ≤ basisConstant n + 1 := by linarith
      nlinarith [mul_le_mul hsq hsum (by positivity) (by positivity)]

theorem basisConstant_le_succ (n : ℕ) :
    basisConstant n ≤ basisConstant (n + 1) := by
  simp only [basisConstant]
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hc := one_le_basisConstant n
  have hsq : (1 : ℝ) ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith
  calc
    basisConstant n ≤ basisConstant n + 1 := by linarith
    _ ≤ ((n : ℝ) + 2) ^ 2 * (basisConstant n + 1) := by
      exact (le_mul_iff_one_le_left (by linarith)).mpr hsq

theorem basisConstant_succ_large (n : ℕ) :
    1 + (n : ℝ) * ((n : ℝ) * ((1 / 2 : ℝ) * basisConstant n) + 1) ≤
      basisConstant (n + 1) := by
  simp only [basisConstant]
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hc := one_le_basisConstant n
  nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (le_trans zero_le_one hc),
    mul_nonneg hn (le_trans zero_le_one hc)]

theorem nat_mul_basisConstant_le_succ (n : ℕ) :
    (n : ℝ) * basisConstant n ≤ basisConstant (n + 1) := by
  simp only [basisConstant]
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hc0 : 0 ≤ basisConstant n := le_trans zero_le_one (one_le_basisConstant n)
  have hnSq : (n : ℝ) ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith
  calc
    (n : ℝ) * basisConstant n ≤
        ((n : ℝ) + 2) ^ 2 * basisConstant n :=
      mul_le_mul_of_nonneg_right hnSq hc0
    _ ≤ ((n : ℝ) + 2) ^ 2 * (basisConstant n + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)

theorem real_placeNorm_infinite_fin_sum_le_nat_mul {n : ℕ}
    (f : Fin n → ℚ) (t : ℝ)
    (h : ∀ i, ((placeNorm .infinite (f i) : ℚ) : ℝ) ≤ t) :
    ((placeNorm .infinite (∑ i, f i) : ℚ) : ℝ) ≤ (n : ℝ) * t := by
  calc
    ((placeNorm .infinite (∑ i, f i) : ℚ) : ℝ) ≤
        ∑ i, ((placeNorm .infinite (f i) : ℚ) : ℝ) := by
      simp only [placeNorm_infinite]
      exact_mod_cast (Finset.abs_sum_le_sum_abs f Finset.univ)
    _ ≤ ∑ _i : Fin n, t := Finset.sum_le_sum fun i _ ↦ h i
    _ = (n : ℝ) * t := by simp

theorem real_placeNorm_infinite_add_le (a b : ℚ) :
    ((placeNorm Place23.infinite (a + b) : ℚ) : ℝ) ≤
      ((placeNorm Place23.infinite a : ℚ) : ℝ) +
        ((placeNorm Place23.infinite b : ℚ) : ℝ) := by
  simp only [placeNorm_infinite, Rat.cast_abs, Rat.cast_add]
  exact abs_add_le _ _

theorem real_placeNorm_add_le_max_of_ne_infinite
    (v : Place23) (hv : v ≠ .infinite) (a b : ℚ) :
    ((placeNorm v (a + b) : ℚ) : ℝ) ≤
      max ((placeNorm v a : ℚ) : ℝ) ((placeNorm v b : ℚ) : ℝ) := by
  fin_cases v
  · exact (hv rfl).elim
  · exact_mod_cast padicNorm.nonarchimedean
  · exact_mod_cast padicNorm.nonarchimedean

theorem real_placeNorm_fin_sum_le_of_ne_infinite {n : ℕ}
    (v : Place23) (hv : v ≠ .infinite) (f : Fin n → ℚ)
    (t : ℝ) (ht : 0 ≤ t)
    (h : ∀ i, ((placeNorm v (f i) : ℚ) : ℝ) ≤ t) :
    ((placeNorm v (∑ i, f i) : ℚ) : ℝ) ≤ t := by
  classical
  let s : Finset (Fin n) := Finset.univ
  change ((placeNorm v (∑ i ∈ s, f i) : ℚ) : ℝ) ≤ t
  induction s using Finset.induction_on with
  | empty => simpa using ht
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (real_placeNorm_add_le_max_of_ne_infinite v hv _ _).trans
        (max_le (h a) ih)

theorem real_placeNorm_mul_le_mul (v : Place23) (a b : ℚ) (A B : ℝ)
    (hA : ((placeNorm v a : ℚ) : ℝ) ≤ A)
    (hB : ((placeNorm v b : ℚ) : ℝ) ≤ B)
    (hA0 : 0 ≤ A) :
    ((placeNorm v (a * b) : ℚ) : ℝ) ≤ A * B := by
  rw [placeNorm_mul, Rat.cast_mul]
  exact mul_le_mul hA hB (by exact_mod_cast placeNorm_nonneg v b) hA0

theorem linearForm_prefixVector {n : ℕ}
    (f : RatLinearForm (n + 1)) (x : Fin (n + 1) → Fin (n + 1) → ℚ)
    (y : Fin n → ℚ) :
    f (prefixVector x y) = ∑ j, y j * f (x (Fin.castSucc j)) := by
  simp [prefixVector]

theorem restrictedForms_prefixVector {n : ℕ}
    (L : Place23 → Fin (n + 1) → RatLinearForm (n + 1))
    (x : Fin (n + 1) → Fin (n + 1) → ℚ)
    (v : Place23) (i : Fin n) (y : Fin n → ℚ) :
    restrictedForms L x v i y =
      L v ((maximalCofactorRow v
        (basisEvaluationMatrix (L v) x)).succAbove i) (prefixVector x y) := by
  classical
  simp only [restrictedForms, coefficientLinearForm_apply,
    linearForm_prefixVector]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The omitted form relation, extended from the prefix basis to its span. -/
theorem omittedForm_prefixVector {n : ℕ}
    {L : Fin (n + 1) → RatLinearForm (n + 1)}
    {x : Fin (n + 1) → Fin (n + 1) → ℚ}
    (v : Place23) (hL : LinearIndependent ℚ L)
    (hx : LinearIndependent ℚ x) (y : Fin n → ℚ) :
    L (maximalCofactorRow v (basisEvaluationMatrix L x)) (prefixVector x y) =
      ∑ i : Fin n, restrictionCoefficient v (basisEvaluationMatrix L x) i *
        L ((maximalCofactorRow v
          (basisEvaluationMatrix L x)).succAbove i) (prefixVector x y) := by
  classical
  rw [linearForm_prefixVector]
  simp_rw [linearForm_prefixVector]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hrel := omittedForm_eq_sum_restrictionCoefficient v
    (basisEvaluationMatrix_det_ne_zero hL hx) j
  change L (maximalCofactorRow v (basisEvaluationMatrix L x))
      (x (Fin.castSucc j)) = _ at hrel
  rw [hrel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [basisEvaluationMatrix]
  ring

/-! ## The dimension induction -/

/-- Quantitative conclusion of the three-place basis lemma with the explicit
dimension-only constant `basisConstant n`. -/
def BasisConclusion {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (x : Fin n → Fin n → ℚ) (mu : Place23 → Fin n → ℝ) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) ℚ,
    IsUnitLowerTriangular A ∧
    (∀ i j, AdelicMinkowski.InZOneSix (fun _ : Fin 1 ↦ A i j)) ∧
    ∃ pi : Place23 → Equiv.Perm (Fin n), ∀ v i j,
      ((placeNorm v (L v (pi v i) (transformBasis A x j)) : ℚ) : ℝ) ≤
        (if v = Place23.infinite then basisConstant n else 1) *
          min (mu v i) (mu v j)

/-- The rational `S = {∞,2,3}` specialization of Evertse's basis lemma. -/
theorem evertseBasis_induction : ∀ n : ℕ,
    ∀ (L : Place23 → Fin n → RatLinearForm n), IsNonsingularFamily L →
    ∀ (x : Fin n → Fin n → ℚ) (mu : Place23 → Fin n → ℝ),
      LinearIndependent ℚ x →
      (∀ v i, 0 < mu v i) →
      (∀ v, Monotone (mu v)) →
      (∀ v k j, ((placeNorm v (L v k (x j)) : ℚ) : ℝ) ≤ mu v j) →
      BasisConclusion L x mu := by
  intro n
  induction n with
  | zero =>
      intro L hL x mu hx hmu hmono hbound
      refine ⟨0, ?_, ?_, fun _ ↦ Equiv.refl _, ?_⟩
      · constructor
        · intro i j hij
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
      · intro v i
        exact Fin.elim0 i
  | succ n ih =>
      intro L hL x mu hx hmu hmono hbound
      let L' : Place23 → Fin n → RatLinearForm n := restrictedForms L x
      let x' : Fin n → Fin n → ℚ := Pi.basisFun ℚ (Fin n)
      let mu' : Place23 → Fin n → ℝ := fun v i ↦ mu v (Fin.castSucc i)
      have hL' : IsNonsingularFamily L' := restrictedForms_nonsingular hL hx
      have hx' : LinearIndependent ℚ x' := (Pi.basisFun ℚ (Fin n)).linearIndependent
      have hmu' : ∀ v i, 0 < mu' v i := fun v i ↦ hmu v (Fin.castSucc i)
      have hmono' : ∀ v, Monotone (mu' v) := by
        intro v i j hij
        exact hmono v (Fin.castSucc_le_castSucc_iff.mpr hij)
      have hbound' : ∀ v k j,
          ((placeNorm v (L' v k (x' j)) : ℚ) : ℝ) ≤ mu' v j := by
        intro v k j
        simpa only [L', x', mu', restrictedForms_basis_apply] using hbound v
          ((maximalCofactorRow v
            (basisEvaluationMatrix (L v) x)).succAbove k) (Fin.castSucc j)
      obtain ⟨A', hA'lower, hA'Z, pi', hIH⟩ :=
        ih L' hL' x' mu' hx' hmu' hmono' hbound'
      let u : Fin n → Fin n → ℚ := transformBasis A' x'
      have hdetA' : A'.det = 1 := by
        rw [Matrix.det_of_isLowerTriangular A' hA'lower.1]
        simp [hA'lower.2]
      have hA'unit : IsUnit A' := by
        rw [Matrix.isUnit_iff_isUnit_det, hdetA']
        exact isUnit_one
      have hu : LinearIndependent ℚ u := by
        have hr : LinearIndependent ℚ A' :=
          Matrix.linearIndependent_rows_iff_isUnit.mpr hA'unit
        have heu : u = A' := by
          funext i
          exact transformBasis_basisFun A' i
        rw [heu]
        exact hr
      let F : Place23 → Fin n → RatLinearForm n :=
        fun v i ↦ L' v (pi' v i)
      have hF : IsNonsingularFamily F := by
        intro v
        exact (hL' v).comp (pi' v) (pi' v).injective
      have hB : ∀ v, (basisEvaluationMatrix (F v) u).det ≠ 0 :=
        fun v ↦ basisEvaluationMatrix_det_ne_zero (hF v) hu
      have hsurj : ∀ v, Function.Surjective
          (basisEvaluationMatrix (F v) u).mulVec := by
        intro v
        rw [Matrix.mulVec_surjective_iff_isUnit,
          Matrix.isUnit_iff_isUnit_det]
        exact isUnit_iff_ne_zero.mpr (hB v)
      have hgamma : ∀ v : Place23, ∃ gamma : Fin n → ℚ,
          (basisEvaluationMatrix (F v) u).mulVec gamma =
            fun i ↦ L v ((maximalCofactorRow v
              (basisEvaluationMatrix (L v) x)).succAbove (pi' v i))
                (x (Fin.last n)) := by
        intro v
        exact hsurj v _
      choose gamma hgammaEq using hgamma
      have happrox : ∀ j : Fin n, ∃ a : ℚ,
          SIntegerApproximation.InZOneSixScalar a ∧
          abs (((a + gamma Place23.infinite j : ℚ) : ℝ)) ≤ 1 / 2 ∧
          padicNorm 2 (a + gamma Place23.two j) ≤ 1 ∧
          padicNorm 3 (a + gamma Place23.three j) ≤ 1 := by
        intro j
        obtain ⟨a, haZ, haInf, haTwo, haThree⟩ :=
          SIntegerApproximation.exists_inZOneSix_approximation
            (-gamma Place23.infinite j) (-gamma Place23.two j)
              (-gamma Place23.three j)
        refine ⟨a, haZ, ?_, ?_, ?_⟩
        · convert haInf using 2 <;> ring_nf
        · convert haTwo using 2 <;> ring
        · convert haThree using 2 <;> ring
      choose xi hxiZ hxiInf hxiTwo hxiThree using happrox
      have hgamma_eval (v : Place23) (i : Fin n) :
          L v ((maximalCofactorRow v
            (basisEvaluationMatrix (L v) x)).succAbove (pi' v i))
              (x (Fin.last n)) =
            ∑ j, gamma v j *
              L v ((maximalCofactorRow v
                (basisEvaluationMatrix (L v) x)).succAbove (pi' v i))
                  (prefixVector x (A' j)) := by
        have hg := congrFun (hgammaEq v) i
        change (∑ j, L' v (pi' v i) (u j) * gamma v j) =
          L v ((maximalCofactorRow v
            (basisEvaluationMatrix (L v) x)).succAbove (pi' v i))
              (x (Fin.last n)) at hg
        rw [← hg]
        apply Finset.sum_congr rfl
        intro j hj
        have huj : u j = A' j := transformBasis_basisFun A' j
        rw [huj, restrictedForms_prefixVector]
        ring
      have hselected_last (v : Place23) (i : Fin n) :
          L v ((maximalCofactorRow v
            (basisEvaluationMatrix (L v) x)).succAbove (pi' v i))
              (transformBasis (liftMatrix A' xi) x (Fin.last n)) =
            ∑ j, (xi j + gamma v j) *
              L v ((maximalCofactorRow v
                (basisEvaluationMatrix (L v) x)).succAbove (pi' v i))
                  (prefixVector x (A' j)) := by
        rw [linearForm_transformBasis_liftMatrix_last, hgamma_eval]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      have hprefix_pair (v : Place23) (i j : Fin n) :
          ((placeNorm v
            (L v ((maximalCofactorRow v
              (basisEvaluationMatrix (L v) x)).succAbove (pi' v i))
                (prefixVector x (A' j))) : ℚ) : ℝ) ≤
            (if v = Place23.infinite then basisConstant n else 1) *
              min (mu v (Fin.castSucc i)) (mu v (Fin.castSucc j)) := by
        rw [← restrictedForms_prefixVector]
        simpa only [L', x', mu', transformBasis_basisFun] using hIH v i j
      have hprefix_left (v : Place23) (i j : Fin n) :
          ((placeNorm v
            (L v ((maximalCofactorRow v
              (basisEvaluationMatrix (L v) x)).succAbove (pi' v i))
                (prefixVector x (A' j))) : ℚ) : ℝ) ≤
            (if v = Place23.infinite then basisConstant n else 1) *
              mu v (Fin.castSucc i) := by
        exact (hprefix_pair v i j).trans (mul_le_mul_of_nonneg_left
          (min_le_left _ _) (by split <;> positivity [one_le_basisConstant n]))
      have hprefix_right (v : Place23) (i j : Fin n) :
          ((placeNorm v
            (L v ((maximalCofactorRow v
              (basisEvaluationMatrix (L v) x)).succAbove (pi' v i))
                (prefixVector x (A' j))) : ℚ) : ℝ) ≤
            (if v = Place23.infinite then basisConstant n else 1) *
              mu v (Fin.castSucc j) := by
        exact (hprefix_pair v i j).trans (mul_le_mul_of_nonneg_left
          (min_le_right _ _) (by split <;> positivity [one_le_basisConstant n]))
      have herror (v : Place23) (j : Fin n) :
          ((placeNorm v (xi j + gamma v j) : ℚ) : ℝ) ≤
            if v = Place23.infinite then 1 / 2 else 1 := by
        fin_cases v
        · change ((|(xi j + gamma Place23.infinite j)| : ℚ) : ℝ) ≤ 1 / 2
          simpa only [Rat.cast_abs, Rat.cast_add] using hxiInf j
        · change ((padicNorm 2 (xi j + gamma Place23.two j) : ℚ) : ℝ) ≤ 1
          exact_mod_cast hxiTwo j
        · change ((padicNorm 3 (xi j + gamma Place23.three j) : ℚ) : ℝ) ≤ 1
          exact_mod_cast hxiThree j
      have hcoefficient (v : Place23) (i : Fin n) :
          ((placeNorm v
            (restrictionCoefficient v (basisEvaluationMatrix (L v) x)
              (pi' v i)) : ℚ) : ℝ) ≤ 1 := by
        exact_mod_cast placeNorm_restrictionCoefficient_le_one v
          (basisEvaluationMatrix_det_ne_zero (hL v) hx) (pi' v i)
      have hselected_final_bound (v : Place23) (i : Fin n) :
          ((placeNorm v
            (L v ((maximalCofactorRow v
              (basisEvaluationMatrix (L v) x)).succAbove (pi' v i))
                (transformBasis (liftMatrix A' xi) x (Fin.last n))) : ℚ) : ℝ) ≤
            if v = Place23.infinite then
              (n : ℝ) * ((1 / 2 : ℝ) *
                (basisConstant n * mu v (Fin.castSucc i)))
            else mu v (Fin.castSucc i) := by
        by_cases hv : v = Place23.infinite
        · subst v
          simp only [if_pos]
          rw [hselected_last]
          apply real_placeNorm_infinite_fin_sum_le_nat_mul
          intro k
          exact real_placeNorm_mul_le_mul Place23.infinite _ _ _ _
            (herror Place23.infinite k) (hprefix_left _ i k) (by positivity)
        · simp only [if_neg hv]
          rw [hselected_last]
          apply real_placeNorm_fin_sum_le_of_ne_infinite v hv _ _
            (le_of_lt (hmu v _))
          intro k
          simpa only [one_mul] using
            (real_placeNorm_mul_le_mul v _ _ 1
              (mu v (Fin.castSucc i))
              (by simpa only [if_neg hv] using herror v k)
              (by simpa only [if_neg hv, one_mul] using hprefix_left v i k)
              (by positivity))
      have hselected_difference_bound (v : Place23) (i : Fin n) :
          ((placeNorm v
            (L v ((maximalCofactorRow v
                (basisEvaluationMatrix (L v) x)).succAbove (pi' v i))
                  (transformBasis (liftMatrix A' xi) x (Fin.last n)) -
              L v ((maximalCofactorRow v
                (basisEvaluationMatrix (L v) x)).succAbove (pi' v i))
                  (x (Fin.last n))) : ℚ) : ℝ) ≤
            if v = Place23.infinite then
              ((n : ℝ) * ((1 / 2 : ℝ) * basisConstant n) + 1) *
                mu v (Fin.last n)
            else mu v (Fin.last n) := by
        by_cases hv : v = Place23.infinite
        · subst v
          simp only [if_pos, placeNorm_infinite, Rat.cast_abs, Rat.cast_sub]
          have hf := hselected_final_bound Place23.infinite i
          simp only [if_pos, placeNorm_infinite, Rat.cast_abs] at hf
          have hxlast := hbound Place23.infinite
            ((maximalCofactorRow Place23.infinite
              (basisEvaluationMatrix (L Place23.infinite) x)).succAbove
                (pi' Place23.infinite i)) (Fin.last n)
          simp only [placeNorm_infinite, Rat.cast_abs] at hxlast
          calc
            |_ - _| ≤
                |((L Place23.infinite
                    ((maximalCofactorRow Place23.infinite
                      (basisEvaluationMatrix (L Place23.infinite) x)).succAbove
                        (pi' Place23.infinite i))
                      (transformBasis (liftMatrix A' xi) x (Fin.last n)) : ℚ) : ℝ)| +
                |((L Place23.infinite
                    ((maximalCofactorRow Place23.infinite
                      (basisEvaluationMatrix (L Place23.infinite) x)).succAbove
                        (pi' Place23.infinite i))
                      (x (Fin.last n)) : ℚ) : ℝ)| := abs_sub _ _
            _ ≤ (n : ℝ) * ((1 / 2 : ℝ) *
                  (basisConstant n * mu Place23.infinite (Fin.castSucc i))) +
                mu Place23.infinite (Fin.last n) :=
              add_le_add hf hxlast
            _ ≤ ((n : ℝ) * ((1 / 2 : ℝ) * basisConstant n) + 1) *
                mu Place23.infinite (Fin.last n) := by
              have hm := hmono Place23.infinite (Fin.le_last (Fin.castSucc i))
              have hK : 0 ≤ (n : ℝ) * ((1 / 2 : ℝ) * basisConstant n) :=
                by positivity [one_le_basisConstant n]
              have hfirst :
                  (n : ℝ) * ((1 / 2 : ℝ) *
                    (basisConstant n * mu Place23.infinite (Fin.castSucc i))) ≤
                    ((n : ℝ) * ((1 / 2 : ℝ) * basisConstant n)) *
                      mu Place23.infinite (Fin.last n) := by
                calc
                  _ = ((n : ℝ) * ((1 / 2 : ℝ) * basisConstant n)) *
                      mu Place23.infinite (Fin.castSucc i) := by ring
                  _ ≤ _ := mul_le_mul_of_nonneg_left hm hK
              calc
                _ ≤ ((n : ℝ) * ((1 / 2 : ℝ) * basisConstant n)) *
                      mu Place23.infinite (Fin.last n) +
                    mu Place23.infinite (Fin.last n) :=
                  add_le_add hfirst le_rfl
                _ = _ := by ring
        · simp only [if_neg hv]
          have ht := real_placeNorm_add_le_max_of_ne_infinite v hv
              (L v
                ((maximalCofactorRow v
                  (basisEvaluationMatrix (L v) x)).succAbove
                    (pi' v i))
                  (transformBasis (liftMatrix A' xi) x (Fin.last n)))
              (-L v
                ((maximalCofactorRow v
                  (basisEvaluationMatrix (L v) x)).succAbove
                    (pi' v i)) (x (Fin.last n)))
          rw [← sub_eq_add_neg] at ht
          have hf := hselected_final_bound v i
          simp only [if_neg hv] at hf
          have hxv := hbound v
            ((maximalCofactorRow v
              (basisEvaluationMatrix (L v) x)).succAbove (pi' v i)) (Fin.last n)
          exact ht.trans (max_le
            (hf.trans (hmono v (Fin.le_last _)))
            (by simpa only [placeNorm_neg] using hxv))
      have homitted_prefix (v : Place23) (y : Fin n → ℚ) :
          L v (maximalCofactorRow v (basisEvaluationMatrix (L v) x))
              (prefixVector x y) =
            ∑ i, restrictionCoefficient v (basisEvaluationMatrix (L v) x)
                (pi' v i) *
              L v ((maximalCofactorRow v
                (basisEvaluationMatrix (L v) x)).succAbove (pi' v i))
                  (prefixVector x y) := by
        rw [omittedForm_prefixVector v (hL v) hx]
        exact (Equiv.sum_comp (pi' v) (fun i ↦
          restrictionCoefficient v (basisEvaluationMatrix (L v) x) i *
            L v ((maximalCofactorRow v
              (basisEvaluationMatrix (L v) x)).succAbove i)
                (prefixVector x y))).symm
      have homitted_last (v : Place23) :
          L v (maximalCofactorRow v (basisEvaluationMatrix (L v) x))
              (transformBasis (liftMatrix A' xi) x (Fin.last n)) =
            L v (maximalCofactorRow v (basisEvaluationMatrix (L v) x))
                (x (Fin.last n)) +
              ∑ i, restrictionCoefficient v
                  (basisEvaluationMatrix (L v) x) (pi' v i) *
                (L v ((maximalCofactorRow v
                    (basisEvaluationMatrix (L v) x)).succAbove (pi' v i))
                      (transformBasis (liftMatrix A' xi) x (Fin.last n)) -
                  L v ((maximalCofactorRow v
                    (basisEvaluationMatrix (L v) x)).succAbove (pi' v i))
                      (x (Fin.last n))) := by
        rw [linearForm_transformBasis_liftMatrix_last]
        simp_rw [homitted_prefix]
        simp_rw [linearForm_transformBasis_liftMatrix_last]
        simp only [add_sub_cancel_left]
        simp_rw [Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      refine ⟨liftMatrix A' xi, liftMatrix_unitLower xi hA'lower,
        ?_, fun v ↦ insertOmittedPerm
          (maximalCofactorRow v (basisEvaluationMatrix (L v) x)) (pi' v), ?_⟩
      · exact liftMatrix_inZOneSix
          (fun i j ↦ hA'Z i j) hxiZ
      · intro v i j
        refine Fin.lastCases ?_ (fun i ↦ ?_) i
        · refine Fin.lastCases ?_ (fun j ↦ ?_) j
          · simp only [insertOmittedPerm_last, min_self]
            rw [homitted_last]
            by_cases hv : v = Place23.infinite
            · subst v
              simp only [if_pos]
              have hs := real_placeNorm_infinite_fin_sum_le_nat_mul
                (fun k ↦ restrictionCoefficient Place23.infinite
                    (basisEvaluationMatrix (L Place23.infinite) x)
                      (pi' Place23.infinite k) *
                  (L Place23.infinite
                      ((maximalCofactorRow Place23.infinite
                        (basisEvaluationMatrix (L Place23.infinite) x)).succAbove
                          (pi' Place23.infinite k))
                        (transformBasis (liftMatrix A' xi) x (Fin.last n)) -
                    L Place23.infinite
                      ((maximalCofactorRow Place23.infinite
                        (basisEvaluationMatrix (L Place23.infinite) x)).succAbove
                          (pi' Place23.infinite k)) (x (Fin.last n))))
                (((n : ℝ) * ((1 / 2 : ℝ) * basisConstant n) + 1) *
                  mu Place23.infinite (Fin.last n))
                (fun k ↦ by
                  have hd := hselected_difference_bound Place23.infinite k
                  simp only [if_pos] at hd
                  simpa only [one_mul] using
                    (real_placeNorm_mul_le_mul Place23.infinite _ _ 1 _
                      (hcoefficient Place23.infinite k)
                      hd
                      (by positivity)))
              have h0 := hbound Place23.infinite
                (maximalCofactorRow Place23.infinite
                  (basisEvaluationMatrix (L Place23.infinite) x)) (Fin.last n)
              calc
                _ ≤ ((placeNorm Place23.infinite
                      (L Place23.infinite
                        (maximalCofactorRow Place23.infinite
                          (basisEvaluationMatrix (L Place23.infinite) x))
                            (x (Fin.last n))) : ℚ) : ℝ) +
                    ((placeNorm Place23.infinite
                      (∑ k, restrictionCoefficient Place23.infinite
                          (basisEvaluationMatrix (L Place23.infinite) x)
                            (pi' Place23.infinite k) *
                        (L Place23.infinite
                            ((maximalCofactorRow Place23.infinite
                              (basisEvaluationMatrix (L Place23.infinite) x)).succAbove
                                (pi' Place23.infinite k))
                              (transformBasis (liftMatrix A' xi) x (Fin.last n)) -
                          L Place23.infinite
                            ((maximalCofactorRow Place23.infinite
                              (basisEvaluationMatrix (L Place23.infinite) x)).succAbove
                                (pi' Place23.infinite k))
                              (x (Fin.last n)))) : ℚ) : ℝ) :=
                  real_placeNorm_infinite_add_le _ _
                _ ≤ mu Place23.infinite (Fin.last n) +
                    (n : ℝ) * (((n : ℝ) * ((1 / 2 : ℝ) * basisConstant n) + 1) *
                      mu Place23.infinite (Fin.last n)) := add_le_add h0 hs
                _ ≤ basisConstant (n + 1) *
                    mu Place23.infinite (Fin.last n) := by
                  calc
                    _ = (1 + (n : ℝ) *
                        ((n : ℝ) * ((1 / 2 : ℝ) * basisConstant n) + 1)) *
                          mu Place23.infinite (Fin.last n) := by ring
                    _ ≤ _ := mul_le_mul_of_nonneg_right
                      (basisConstant_succ_large n)
                      (le_of_lt (hmu Place23.infinite (Fin.last n)))
            · simp only [if_neg hv, one_mul]
              have hs := real_placeNorm_fin_sum_le_of_ne_infinite v hv
                (fun k ↦ restrictionCoefficient v
                    (basisEvaluationMatrix (L v) x) (pi' v k) *
                  (L v ((maximalCofactorRow v
                      (basisEvaluationMatrix (L v) x)).succAbove (pi' v k))
                        (transformBasis (liftMatrix A' xi) x (Fin.last n)) -
                    L v ((maximalCofactorRow v
                      (basisEvaluationMatrix (L v) x)).succAbove (pi' v k))
                        (x (Fin.last n))))
                (mu v (Fin.last n)) (le_of_lt (hmu v _)) (fun k ↦ by
                  simpa only [one_mul] using
                    (real_placeNorm_mul_le_mul v _ _ 1 _
                      (hcoefficient v k)
                      (by simpa only [if_neg hv] using
                        hselected_difference_bound v k) (by positivity)))
              exact (real_placeNorm_add_le_max_of_ne_infinite v hv _ _).trans
                (max_le (hbound v
                  (maximalCofactorRow v (basisEvaluationMatrix (L v) x))
                    (Fin.last n)) hs)
          · simp only [insertOmittedPerm_last,
              transformBasis_liftMatrix_prefix]
            rw [homitted_prefix]
            rw [min_eq_right (hmono v (Fin.le_last _))]
            by_cases hv : v = Place23.infinite
            · subst v
              simp only [if_pos]
              have hs := real_placeNorm_infinite_fin_sum_le_nat_mul
                (fun k ↦ restrictionCoefficient Place23.infinite
                    (basisEvaluationMatrix (L Place23.infinite) x)
                      (pi' Place23.infinite k) *
                  L Place23.infinite
                    ((maximalCofactorRow Place23.infinite
                      (basisEvaluationMatrix (L Place23.infinite) x)).succAbove
                        (pi' Place23.infinite k)) (prefixVector x (A' j)))
                (basisConstant n * mu Place23.infinite (Fin.castSucc j))
                (fun k ↦ by
                  have hp := hprefix_right Place23.infinite k j
                  simp only [if_pos] at hp
                  simpa only [one_mul] using
                    (real_placeNorm_mul_le_mul Place23.infinite _ _ 1 _
                      (hcoefficient Place23.infinite k)
                      hp (by positivity)))
              calc
                _ ≤ (n : ℝ) * (basisConstant n *
                    mu Place23.infinite (Fin.castSucc j)) := hs
                _ = ((n : ℝ) * basisConstant n) *
                    mu Place23.infinite (Fin.castSucc j) := by ring
                _ ≤ basisConstant (n + 1) *
                    mu Place23.infinite (Fin.castSucc j) :=
                  mul_le_mul_of_nonneg_right (nat_mul_basisConstant_le_succ n)
                    (le_of_lt (hmu Place23.infinite _))
            · simp only [if_neg hv, one_mul]
              apply real_placeNorm_fin_sum_le_of_ne_infinite v hv _ _
                (le_of_lt (hmu v _))
              intro k
              simpa only [one_mul] using
                (real_placeNorm_mul_le_mul v _ _ 1 _ (hcoefficient v k)
                  (by simpa only [if_neg hv, one_mul] using hprefix_right v k j)
                  (by positivity))
        · refine Fin.lastCases ?_ (fun j ↦ ?_) j
          · simp only [insertOmittedPerm_castSucc]
            rw [hselected_last]
            rw [min_eq_left (hmono v (Fin.le_last _))]
            by_cases hv : v = Place23.infinite
            · subst v
              simp only [if_pos]
              have hs := real_placeNorm_infinite_fin_sum_le_nat_mul
                (fun k ↦ (xi k + gamma Place23.infinite k) *
                  L Place23.infinite
                    ((maximalCofactorRow Place23.infinite
                      (basisEvaluationMatrix (L Place23.infinite) x)).succAbove
                        (pi' Place23.infinite i)) (prefixVector x (A' k)))
                ((1 / 2 : ℝ) *
                  (basisConstant n * mu Place23.infinite (Fin.castSucc i)))
                (fun k ↦ real_placeNorm_mul_le_mul Place23.infinite _ _ _ _
                  (herror Place23.infinite k) (hprefix_left _ i k) (by positivity))
              calc
                _ ≤ (n : ℝ) * ((1 / 2 : ℝ) *
                    (basisConstant n * mu Place23.infinite (Fin.castSucc i))) := hs
                _ = (((n : ℝ) * (1 / 2 : ℝ)) * basisConstant n) *
                    mu Place23.infinite (Fin.castSucc i) := by ring
                _ ≤ ((n : ℝ) * basisConstant n) *
                    mu Place23.infinite (Fin.castSucc i) := by
                  apply mul_le_mul_of_nonneg_right _ (le_of_lt (hmu _ _))
                  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
                  have hc0 : 0 ≤ basisConstant n :=
                    le_trans zero_le_one (one_le_basisConstant n)
                  nlinarith [mul_nonneg hn hc0]
                _ ≤ basisConstant (n + 1) *
                    mu Place23.infinite (Fin.castSucc i) :=
                  mul_le_mul_of_nonneg_right (nat_mul_basisConstant_le_succ n)
                    (le_of_lt (hmu Place23.infinite _))
            · simp only [if_neg hv, one_mul]
              apply real_placeNorm_fin_sum_le_of_ne_infinite v hv _ _
                (le_of_lt (hmu v _))
              intro k
              simpa only [one_mul] using
                (real_placeNorm_mul_le_mul v _ _ 1 (mu v (Fin.castSucc i))
                  (by simpa only [if_neg hv] using herror v k)
                  (by simpa only [if_neg hv, one_mul] using hprefix_left v i k)
                  (by positivity))
          · simp only [insertOmittedPerm_castSucc,
              transformBasis_liftMatrix_prefix]
            by_cases hv : v = Place23.infinite
            · subst v
              simp only [if_pos]
              exact (hprefix_pair Place23.infinite i j).trans
                (mul_le_mul_of_nonneg_right (basisConstant_le_succ n)
                  (le_min (le_of_lt (hmu _ _)) (le_of_lt (hmu _ _))))
            · simpa only [if_neg hv, one_mul] using hprefix_pair v i j

/-- Uniform form of Evertse's basis lemma.  The constant depends only on the
dimension, and is fixed before the vectors and their local size bounds are
quantified.  At the two finite places the multiplicative constant is exactly
one. -/
theorem exists_evertseBasis {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (hL : IsNonsingularFamily L) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (x : Fin n → Fin n → ℚ) (mu : Place23 → Fin n → ℝ),
        LinearIndependent ℚ x →
        (∀ v i, 0 < mu v i) →
        (∀ v, Monotone (mu v)) →
        (∀ v k j, ((placeNorm v (L v k (x j)) : ℚ) : ℝ) ≤ mu v j) →
        ∃ A : Matrix (Fin n) (Fin n) ℚ,
          IsUnitLowerTriangular A ∧
          (∀ i j, AdelicMinkowski.InZOneSix (fun _ : Fin 1 ↦ A i j)) ∧
          ∃ pi : Place23 → Equiv.Perm (Fin n), ∀ v i j,
            ((placeNorm v (L v (pi v i) (transformBasis A x j)) : ℚ) : ℝ) ≤
              (if v = Place23.infinite then C else 1) *
                min (mu v i) (mu v j) := by
  refine ⟨basisConstant n, one_le_basisConstant n, ?_⟩
  intro x mu hx hmu hmono hbound
  exact evertseBasis_induction n L hL x mu hx hmu hmono hbound

end EvertseBasis

end Erdos407.PadicSubspace
