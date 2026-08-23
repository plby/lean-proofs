/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.NumberTheory.SiegelsLemma

/-!
# Integral auxiliary exponential polynomials for Erdős 240

This module packages the finite-dimensional Siegel-lemma step used in
auxiliary-function proofs for linear forms in logarithms. Its columns are
bounded exponent vectors. A row `(x,t)` asks that the `t`-th forward
difference at the natural point `x` vanish. For an exponential monomial
`z ↦ u ^ z`, that row has the integral value

`u ^ x * (u - 1) ^ t`.

Consequently the construction stays entirely over `ℤ`, while the bases may
be products of arbitrary prescribed integral bases. In the intended
application these are distinct primes, after clearing denominators and
translating the exponent box.
-/

namespace Erdos240.Auxiliary

open scoped BigOperators
open Finset

/- `NumberTheory.SiegelsLemma` uses this entrywise sup norm on matrices. -/
attribute [local instance] Matrix.seminormedAddCommGroup

/-- A column is a bounded exponent vector for `rank` prescribed bases. -/
abbrev ExpColumn (rank width : ℕ) := Fin rank → Fin width

/-- Rows are evaluation points together with forward-difference orders. -/
abbrev ExpRow (points multiplicity : ℕ) := Fin points × Fin multiplicity

@[simp] theorem card_expColumn (rank width : ℕ) :
    Fintype.card (ExpColumn rank width) = width ^ rank := by
  simp [ExpColumn]

@[simp] theorem card_expRow (points multiplicity : ℕ) :
    Fintype.card (ExpRow points multiplicity) = points * multiplicity := by
  simp [ExpRow]

/-- The integral base attached to a bounded exponent vector. -/
def monomialBase {rank width : ℕ} (α : Fin rank → ℤ)
    (l : ExpColumn rank width) : ℤ :=
  ∏ i, α i ^ (l i : ℕ)

/-- A uniform bound for the prescribed integral bases gives a uniform bound
for every base represented by an exponent box. -/
theorem norm_monomialBase_le {rank width : ℕ} (α : Fin rank → ℤ)
    (baseBound : ℝ) (hbase : 1 ≤ baseBound)
    (hα : ∀ i, ‖α i‖ ≤ baseBound) (l : ExpColumn rank width) :
    ‖monomialBase α l‖ ≤ baseBound ^ (rank * (width - 1)) := by
  rw [monomialBase, norm_prod]
  calc
    ∏ i, ‖α i ^ (l i : ℕ)‖
        ≤ ∏ _i : Fin rank, baseBound ^ (width - 1) := by
          refine Finset.prod_le_prod (fun i _ ↦ norm_nonneg (α i ^ (l i : ℕ))) ?_
          intro i _
          rw [norm_pow]
          exact (pow_le_pow_left₀ (norm_nonneg (α i)) (hα i) _).trans
            (pow_le_pow_right₀ hbase (Nat.le_sub_one_of_lt (l i).isLt))
    _ = baseBound ^ ((width - 1) * rank) := by
          simp [pow_mul]
    _ = baseBound ^ (rank * (width - 1)) := by
          rw [Nat.mul_comm]

/-- The exponential polynomial represented by a full coefficient vector. -/
def exponentialPolynomial {rank width : ℕ} (α : Fin rank → ℤ)
    (c : ExpColumn rank width → ℤ) (z : ℕ) : ℤ :=
  ∑ l, c l * monomialBase α l ^ z

/-- Forward difference by one on integer-valued sequences. -/
def forwardDiff (f : ℕ → ℤ) (x : ℕ) : ℤ :=
  f (x + 1) - f x

/-- The `t`-fold forward difference of an integer-valued sequence. -/
def iteratedForwardDiff (t : ℕ) (f : ℕ → ℤ) : ℕ → ℤ :=
  (forwardDiff^[t]) f

/-- Exact forward-difference formula for one integral exponential
monomial. -/
theorem iteratedForwardDiff_pow (u : ℤ) (t x : ℕ) :
    iteratedForwardDiff t (fun z ↦ u ^ z) x =
      u ^ x * (u - 1) ^ t := by
  induction t generalizing x with
  | zero => simp [iteratedForwardDiff]
  | succ t ih =>
      rw [iteratedForwardDiff, Function.iterate_succ_apply']
      simp only [forwardDiff]
      rw [show (forwardDiff^[t]) (fun z ↦ u ^ z) =
          fun y ↦ u ^ y * (u - 1) ^ t by
        funext y
        exact ih y]
      simp only
      rw [pow_succ', pow_succ']
      ring

/-- Exact forward-difference formula for the full auxiliary exponential
polynomial. -/
theorem iteratedForwardDiff_exponentialPolynomial
    {rank width : ℕ} (α : Fin rank → ℤ)
    (c : ExpColumn rank width → ℤ) (t x : ℕ) :
    iteratedForwardDiff t (exponentialPolynomial α c) x =
      ∑ l, c l * (monomialBase α l ^ x *
        (monomialBase α l - 1) ^ t) := by
  induction t generalizing x with
  | zero => simp [iteratedForwardDiff, exponentialPolynomial]
  | succ t ih =>
      rw [iteratedForwardDiff, Function.iterate_succ_apply']
      simp only [forwardDiff]
      rw [show (forwardDiff^[t]) (exponentialPolynomial α c) =
          fun y ↦ ∑ l, c l * (monomialBase α l ^ y *
            (monomialBase α l - 1) ^ t) by
        funext y
        exact ih y]
      simp only
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l _
      rw [pow_succ', pow_succ']
      ring

/-- The integral linear system imposing forward-difference vanishing. The
entry in row `(x,t)` and column `l` is the `t`-th forward difference of the
exponential monomial with base `monomialBase α l`, evaluated at `x`. -/
def constraintMatrix {rank width points multiplicity : ℕ}
    (α : Fin rank → ℤ) :
    Matrix (ExpRow points multiplicity) (ExpColumn rank width) ℤ :=
  fun r l ↦ monomialBase α l ^ (r.1 : ℕ) *
    (monomialBase α l - 1) ^ (r.2 : ℕ)

/-- Explicit entrywise-sup bound for the constraint matrix, in terms of a
uniform bound for the prescribed integral bases. The slightly redundant
exponents `points` and `multiplicity` avoid exceptional zero-dimensional
cases and are convenient when inserted into Siegel's lemma. -/
theorem norm_constraintMatrix_le_of_base_norm_le
    {rank width points multiplicity : ℕ} (α : Fin rank → ℤ)
    (baseBound : ℝ) (hbase : 1 ≤ baseBound)
    (hα : ∀ i, ‖α i‖ ≤ baseBound) :
    ‖constraintMatrix (width := width) (points := points)
        (multiplicity := multiplicity) α‖ ≤
      (baseBound ^ (rank * (width - 1))) ^ points *
        (baseBound ^ (rank * (width - 1)) + 1) ^ multiplicity := by
  let U : ℝ := baseBound ^ (rank * (width - 1))
  have hU : 1 ≤ U := one_le_pow₀ hbase
  have hright : 0 ≤ U ^ points * (U + 1) ^ multiplicity := by positivity
  rw [Matrix.norm_le_iff hright]
  intro r l
  have hmonomial : ‖monomialBase α l‖ ≤ U := by
    exact norm_monomialBase_le α baseBound hbase hα l
  have hsub : ‖monomialBase α l - 1‖ ≤ U + 1 := by
    calc
      ‖monomialBase α l - 1‖ ≤ ‖monomialBase α l‖ + ‖(1 : ℤ)‖ := norm_sub_le _ _
      _ ≤ U + 1 := by simpa using add_le_add_right hmonomial 1
  simp only [constraintMatrix, norm_mul, norm_pow]
  calc
    ‖monomialBase α l‖ ^ (r.1 : ℕ) *
          ‖monomialBase α l - 1‖ ^ (r.2 : ℕ)
        ≤ U ^ (r.1 : ℕ) * (U + 1) ^ (r.2 : ℕ) := by
          calc
            _ ≤ U ^ (r.1 : ℕ) *
                ‖monomialBase α l - 1‖ ^ (r.2 : ℕ) :=
              mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ (norm_nonneg _) hmonomial _) (by positivity)
            _ ≤ U ^ (r.1 : ℕ) * (U + 1) ^ (r.2 : ℕ) :=
              mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ (norm_nonneg _) hsub _) (by positivity)
    _ ≤ U ^ points * (U + 1) ^ multiplicity := by
          calc
            _ ≤ U ^ points * (U + 1) ^ (r.2 : ℕ) :=
              mul_le_mul_of_nonneg_right
                (pow_le_pow_right₀ hU (Nat.le_of_lt r.1.isLt)) (by positivity)
            _ ≤ U ^ points * (U + 1) ^ multiplicity :=
              mul_le_mul_of_nonneg_left
                (pow_le_pow_right₀ (by linarith) (Nat.le_of_lt r.2.isLt)) (by positivity)

theorem constraintMatrix_mulVec_apply
    {rank width points multiplicity : ℕ} (α : Fin rank → ℤ)
    (c : ExpColumn rank width → ℤ) (x : Fin points)
    (t : Fin multiplicity) :
    (constraintMatrix α).mulVec c (x, t) =
      ∑ l, c l * (monomialBase α l ^ (x : ℕ) *
        (monomialBase α l - 1) ^ (t : ℕ)) := by
  classical
  simp only [Matrix.mulVec, dotProduct, constraintMatrix]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- A row of the constraint matrix is exactly the requested iterated
forward difference of the represented exponential polynomial. -/
theorem constraintMatrix_mulVec_apply_eq_iteratedForwardDiff
    {rank width points multiplicity : ℕ} (α : Fin rank → ℤ)
    (c : ExpColumn rank width → ℤ) (x : Fin points)
    (t : Fin multiplicity) :
    (constraintMatrix α).mulVec c (x, t) =
      iteratedForwardDiff (t : ℕ) (exponentialPolynomial α c) (x : ℕ) := by
  rw [constraintMatrix_mulVec_apply,
    iteratedForwardDiff_exponentialPolynomial]

/-- Generic integral Siegel-lemma construction for the exponential
constraint matrix. No property of the bases is needed at this stage. -/
theorem exists_kernel_coefficients
    {rank width points multiplicity : ℕ} (α : Fin rank → ℤ)
    (hunder : Fintype.card (ExpRow points multiplicity) <
      Fintype.card (ExpColumn rank width))
    (hrows : 0 < Fintype.card (ExpRow points multiplicity)) :
    ∃ c : ExpColumn rank width → ℤ,
      c ≠ 0 ∧
      (constraintMatrix (width := width) (points := points)
        (multiplicity := multiplicity) α).mulVec c = 0 ∧
      ‖c‖ ≤
        (Fintype.card (ExpColumn rank width) *
            max 1 ‖constraintMatrix (width := width) (points := points)
              (multiplicity := multiplicity) α‖) ^
          ((Fintype.card (ExpRow points multiplicity) : ℝ) /
            (Fintype.card (ExpColumn rank width) -
              Fintype.card (ExpRow points multiplicity))) := by
  classical
  exact Int.Matrix.exists_ne_zero_int_vec_norm_le
    (constraintMatrix (width := width) (points := points)
      (multiplicity := multiplicity) α) hunder hrows

/-- The same construction with the dimension hypotheses stated only in
terms of the four natural parameters. -/
theorem exists_kernel_coefficients_of_card
    {rank width points multiplicity : ℕ} (α : Fin rank → ℤ)
    (hunder : points * multiplicity < width ^ rank)
    (hpoints : 0 < points) (hmultiplicity : 0 < multiplicity) :
    ∃ c : ExpColumn rank width → ℤ,
      c ≠ 0 ∧
      (constraintMatrix (width := width) (points := points)
        (multiplicity := multiplicity) α).mulVec c = 0 ∧
      ‖c‖ ≤
        (((width ^ rank : ℕ) : ℝ) *
            max 1 ‖constraintMatrix (width := width) (points := points)
              (multiplicity := multiplicity) α‖) ^
          (((points * multiplicity : ℕ) : ℝ) /
            (((width ^ rank : ℕ) : ℝ) -
              ((points * multiplicity : ℕ) : ℝ))) := by
  classical
  have hrows : 0 < Fintype.card (ExpRow points multiplicity) := by
    simp only [card_expRow]
    exact Nat.mul_pos hpoints hmultiplicity
  have hunder' : Fintype.card (ExpRow points multiplicity) <
      Fintype.card (ExpColumn rank width) := by
    simpa only [card_expColumn, card_expRow] using hunder
  simpa only [card_expColumn, card_expRow] using
    (exists_kernel_coefficients (width := width) (points := points)
      (multiplicity := multiplicity) α hunder' hrows)

/-- Siegel's coefficient estimate with the matrix norm eliminated in favour
of a uniform bound for the prescribed integral bases. The preceding theorem
retains the sharper exact matrix-norm estimate. -/
theorem exists_kernel_coefficients_of_base_norm_le
    {rank width points multiplicity : ℕ} (α : Fin rank → ℤ)
    (baseBound : ℝ) (hbase : 1 ≤ baseBound)
    (hα : ∀ i, ‖α i‖ ≤ baseBound)
    (hunder : points * multiplicity < width ^ rank)
    (hpoints : 0 < points) (hmultiplicity : 0 < multiplicity) :
    ∃ c : ExpColumn rank width → ℤ,
      c ≠ 0 ∧
      (constraintMatrix (width := width) (points := points)
        (multiplicity := multiplicity) α).mulVec c = 0 ∧
      ‖c‖ ≤
        (((width ^ rank : ℕ) : ℝ) *
            ((baseBound ^ (rank * (width - 1))) ^ points *
              (baseBound ^ (rank * (width - 1)) + 1) ^ multiplicity)) ^
          (((points * multiplicity : ℕ) : ℝ) /
            (((width ^ rank : ℕ) : ℝ) -
              ((points * multiplicity : ℕ) : ℝ))) := by
  classical
  obtain ⟨c, hc, hkernel, hbound⟩ :=
    exists_kernel_coefficients_of_card α hunder hpoints hmultiplicity
  refine ⟨c, hc, hkernel, hbound.trans ?_⟩
  let U : ℝ := baseBound ^ (rank * (width - 1))
  let matrixBound : ℝ := U ^ points * (U + 1) ^ multiplicity
  have hU : 1 ≤ U := one_le_pow₀ hbase
  have hmatrix_one : 1 ≤ matrixBound := by
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hU)
      (one_le_pow₀ (by linarith))
  have hmatrix :
      ‖constraintMatrix (width := width) (points := points)
          (multiplicity := multiplicity) α‖ ≤ matrixBound := by
    exact norm_constraintMatrix_le_of_base_norm_le α baseBound hbase hα
  have hmax :
      max 1 ‖constraintMatrix (width := width) (points := points)
        (multiplicity := multiplicity) α‖ ≤ matrixBound :=
    max_le hmatrix_one hmatrix
  have hbase_product :
      (((width ^ rank : ℕ) : ℝ) *
          max 1 ‖constraintMatrix (width := width) (points := points)
            (multiplicity := multiplicity) α‖) ≤
        (((width ^ rank : ℕ) : ℝ) * matrixBound) := by
    exact mul_le_mul_of_nonneg_left hmax (by positivity)
  have hexponent :
      0 ≤ (((points * multiplicity : ℕ) : ℝ) /
        (((width ^ rank : ℕ) : ℝ) -
          ((points * multiplicity : ℕ) : ℝ))) := by
    have hdim : ((points * multiplicity : ℕ) : ℝ) ≤
        ((width ^ rank : ℕ) : ℝ) := by
      exact_mod_cast hunder.le
    exact div_nonneg (by positivity) (sub_nonneg.mpr hdim)
  exact Real.rpow_le_rpow (by positivity) hbase_product hexponent

/-- Expanded form of all the vanishing equations delivered by the kernel
vector. -/
theorem exists_auxiliary_exponentialPolynomial
    {rank width points multiplicity : ℕ} (α : Fin rank → ℤ)
    (hunder : points * multiplicity < width ^ rank)
    (hpoints : 0 < points) (hmultiplicity : 0 < multiplicity) :
    ∃ c : ExpColumn rank width → ℤ,
      c ≠ 0 ∧
      (∀ x : Fin points, ∀ t : Fin multiplicity,
        ∑ l, c l * (monomialBase α l ^ (x : ℕ) *
          (monomialBase α l - 1) ^ (t : ℕ)) = 0) ∧
      ‖c‖ ≤
        (((width ^ rank : ℕ) : ℝ) *
            max 1 ‖constraintMatrix (width := width) (points := points)
              (multiplicity := multiplicity) α‖) ^
          (((points * multiplicity : ℕ) : ℝ) /
            (((width ^ rank : ℕ) : ℝ) -
              ((points * multiplicity : ℕ) : ℝ))) := by
  classical
  obtain ⟨c, hc, hkernel, hbound⟩ :=
    exists_kernel_coefficients_of_card α hunder hpoints hmultiplicity
  refine ⟨c, hc, ?_, hbound⟩
  intro x t
  have hz := congrFun hkernel (x, t)
  rw [constraintMatrix_mulVec_apply] at hz
  exact hz

/-- A nonzero coefficient vector of controlled height whose exponential
polynomial has every iterated forward difference of order below
`multiplicity` vanishing at every point below `points`. -/
theorem exists_auxiliary_exponentialPolynomial_forwardDiff
    {rank width points multiplicity : ℕ} (α : Fin rank → ℤ)
    (hunder : points * multiplicity < width ^ rank)
    (hpoints : 0 < points) (hmultiplicity : 0 < multiplicity) :
    ∃ c : ExpColumn rank width → ℤ,
      c ≠ 0 ∧
      (∀ x : Fin points, ∀ t : Fin multiplicity,
        iteratedForwardDiff (t : ℕ) (exponentialPolynomial α c) (x : ℕ) = 0) ∧
      ‖c‖ ≤
        (((width ^ rank : ℕ) : ℝ) *
            max 1 ‖constraintMatrix (width := width) (points := points)
              (multiplicity := multiplicity) α‖) ^
          (((points * multiplicity : ℕ) : ℝ) /
            (((width ^ rank : ℕ) : ℝ) -
              ((points * multiplicity : ℕ) : ℝ))) := by
  classical
  obtain ⟨c, hc, hvanish, hbound⟩ :=
    exists_auxiliary_exponentialPolynomial α hunder hpoints hmultiplicity
  refine ⟨c, hc, ?_, hbound⟩
  intro x t
  rw [iteratedForwardDiff_exponentialPolynomial]
  exact hvanish x t

#print axioms Erdos240.Auxiliary.exists_kernel_coefficients
#print axioms Erdos240.Auxiliary.exists_kernel_coefficients_of_base_norm_le
#print axioms Erdos240.Auxiliary.exists_auxiliary_exponentialPolynomial
#print axioms Erdos240.Auxiliary.exists_auxiliary_exponentialPolynomial_forwardDiff

end Erdos240.Auxiliary
