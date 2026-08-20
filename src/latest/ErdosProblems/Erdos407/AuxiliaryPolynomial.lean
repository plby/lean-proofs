/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.NumberTheory.SiegelsLemma

/-!
# Auxiliary multihomogeneous polynomials

This file packages the finite-dimensional linear-algebra part of the auxiliary-polynomial
construction used in rational Subspace-Theorem arguments.  Variables are split into finitely
many blocks of a common size.  A basis index records an exact degree in every block, so every
polynomial obtained from a coefficient vector is multihomogeneous by construction.

The main result, `exists_multihomogeneous_polynomial_in_kernel`, applies Mathlib's elementary
Siegel lemma to an arbitrary finite family of integral linear conditions.  The specialization
`exists_auxiliaryPolynomial` takes the conditions to be divided (Hasse) partial derivatives at
finitely many integral points.  Keeping the general matrix version available is useful when the
linear conditions are transformed coefficients rather than point evaluations.
-/

namespace Erdos407.AuxiliaryPolynomial

open scoped BigOperators

open Finset

/- `NumberTheory.SiegelsLemma` uses this sup norm on matrices locally.  We activate the same
instance here so that its explicit bound can be stated and reused. -/
attribute [local instance] Matrix.seminormedAddCommGroup

/-- A variable is a block number together with a coordinate inside that block. -/
abbrev BlockVar (blocks vars : ℕ) := Fin blocks × Fin vars

/-- Exponent vectors in one block, of exact total degree `degree`.

The `Fin (degree + 1)` codomain makes the type manifestly finite. -/
abbrev BlockExponent (vars degree : ℕ) :=
  {e : Fin vars → Fin (degree + 1) // ∑ i, (e i : ℕ) = degree}

/-- The monomial basis with prescribed degree `degree b` in each block `b`. -/
abbrev MonomialIndex (blocks vars : ℕ) (degree : Fin blocks → ℕ) :=
  ∀ b, BlockExponent vars (degree b)

/-- The exponent of a variable in a basis monomial. -/
def exponent {blocks vars : ℕ} {degree : Fin blocks → ℕ}
    (m : MonomialIndex blocks vars degree) (v : BlockVar blocks vars) : ℕ :=
  (m v.1).1 v.2

@[simp] theorem sum_exponent_block {blocks vars : ℕ}
    {degree : Fin blocks → ℕ} (m : MonomialIndex blocks vars degree) (b : Fin blocks) :
    ∑ j, exponent m (b, j) = degree b :=
  (m b).2

/-- Turn a block exponent into the ordinary finitely-supported exponent used by `MvPolynomial`. -/
noncomputable def toFinsupp {blocks vars : ℕ} {degree : Fin blocks → ℕ}
    (m : MonomialIndex blocks vars degree) : BlockVar blocks vars →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (exponent m)

@[simp] theorem toFinsupp_apply {blocks vars : ℕ}
    {degree : Fin blocks → ℕ} (m : MonomialIndex blocks vars degree)
    (v : BlockVar blocks vars) :
    toFinsupp m v = exponent m v := by
  simp [toFinsupp]

theorem exponent_injective {blocks vars : ℕ} {degree : Fin blocks → ℕ} :
    Function.Injective
      (exponent : MonomialIndex blocks vars degree → BlockVar blocks vars → ℕ) := by
  intro m n h
  funext b
  apply Subtype.ext
  funext j
  apply Fin.ext
  exact congrFun h (b, j)

theorem toFinsupp_injective {blocks vars : ℕ} {degree : Fin blocks → ℕ} :
    Function.Injective
      (toFinsupp : MonomialIndex blocks vars degree → BlockVar blocks vars →₀ ℕ) := by
  intro m n h
  apply exponent_injective
  funext v
  simpa only [toFinsupp_apply] using DFunLike.congr_fun h v

/-- The multihomogeneous polynomial represented by its full finite coefficient vector. -/
noncomputable def ofCoefficients {R : Type*} [CommSemiring R]
    {blocks vars : ℕ} {degree : Fin blocks → ℕ}
    (c : MonomialIndex blocks vars degree → R) :
    MvPolynomial (BlockVar blocks vars) R :=
  ∑ m, MvPolynomial.monomial (toFinsupp m) (c m)

@[simp] theorem coeff_ofCoefficients {R : Type*} [CommSemiring R]
    {blocks vars : ℕ} {degree : Fin blocks → ℕ}
    (c : MonomialIndex blocks vars degree → R) (m : MonomialIndex blocks vars degree) :
    MvPolynomial.coeff (toFinsupp m) (ofCoefficients c) = c m := by
  classical
  simp only [ofCoefficients, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single m]
  · simp
  · intro n _ hnm
    simp only [ite_eq_right_iff]
    intro h
    exact (hnm (toFinsupp_injective h)).elim
  · simp

/-- Every monomial occurring in `ofCoefficients c` belongs to the prescribed block basis. -/
theorem exists_index_of_mem_support {R : Type*} [CommSemiring R]
    {blocks vars : ℕ} {degree : Fin blocks → ℕ}
    (c : MonomialIndex blocks vars degree → R)
    {e : BlockVar blocks vars →₀ ℕ} (he : e ∈ (ofCoefficients c).support) :
    ∃ m : MonomialIndex blocks vars degree, toFinsupp m = e := by
  classical
  rw [MvPolynomial.mem_support_iff] at he
  by_contra h
  push Not at h
  simp only [ofCoefficients, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial] at he
  simp [h] at he

/-- `ofCoefficients c` is multihomogeneous of multidegree `degree`: each exponent in its support
has the prescribed total degree in every block. -/
theorem blockDegree_of_mem_support {R : Type*} [CommSemiring R]
    {blocks vars : ℕ} {degree : Fin blocks → ℕ}
    (c : MonomialIndex blocks vars degree → R)
    {e : BlockVar blocks vars →₀ ℕ} (he : e ∈ (ofCoefficients c).support)
    (b : Fin blocks) :
    ∑ j, e (b, j) = degree b := by
  obtain ⟨m, rfl⟩ := exists_index_of_mem_support c he
  simpa only [toFinsupp_apply] using sum_exponent_block m b

theorem ofCoefficients_ne_zero {R : Type*} [CommSemiring R] [Nontrivial R]
    {blocks vars : ℕ} {degree : Fin blocks → ℕ}
    {c : MonomialIndex blocks vars degree → R} (hc : c ≠ 0) :
    ofCoefficients c ≠ 0 := by
  intro hp
  apply hc
  funext m
  have := coeff_ofCoefficients c m
  rw [hp, MvPolynomial.coeff_zero] at this
  exact this.symm

/-! ## Divided partial derivatives -/

/-- The value at `x` of the divided derivative of `X^e` of multiorder `order`.

This is the multivariate Hasse derivative convention: its coefficient is
`∏ v, (e v).choose (order v)`.  It is integral and therefore is the convenient convention for
the Siegel-lemma matrix. -/
def dividedMonomial {R : Type*} [CommSemiring R] {V : Type*} [Fintype V]
    (order : V → ℕ) (e : V →₀ ℕ) (x : V → R) : R :=
  ∏ v, (Nat.choose (e v) (order v) : R) * x v ^ (e v - order v)

/-- Evaluate a divided partial derivative of an arbitrary multivariate polynomial. -/
noncomputable def dividedDerivativeEval {R : Type*} [CommSemiring R]
    {V : Type*} [Fintype V] (order : V → ℕ) (x : V → R)
    (P : MvPolynomial V R) : R :=
  (AddMonoidAlgebra.coeff P).sum fun e a ↦ a * dividedMonomial order e x

@[simp] theorem dividedDerivativeEval_monomial {R : Type*} [CommSemiring R]
    {V : Type*} [Fintype V] (order : V → ℕ) (x : V → R)
    (e : V →₀ ℕ) (a : R) :
    dividedDerivativeEval order x (MvPolynomial.monomial e a) =
      a * dividedMonomial order e x := by
  classical
  simp [dividedDerivativeEval]

@[simp] theorem dividedDerivativeEval_zero {R : Type*} [CommSemiring R]
    {V : Type*} [Fintype V] (order : V → ℕ) (x : V → R) :
    dividedDerivativeEval order x (0 : MvPolynomial V R) = 0 := by
  simp [dividedDerivativeEval]

@[simp] theorem dividedDerivativeEval_add {R : Type*} [CommSemiring R]
    {V : Type*} [Fintype V] (order : V → ℕ) (x : V → R)
    (P Q : MvPolynomial V R) :
    dividedDerivativeEval order x (P + Q) =
      dividedDerivativeEval order x P + dividedDerivativeEval order x Q := by
  classical
  unfold dividedDerivativeEval
  rw [AddMonoidAlgebra.coeff_add]
  apply Finsupp.sum_add_index'
  · intro e
    simp
  · intro e a b
    exact add_mul a b (dividedMonomial order e x)

theorem dividedDerivativeEval_ofCoefficients {R : Type*} [CommSemiring R]
    {blocks vars : ℕ} {degree : Fin blocks → ℕ}
    (c : MonomialIndex blocks vars degree → R)
    (order : BlockVar blocks vars → ℕ) (x : BlockVar blocks vars → R) :
    dividedDerivativeEval order x (ofCoefficients c) =
      ∑ m, c m * dividedMonomial order (toFinsupp m) x := by
  classical
  unfold ofCoefficients
  induction (Finset.univ : Finset (MonomialIndex blocks vars degree)) using Finset.induction with
  | empty => simp
  | @insert m s hm ih =>
      rw [Finset.sum_insert hm, dividedDerivativeEval_add,
        dividedDerivativeEval_monomial, ih, Finset.sum_insert hm]

@[simp] theorem dividedMonomial_zero_order {R : Type*} [CommSemiring R]
    {V : Type*} [Fintype V] (e : V →₀ ℕ) (x : V → R) :
    dividedMonomial (fun _ ↦ 0) e x = ∏ v, x v ^ e v := by
  classical
  simp [dividedMonomial]

theorem dividedDerivativeEval_zero_order {R : Type*} [CommSemiring R]
    {V : Type*} [Fintype V] (x : V → R) (P : MvPolynomial V R) :
    dividedDerivativeEval (fun _ ↦ 0) x P = MvPolynomial.eval x P := by
  classical
  simp only [dividedDerivativeEval, dividedMonomial_zero_order]
  rw [MvPolynomial.eval_eq']
  rfl

/-! ## Finite counting bounds -/

theorem card_blockExponent_le (vars degree : ℕ) :
    Fintype.card (BlockExponent vars degree) ≤ (degree + 1) ^ vars := by
  calc
    Fintype.card (BlockExponent vars degree) ≤
        Fintype.card (Fin vars → Fin (degree + 1)) := Fintype.card_subtype_le _
    _ = (degree + 1) ^ vars := by simp

theorem card_monomialIndex_eq_prod (blocks vars : ℕ) (degree : Fin blocks → ℕ) :
    Fintype.card (MonomialIndex blocks vars degree) =
      ∏ b, Fintype.card (BlockExponent vars (degree b)) := by
  simp [MonomialIndex]

theorem card_monomialIndex_le (blocks vars : ℕ) (degree : Fin blocks → ℕ) :
    Fintype.card (MonomialIndex blocks vars degree) ≤
      ∏ b, (degree b + 1) ^ vars := by
  rw [card_monomialIndex_eq_prod]
  exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) fun b _ ↦
    card_blockExponent_le vars (degree b)

/-- The loose but convenient monomial count used when each block has at most five variables. -/
theorem card_monomialIndex_le_fifthPower {blocks vars : ℕ}
    (degree : Fin blocks → ℕ) (hvars : vars ≤ 5) :
    Fintype.card (MonomialIndex blocks vars degree) ≤
      ∏ b, (degree b + 1) ^ 5 := by
  refine (card_monomialIndex_le blocks vars degree).trans ?_
  exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) fun b _ ↦
    Nat.pow_le_pow_right (Nat.zero_lt_succ _) hvars

/-! ## Siegel lemma for arbitrary integral conditions -/

/-- The coefficient vector obtained by Siegel's lemma, together with all properties needed by
an auxiliary-polynomial argument.  `A` may encode point derivatives, transformed coefficients,
or any other finite collection of integral linear conditions. -/
theorem exists_multihomogeneous_polynomial_in_kernel
    {rows : Type*} [Fintype rows] {blocks vars : ℕ} {degree : Fin blocks → ℕ}
    (A : Matrix rows (MonomialIndex blocks vars degree) ℤ)
    (hunder : Fintype.card rows < Fintype.card (MonomialIndex blocks vars degree))
    (hrows : 0 < Fintype.card rows) :
    ∃ c : MonomialIndex blocks vars degree → ℤ,
      c ≠ 0 ∧
      A.mulVec c = 0 ∧
      ofCoefficients c ≠ 0 ∧
      ‖c‖ ≤
        (Fintype.card (MonomialIndex blocks vars degree) * max 1 ‖A‖) ^
          ((Fintype.card rows : ℝ) /
            (Fintype.card (MonomialIndex blocks vars degree) - Fintype.card rows)) := by
  classical
  obtain ⟨c, hc, hAc, hbound⟩ :=
    Int.Matrix.exists_ne_zero_int_vec_norm_le A hunder hrows
  exact ⟨c, hc, hAc, ofCoefficients_ne_zero hc, by simpa using hbound⟩

/-! ## High-order vanishing at finitely many points -/

/-- Multiorders of total order strictly less than `cutoff`.

As with `BlockExponent`, bounding every entry by `cutoff` makes finiteness definitional. -/
abbrev DerivativeIndex (blocks vars cutoff : ℕ) :=
  {a : BlockVar blocks vars → Fin (cutoff + 1) // ∑ v, (a v : ℕ) < cutoff}

/-- Regard a bounded derivative index as an ordinary natural-valued multiindex. -/
def DerivativeIndex.order {blocks vars cutoff : ℕ}
    (a : DerivativeIndex blocks vars cutoff) : BlockVar blocks vars → ℕ :=
  fun v ↦ a.1 v

@[simp] theorem DerivativeIndex.total_order_lt {blocks vars cutoff : ℕ}
    (a : DerivativeIndex blocks vars cutoff) :
    ∑ v, a.order v < cutoff :=
  a.2

/-- The zero multiindex is among the vanishing conditions when the cutoff is positive. -/
theorem derivativeIndex_nonempty {blocks vars cutoff : ℕ} (hcutoff : 0 < cutoff) :
    Nonempty (DerivativeIndex blocks vars cutoff) := by
  classical
  exact ⟨⟨fun _ ↦ 0, by simpa using hcutoff⟩⟩

theorem card_derivativeIndex_le (blocks vars cutoff : ℕ) :
    Fintype.card (DerivativeIndex blocks vars cutoff) ≤
      (cutoff + 1) ^ (blocks * vars) := by
  calc
    Fintype.card (DerivativeIndex blocks vars cutoff) ≤
        Fintype.card (BlockVar blocks vars → Fin (cutoff + 1)) :=
      Fintype.card_subtype_le _
    _ = (cutoff + 1) ^ (blocks * vars) := by simp [BlockVar]

/-- Number of point/derivative conditions, bounded by the enclosing box of multiindices. -/
theorem card_point_derivative_rows_le (points blocks vars cutoff : ℕ) :
    Fintype.card (Fin points × DerivativeIndex blocks vars cutoff) ≤
      points * (cutoff + 1) ^ (blocks * vars) := by
  simpa using Nat.mul_le_mul_left points (card_derivativeIndex_le blocks vars cutoff)

/-- A positive number of points and a positive cutoff give a nonempty system of conditions. -/
theorem card_point_derivative_rows_pos {points blocks vars cutoff : ℕ}
    (hpoints : 0 < points) (hcutoff : 0 < cutoff) :
    0 < Fintype.card (Fin points × DerivativeIndex blocks vars cutoff) := by
  rw [Fintype.card_pos_iff]
  exact ⟨⟨⟨0, hpoints⟩, (derivativeIndex_nonempty hcutoff).some⟩⟩

/-- The integral matrix whose rows are all divided derivatives of total order `< cutoff` at the
given integral points. -/
noncomputable def vanishingMatrix {points blocks vars cutoff : ℕ} {degree : Fin blocks → ℕ}
    (x : Fin points → BlockVar blocks vars → ℤ) :
    Matrix (Fin points × DerivativeIndex blocks vars cutoff)
      (MonomialIndex blocks vars degree) ℤ :=
  fun r m ↦ dividedMonomial r.2.order (toFinsupp m) (x r.1)

theorem vanishingMatrix_mulVec_apply
    {points blocks vars cutoff : ℕ} {degree : Fin blocks → ℕ}
    (x : Fin points → BlockVar blocks vars → ℤ)
    (c : MonomialIndex blocks vars degree → ℤ)
    (p : Fin points) (a : DerivativeIndex blocks vars cutoff) :
    (vanishingMatrix x).mulVec c (p, a) =
      dividedDerivativeEval a.order (x p) (ofCoefficients c) := by
  classical
  rw [dividedDerivativeEval_ofCoefficients]
  simp only [Matrix.mulVec, dotProduct, vanishingMatrix]
  apply Finset.sum_congr rfl
  intro m _
  exact mul_comm _ _

/-- A nonzero integral multihomogeneous polynomial with all divided derivatives of total order
`< cutoff` vanishing at the prescribed integral points, and with the explicit coefficient-height
bound supplied by Mathlib's Siegel lemma. -/
theorem exists_auxiliaryPolynomial
    {points blocks vars cutoff : ℕ} {degree : Fin blocks → ℕ}
    (x : Fin points → BlockVar blocks vars → ℤ)
    (hunder : Fintype.card (Fin points × DerivativeIndex blocks vars cutoff) <
      Fintype.card (MonomialIndex blocks vars degree))
    (hrows : 0 < Fintype.card (Fin points × DerivativeIndex blocks vars cutoff)) :
    ∃ c : MonomialIndex blocks vars degree → ℤ,
      c ≠ 0 ∧
      ofCoefficients c ≠ 0 ∧
      (∀ p : Fin points, ∀ a : DerivativeIndex blocks vars cutoff,
        dividedDerivativeEval a.order (x p) (ofCoefficients c) = 0) ∧
      ‖c‖ ≤
        (Fintype.card (MonomialIndex blocks vars degree) *
            max 1 ‖vanishingMatrix (cutoff := cutoff) (degree := degree) x‖) ^
          ((Fintype.card (Fin points × DerivativeIndex blocks vars cutoff) : ℝ) /
            (Fintype.card (MonomialIndex blocks vars degree) -
              Fintype.card (Fin points × DerivativeIndex blocks vars cutoff))) := by
  classical
  obtain ⟨c, hc, hAc, hPc, hbound⟩ :=
    exists_multihomogeneous_polynomial_in_kernel
      (vanishingMatrix (cutoff := cutoff) (degree := degree) x) hunder hrows
  refine ⟨c, hc, hPc, ?_, ?_⟩
  · intro p a
    have hz := congrFun hAc (p, a)
    exact (vanishingMatrix_mulVec_apply x c p a).symm.trans hz
  · exact hbound

#print axioms exists_multihomogeneous_polynomial_in_kernel
#print axioms exists_auxiliaryPolynomial

end Erdos407.AuxiliaryPolynomial
