/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos407.GeneralizedRoth

/-!
# The index of a polynomial along a product of rational hyperplanes

This file supplies the small algebraic bridge which is needed after the
generalized Roth lemma.  There is one nonzero rational linear form in each
block of variables.  We use the triangular change of coordinates from
`GeneralizedRoth`: in the new coordinates the form in a block is its pivot
variable.  Restricting the divided derivative of normal order `I` to the
product of the kernels therefore extracts exactly the terms whose pivot
exponents are `I`.

The important point is that the polynomial itself need not restrict
nontrivially to this product.  What is always true is that *some divided
derivative* restricts nontrivially.  We define the normalized ideal index as
the least weight of such an order and prove that the least weight is attained
by an actual restricted derivative.  Thus an upper bound for the index gives
the derivative needed by the rank-drop argument, without assuming that the
zeroth derivative works.
-/

namespace Erdos407.RestrictionIndex

open scoped BigOperators

noncomputable section

open Erdos407.GeneralizedRoth

/-- A divided-derivative order in the normal direction of every block. -/
abbrev NormalOrder (m : ℕ) := Fin m → ℕ

/-- The normalized weight `sum_j I_j / d_j` of a normal derivative. -/
def normalWeight {m : ℕ} (d : Fin m → ℕ) (I : NormalOrder m) : ℚ :=
  ∑ j : Fin m, (I j : ℚ) / (d j : ℚ)

theorem normalWeight_nonneg {m : ℕ} (d : Fin m → ℕ)
    (I : NormalOrder m) : 0 ≤ normalWeight d I := by
  unfold normalWeight
  positivity

/-- Regard a normal order as an ordinary `RothIndex.MultiIndex`: its only
nonzero entry in a block is at the form-adapted pivot coordinate. -/
def normalMultiIndex {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0) (I : NormalOrder m) : RothIndex.MultiIndex m n :=
  Finsupp.equivFunOnFinite.symm fun v ↦
    if v.2 = pivotIndex (M v.1) (hM v.1) then I v.1 else 0

@[simp] theorem normalMultiIndex_apply {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0) (I : NormalOrder m)
    (v : RothIndex.BlockVar m n) :
    normalMultiIndex M hM I v =
      if v.2 = pivotIndex (M v.1) (hM v.1) then I v.1 else 0 := by
  simp [normalMultiIndex]

@[simp] theorem blockOrder_normalMultiIndex {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0) (I : NormalOrder m) (j : Fin m) :
    RothIndex.blockOrder (normalMultiIndex M hM I) j = I j := by
  classical
  unfold RothIndex.blockOrder
  rw [Finset.sum_eq_single (pivotIndex (M j) (hM j))]
  · simp
  · intro k _ hk
    simp [normalMultiIndex, hk]
  · simp

/-- Our normal weight is literally the existing `RothIndex` weight of the
corresponding pivot-supported multi-index. -/
theorem normalizedWeight_normalMultiIndex {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0) (d : Fin m → ℕ) (I : NormalOrder m) :
    RothIndex.normalizedWeight d (normalMultiIndex M hM I) = normalWeight d I := by
  simp [RothIndex.normalizedWeight, normalWeight]

/-- The exponent of a monomial in the pivot (normal) coordinate of each
block. -/
def normalOrderOfExponent {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0)
    (e : RothIndex.MultiIndex m n) : NormalOrder m :=
  fun j ↦ e (j, pivotIndex (M j) (hM j))

/-- Remove all pivot-coordinate exponents.  This is the exponent left on the
product of kernels after restriction. -/
def tangentialExponent {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0)
    (e : RothIndex.MultiIndex m n) : RothIndex.MultiIndex m n :=
  e.filter (fun v ↦ v.2 ≠ pivotIndex (M v.1) (hM v.1))

@[simp] theorem tangentialExponent_apply {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0) (e : RothIndex.MultiIndex m n)
    (v : RothIndex.BlockVar m n) :
    tangentialExponent M hM e v =
      if v.2 ≠ pivotIndex (M v.1) (hM v.1) then e v else 0 := by
  rfl

@[simp] theorem tangentialExponent_pivot {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0) (e : RothIndex.MultiIndex m n) (j : Fin m) :
    tangentialExponent M hM e (j, pivotIndex (M j) (hM j)) = 0 := by
  simp [tangentialExponent]

theorem tangentialExponent_nonpivot {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0) (e : RothIndex.MultiIndex m n)
    (j : Fin m) (k : Fin (n + 1))
    (hk : k ≠ pivotIndex (M j) (hM j)) :
    tangentialExponent M hM e (j, k) = e (j, k) := by
  simp [tangentialExponent, hk]

/-- Two monomials are equal if their normal orders and their tangential
exponents agree. -/
theorem exponent_eq_of_normalOrderOfExponent_eq_of_tangentialExponent_eq
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    {e f : RothIndex.MultiIndex m n}
    (hnormal : normalOrderOfExponent M hM e = normalOrderOfExponent M hM f)
    (htangent : tangentialExponent M hM e = tangentialExponent M hM f) :
    e = f := by
  ext v
  rcases v with ⟨j, k⟩
  by_cases hk : k = pivotIndex (M j) (hM j)
  · subst k
    exact congrFun hnormal j
  · have h := DFunLike.congr_fun htangent (j, k)
    simpa [tangentialExponent, hk] using h

/-- The polynomial obtained by taking the normal Hasse divided derivative of
order `I` in form-adapted coordinates and then restricting to the product of
the kernels.  The displayed coefficient formula is the usual divided
derivative formula after the pivot variables are set to zero: the binomial
factor is `choose (I j) (I j) = 1`, while all terms of different pivot
degree vanish.

It is useful to retain the ambient variable type; every pivot variable has
exponent zero in this polynomial. -/
def restrictedDividedDerivativeInAdaptedCoordinates {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    (Q : MvPolynomial (RothIndex.BlockVar m n) ℚ) (I : NormalOrder m) :
    MvPolynomial (RothIndex.BlockVar m n) ℚ :=
  ∑ e ∈ Q.support.filter (fun e ↦ normalOrderOfExponent M hM e = I),
    MvPolynomial.monomial (tangentialExponent M hM e)
      (MvPolynomial.coeff e Q)

/-- Take the divided derivative after rewriting the original polynomial in
coordinates adapted to the forms.  Its nonvanishing is exactly
nonvanishing of the derivative on `ker M_1 × ⋯ × ker M_m`. -/
def restrictedDividedDerivative {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) (I : NormalOrder m) :
    MvPolynomial (RothIndex.BlockVar m n) ℚ :=
  restrictedDividedDerivativeInAdaptedCoordinates M hM
    (toFormCoordinates M hM P) I

/-- A term of the adapted polynomial survives in the restricted derivative
of its own normal order. -/
theorem coeff_restrictedDividedDerivativeInAdaptedCoordinates
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    (Q : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    {e : RothIndex.MultiIndex m n} (he : e ∈ Q.support) :
    MvPolynomial.coeff (tangentialExponent M hM e)
        (restrictedDividedDerivativeInAdaptedCoordinates M hM Q
          (normalOrderOfExponent M hM e)) =
      MvPolynomial.coeff e Q := by
  classical
  simp only [restrictedDividedDerivativeInAdaptedCoordinates,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single e]
  · simp
  · intro f hf hfe
    rw [Finset.mem_filter] at hf
    simp only [ite_eq_right_iff]
    intro htangent
    exact (hfe
      (exponent_eq_of_normalOrderOfExponent_eq_of_tangentialExponent_eq
        M hM hf.2 htangent)).elim
  · simp [he]

/-- An order occurs among the adapted monomials exactly when its restricted
divided derivative is nonzero. -/
theorem restrictedDividedDerivativeInAdaptedCoordinates_ne_zero_iff
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    (Q : MvPolynomial (RothIndex.BlockVar m n) ℚ) (I : NormalOrder m) :
    restrictedDividedDerivativeInAdaptedCoordinates M hM Q I ≠ 0 ↔
      ∃ e ∈ Q.support, normalOrderOfExponent M hM e = I := by
  classical
  constructor
  · intro hder
    by_contra hex
    push Not at hex
    apply hder
    have hempty :
        Q.support.filter (fun e ↦ normalOrderOfExponent M hM e = I) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro e he
      exact hex e he
    simp [restrictedDividedDerivativeInAdaptedCoordinates, hempty]
  · rintro ⟨e, he, rfl⟩
    intro hzero
    have hcoeff :=
      coeff_restrictedDividedDerivativeInAdaptedCoordinates M hM Q he
    rw [hzero, MvPolynomial.coeff_zero] at hcoeff
    exact (MvPolynomial.mem_support_iff.mp he) hcoeff.symm

/-- The finite set of normal orders whose restricted divided derivative is
nonzero. -/
def restrictionOrders {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0)
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) : Finset (NormalOrder m) :=
  (toFormCoordinates M hM P).support.image (normalOrderOfExponent M hM)

theorem mem_restrictionOrders_iff {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0)
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) (I : NormalOrder m) :
    I ∈ restrictionOrders M hM P ↔ restrictedDividedDerivative M hM P I ≠ 0 := by
  rw [restrictionOrders, Finset.mem_image]
  simp only [restrictedDividedDerivative,
    restrictedDividedDerivativeInAdaptedCoordinates_ne_zero_iff]

/-- The finite set of weights of nonzero restricted divided derivatives. -/
def restrictionWeights {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0)
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (d : Fin m → ℕ) : Finset ℚ :=
  (restrictionOrders M hM P).image (normalWeight d)

/-- The normalized ideal index of `P` along the product of the kernels of
`M`.  For `P = 0` we totalize the definition by the value zero; substantive
results below assume `P ≠ 0`. -/
def normalizedMIdealIndex {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0)
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (d : Fin m → ℕ) : ℚ :=
  if h : (restrictionWeights M hM P d).Nonempty then
    (restrictionWeights M hM P d).min' h
  else 0

/-- Compatibility with the cycle-free form index used by the quantitative
generalized Roth theorem.  That theorem lives in `GeneralizedRoth`, while
the present file adds the derivative-restriction semantics and extraction
theorems. -/
theorem normalizedMIdealIndex_eq_formIndex {m n : ℕ}
    (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    (P : MvPolynomial (RothIndex.BlockVar m n) ℚ) (d : Fin m → ℕ) :
    normalizedMIdealIndex M hM P d =
      GeneralizedRoth.formIndex M hM P d := by
  rfl

/-- A nonzero polynomial has at least one divided derivative with nonzero
restriction to the product of kernels. -/
theorem restrictionOrders_nonempty {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0) :
    (restrictionOrders M hM P).Nonempty := by
  have hQ : toFormCoordinates M hM P ≠ 0 :=
    toFormCoordinates_ne_zero M hM hP
  exact (MvPolynomial.support_nonempty.mpr hQ).image _

theorem restrictionWeights_nonempty {m n : ℕ} (M : FormFamily m n)
    (hM : ∀ j, M j ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) :
    (restrictionWeights M hM P d).Nonempty :=
  (restrictionOrders_nonempty M hM hP).image _

/-- The minimum in `normalizedMIdealIndex` is attained by an actual normal
divided derivative whose restriction is nonzero. -/
theorem exists_restrictedDividedDerivative_weight_eq_index
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) :
    ∃ I : NormalOrder m,
      restrictedDividedDerivative M hM P I ≠ 0 ∧
      normalWeight d I = normalizedMIdealIndex M hM P d := by
  have hw := restrictionWeights_nonempty M hM hP d
  have hmin : (restrictionWeights M hM P d).min' hw ∈
      restrictionWeights M hM P d := Finset.min'_mem _ _
  obtain ⟨I, hI, hweight⟩ := Finset.mem_image.mp hmin
  refine ⟨I, (mem_restrictionOrders_iff M hM P I).mp hI, ?_⟩
  rw [normalizedMIdealIndex, dif_pos hw]
  exact hweight

/-- Attainment stated with the `GeneralizedRoth.formIndex` name used by the
quantitative theorem. -/
theorem exists_restrictedDividedDerivative_weight_eq_formIndex
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) :
    ∃ I : NormalOrder m,
      restrictedDividedDerivative M hM P I ≠ 0 ∧
      normalWeight d I = GeneralizedRoth.formIndex M hM P d := by
  simpa only [normalizedMIdealIndex_eq_formIndex] using
    (exists_restrictedDividedDerivative_weight_eq_index M hM hP d)

/-- The ideal index is no larger than the weight of any normal divided
derivative which restricts nontrivially. -/
theorem normalizedMIdealIndex_le_weight
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) (I : NormalOrder m)
    (hI : restrictedDividedDerivative M hM P I ≠ 0) :
    normalizedMIdealIndex M hM P d ≤ normalWeight d I := by
  have hw := restrictionWeights_nonempty M hM hP d
  rw [normalizedMIdealIndex, dif_pos hw]
  apply Finset.min'_le
  exact Finset.mem_image.mpr
    ⟨I, (mem_restrictionOrders_iff M hM P I).mpr hI, rfl⟩

theorem normalizedMIdealIndex_nonneg
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) :
    0 ≤ normalizedMIdealIndex M hM P d := by
  obtain ⟨I, _, hweight⟩ :=
    exists_restrictedDividedDerivative_weight_eq_index M hM hP d
  rw [← hweight]
  exact normalWeight_nonneg d I

/-- The bridge consumed by rank drop: every upper bound for the normalized
ideal index supplies a concrete divided derivative of no larger normalized
weight whose restriction to the product of the kernels is nonzero. -/
theorem exists_restrictedDividedDerivative_of_index_le
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) {B : ℚ}
    (hindex : normalizedMIdealIndex M hM P d ≤ B) :
    ∃ I : NormalOrder m,
      normalWeight d I ≤ B ∧
      restrictedDividedDerivative M hM P I ≠ 0 := by
  obtain ⟨I, hI, hweight⟩ :=
    exists_restrictedDividedDerivative_weight_eq_index M hM hP d
  exact ⟨I, hweight.trans_le hindex, hI⟩

/-- Strict-bound variant used when the generalized Roth estimate is strict. -/
theorem exists_restrictedDividedDerivative_of_index_lt
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) {B : ℚ}
    (hindex : normalizedMIdealIndex M hM P d < B) :
    ∃ I : NormalOrder m,
      normalWeight d I < B ∧
      restrictedDividedDerivative M hM P I ≠ 0 := by
  obtain ⟨I, hI, hweight⟩ :=
    exists_restrictedDividedDerivative_weight_eq_index M hM hP d
  exact ⟨I, hweight.trans_lt hindex, hI⟩

/-- Direct adapter for an upper bound proved using the cycle-free
`GeneralizedRoth.formIndex` name. -/
theorem exists_restrictedDividedDerivative_of_formIndex_le
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) {B : ℚ}
    (hindex : GeneralizedRoth.formIndex M hM P d ≤ B) :
    ∃ I : NormalOrder m,
      normalWeight d I ≤ B ∧
      restrictedDividedDerivative M hM P I ≠ 0 := by
  apply exists_restrictedDividedDerivative_of_index_le M hM hP d
  rwa [normalizedMIdealIndex_eq_formIndex]

/-- Strict direct adapter for `GeneralizedRoth.formIndex`. -/
theorem exists_restrictedDividedDerivative_of_formIndex_lt
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) {B : ℚ}
    (hindex : GeneralizedRoth.formIndex M hM P d < B) :
    ∃ I : NormalOrder m,
      normalWeight d I < B ∧
      restrictedDividedDerivative M hM P I ≠ 0 := by
  apply exists_restrictedDividedDerivative_of_index_lt M hM hP d
  rwa [normalizedMIdealIndex_eq_formIndex]

/-- Exact non-strict threshold characterization of the ideal index. -/
theorem normalizedMIdealIndex_le_iff_exists
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    {P : MvPolynomial (RothIndex.BlockVar m n) ℚ} (hP : P ≠ 0)
    (d : Fin m → ℕ) (B : ℚ) :
    normalizedMIdealIndex M hM P d ≤ B ↔
      ∃ I : NormalOrder m,
        normalWeight d I ≤ B ∧
        restrictedDividedDerivative M hM P I ≠ 0 := by
  constructor
  · exact exists_restrictedDividedDerivative_of_index_le M hM hP d
  · rintro ⟨I, hIB, hI⟩
    exact (normalizedMIdealIndex_le_weight M hM hP d I hI).trans hIB

end

end Erdos407.RestrictionIndex
