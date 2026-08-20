/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.GLRAuxiliary

/-!
# Uniform height estimates for the GLR auxiliary polynomial

The integral coordinate changes used by the auxiliary-polynomial
construction are fixed, while its block degrees tend to infinity.  This
file supplies the elementary estimates showing that the logarithms of all
coefficient bounds grow at most linearly in the total multidegree.
-/

namespace Erdos407.AuxiliaryHeightEstimates

open scoped BigOperators Matrix

attribute [local instance] Matrix.seminormedAddCommGroup

noncomputable section

/-- The coefficient `ℓ¹` norm of an integral multivariate polynomial. -/
def coefficientL1 {σ : Type*} (P : MvPolynomial σ ℤ) : ℝ :=
  ∑ e ∈ P.support, ‖MvPolynomial.coeff e P‖

theorem coefficientL1_nonneg {σ : Type*} (P : MvPolynomial σ ℤ) :
    0 ≤ coefficientL1 P := by
  exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

@[simp] theorem coefficientL1_zero {σ : Type*} :
    coefficientL1 (0 : MvPolynomial σ ℤ) = 0 := by
  simp [coefficientL1]

theorem norm_coeff_le_coefficientL1 {σ : Type*} (P : MvPolynomial σ ℤ)
    (e : σ →₀ ℕ) :
    ‖MvPolynomial.coeff e P‖ ≤ coefficientL1 P := by
  by_cases he : e ∈ P.support
  · exact Finset.single_le_sum
      (fun j _ ↦ norm_nonneg (MvPolynomial.coeff j P)) he
  · rw [MvPolynomial.notMem_support_iff.mp he, norm_zero]
    exact coefficientL1_nonneg P

@[simp] theorem coefficientL1_monomial {σ : Type*} (e : σ →₀ ℕ) (a : ℤ) :
    coefficientL1 (MvPolynomial.monomial e a) = ‖a‖ := by
  classical
  by_cases ha : a = 0
  · subst a
    simp
  · rw [coefficientL1, MvPolynomial.support_monomial]
    simp only [ha, ↓reduceIte, Finset.sum_singleton]
    rw [MvPolynomial.coeff_monomial]
    simp

theorem coefficientL1_add_le {σ : Type*} (P Q : MvPolynomial σ ℤ) :
    coefficientL1 (P + Q) ≤ coefficientL1 P + coefficientL1 Q := by
  classical
  have hsupp : (P + Q).support ⊆ P.support ∪ Q.support :=
    MvPolynomial.support_add
  calc
    coefficientL1 (P + Q) ≤
        ∑ e ∈ P.support ∪ Q.support, ‖MvPolynomial.coeff e (P + Q)‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsupp
        (fun _ _ _ ↦ norm_nonneg _)
    _ ≤ ∑ e ∈ P.support ∪ Q.support,
        (‖MvPolynomial.coeff e P‖ + ‖MvPolynomial.coeff e Q‖) := by
      apply Finset.sum_le_sum
      intro e he
      exact norm_add_le _ _
    _ = (∑ e ∈ P.support ∪ Q.support, ‖MvPolynomial.coeff e P‖) +
        (∑ e ∈ P.support ∪ Q.support, ‖MvPolynomial.coeff e Q‖) := by
      rw [Finset.sum_add_distrib]
    _ = coefficientL1 P + coefficientL1 Q := by
      congr 1
      · symm
        apply Finset.sum_subset (Finset.subset_union_left)
        intro e heU heP
        rw [MvPolynomial.notMem_support_iff.mp heP, norm_zero]
      · symm
        apply Finset.sum_subset (Finset.subset_union_right)
        intro e heU heQ
        rw [MvPolynomial.notMem_support_iff.mp heQ, norm_zero]

/-- Adding a fresh monomial adds its coefficient norm exactly. -/
theorem coefficientL1_monomial_add_of_not_mem {σ : Type*}
    (e : σ →₀ ℕ) (a : ℤ) (P : MvPolynomial σ ℤ)
    (he : e ∉ P.support) (ha : a ≠ 0) :
    coefficientL1 (MvPolynomial.monomial e a + P) = ‖a‖ + coefficientL1 P := by
  classical
  unfold coefficientL1
  have hsupp : (MvPolynomial.monomial e a + P).support =
      Finset.cons e P.support he := by
    exact Finsupp.support_single_add he ha
  rw [hsupp, Finset.sum_cons]
  have hecoeff : MvPolynomial.coeff e P = 0 :=
    MvPolynomial.notMem_support_iff.mp he
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_monomial, if_pos rfl,
    hecoeff, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro f hf
  have hef : e ≠ f := by
    intro hef
    subst f
    exact he hf
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_monomial, if_neg hef, zero_add]

/-- Multiplication by one monomial is bounded by the product of coefficient
`ℓ¹` norms. -/
theorem coefficientL1_monomial_mul_le {σ : Type*} (e : σ →₀ ℕ) (a : ℤ)
    (Q : MvPolynomial σ ℤ) :
    coefficientL1 (MvPolynomial.monomial e a * Q) ≤ ‖a‖ * coefficientL1 Q := by
  classical
  induction Q using AddMonoidAlgebra.induction with
  | zero => simp
  | @single_add f b Q hf hb ih =>
      change coefficientL1
          (MvPolynomial.monomial e a * (MvPolynomial.monomial f b + Q)) ≤ _
      rw [mul_add]
      calc
        coefficientL1
            (MvPolynomial.monomial e a * MvPolynomial.monomial f b +
              MvPolynomial.monomial e a * Q) ≤
            coefficientL1
                (MvPolynomial.monomial e a * MvPolynomial.monomial f b) +
              coefficientL1 (MvPolynomial.monomial e a * Q) :=
          coefficientL1_add_le _ _
        _ ≤ ‖a‖ * ‖b‖ + ‖a‖ * coefficientL1 Q := by
          rw [MvPolynomial.monomial_mul, coefficientL1_monomial, norm_mul]
          exact add_le_add (le_refl _) ih
        _ = ‖a‖ * coefficientL1 (MvPolynomial.monomial f b + Q) := by
          rw [coefficientL1_monomial_add_of_not_mem f b Q hf hb]
          ring

/-- The coefficient `ℓ¹` norm is submultiplicative. -/
theorem coefficientL1_mul_le {σ : Type*} (P Q : MvPolynomial σ ℤ) :
    coefficientL1 (P * Q) ≤ coefficientL1 P * coefficientL1 Q := by
  classical
  induction P using AddMonoidAlgebra.induction with
  | zero => simp
  | @single_add e a P he ha ih =>
      change coefficientL1 ((MvPolynomial.monomial e a + P) * Q) ≤ _
      rw [add_mul]
      calc
        coefficientL1
            (MvPolynomial.monomial e a * Q + P * Q) ≤
            coefficientL1 (MvPolynomial.monomial e a * Q) +
              coefficientL1 (P * Q) := coefficientL1_add_le _ _
        _ ≤ ‖a‖ * coefficientL1 Q + coefficientL1 P * coefficientL1 Q :=
          add_le_add (coefficientL1_monomial_mul_le e a Q) ih
        _ = coefficientL1 (MvPolynomial.monomial e a + P) * coefficientL1 Q := by
          rw [coefficientL1_monomial_add_of_not_mem e a P he ha]
          ring

@[simp] theorem coefficientL1_one {σ : Type*} :
    coefficientL1 (1 : MvPolynomial σ ℤ) = 1 := by
  classical
  rw [coefficientL1, MvPolynomial.support_one]
  simp

theorem coefficientL1_pow_le {σ : Type*} (P : MvPolynomial σ ℤ) (d : ℕ) :
    coefficientL1 (P ^ d) ≤ coefficientL1 P ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [pow_succ, pow_succ]
      exact (coefficientL1_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right ih (coefficientL1_nonneg P))

theorem coefficientL1_sum_le {ι σ : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ ℤ) :
    coefficientL1 (∑ i ∈ s, P i) ≤ ∑ i ∈ s, coefficientL1 (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (coefficientL1_add_le _ _).trans (add_le_add (le_refl _) ih)

theorem coefficientL1_prod_le {ι σ : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ ℤ) :
    coefficientL1 (∏ i ∈ s, P i) ≤ ∏ i ∈ s, coefficientL1 (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      exact (coefficientL1_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left ih (coefficientL1_nonneg (P i)))

@[simp] theorem coefficientL1_C_mul_X {σ : Type*} (a : ℤ) (x : σ) :
    coefficientL1 (MvPolynomial.C a * MvPolynomial.X x) = ‖a‖ := by
  rw [MvPolynomial.X, MvPolynomial.C_mul_monomial,
    coefficientL1_monomial, mul_one]

/-- A fixed base, at least one, which controls every row sum of every
coordinate-change matrix. -/
def coordinateChangeBase {coords : ℕ}
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ) : ℝ :=
  max 1 ((coords : ℝ) * ‖T‖)

theorem one_le_coordinateChangeBase {coords : ℕ}
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ) :
    1 ≤ coordinateChangeBase T :=
  le_max_left _ _

theorem coordinateChangeBase_nonneg {coords : ℕ}
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ) :
    0 ≤ coordinateChangeBase T :=
  zero_le_one.trans (one_le_coordinateChangeBase T)

/-- Every changed coordinate linear form has coefficient `ℓ¹` norm at
most the fixed coordinate-change base. -/
theorem coefficientL1_coordinateForm_le {blocks coords : ℕ}
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (v : GLRAuxiliary.Place23)
    (x : AuxiliaryPolynomial.BlockVar blocks coords) :
    coefficientL1
        (∑ j, MvPolynomial.C (T v x.2 j) * MvPolynomial.X (x.1, j)) ≤
      coordinateChangeBase T := by
  classical
  calc
    coefficientL1
        (∑ j, MvPolynomial.C (T v x.2 j) * MvPolynomial.X (x.1, j)) ≤
        ∑ j, coefficientL1
          (MvPolynomial.C (T v x.2 j) * MvPolynomial.X (x.1, j)) := by
      simpa using coefficientL1_sum_le Finset.univ
        (fun j ↦ MvPolynomial.C (T v x.2 j) * MvPolynomial.X (x.1, j))
    _ = ∑ j, ‖T v x.2 j‖ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact coefficientL1_C_mul_X _ _
    _ ≤ ∑ _j : Fin coords, ‖T‖ := by
      apply Finset.sum_le_sum
      intro j hj
      exact (Matrix.norm_entry_le_entrywise_sup_norm (T v)).trans
        (norm_le_pi_norm T v)
    _ = (coords : ℝ) * ‖T‖ := by simp
    _ ≤ coordinateChangeBase T := le_max_right _ _

@[simp] theorem coefficientL1_C {σ : Type*} (a : ℤ) :
    coefficientL1 (MvPolynomial.C a : MvPolynomial σ ℤ) = ‖a‖ := by
  rw [MvPolynomial.C_apply, coefficientL1_monomial]

theorem coefficientL1_finsuppProd_pow_le {blocks coords : ℕ}
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (v : GLRAuxiliary.Place23)
    (e : AuxiliaryPolynomial.BlockVar blocks coords →₀ ℕ) :
    coefficientL1
        (e.prod fun x k ↦
          (∑ j, MvPolynomial.C (T v x.2 j) * MvPolynomial.X (x.1, j)) ^ k) ≤
      coordinateChangeBase T ^ e.degree := by
  classical
  let F : AuxiliaryPolynomial.BlockVar blocks coords →
      MvPolynomial (AuxiliaryPolynomial.BlockVar blocks coords) ℤ :=
    fun x ↦ ∑ j, MvPolynomial.C (T v x.2 j) * MvPolynomial.X (x.1, j)
  have hprod : coefficientL1 (e.prod fun x k ↦ F x ^ k) ≤
      ∏ x ∈ e.support, coefficientL1 (F x ^ e x) := by
    simpa [Finsupp.prod] using coefficientL1_prod_le e.support
      (fun x ↦ F x ^ e x)
  have hterm : ∀ x, coefficientL1 (F x ^ e x) ≤
      coordinateChangeBase T ^ e x := by
    intro x
    exact (coefficientL1_pow_le (F x) (e x)).trans
      (pow_le_pow_left₀ (coefficientL1_nonneg (F x))
        (coefficientL1_coordinateForm_le T v x) _)
  have hsum : ∑ x ∈ e.support, e x = e.degree := by
    rw [Finsupp.degree_eq_sum]
    apply Finset.sum_subset (Finset.subset_univ e.support)
    intro x hxU hx
    exact Finsupp.notMem_support_iff.mp hx
  calc
    coefficientL1 (e.prod fun x k ↦ F x ^ k) ≤
        ∏ x ∈ e.support, coefficientL1 (F x ^ e x) := hprod
    _ ≤ ∏ x ∈ e.support, coordinateChangeBase T ^ e x := by
      exact Finset.prod_le_prod (fun x _ ↦ coefficientL1_nonneg (F x ^ e x))
        (fun x _ ↦ hterm x)
    _ = coordinateChangeBase T ^ e.degree := by
      rw [Finset.prod_pow_eq_pow_sum, hsum]

/-- A changed basis monomial has exponentially bounded coefficient norm,
with a base depending only on the fixed coordinate matrices. -/
theorem coefficientL1_changeCoordinates_monomial_le {blocks coords : ℕ}
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (v : GLRAuxiliary.Place23)
    (e : AuxiliaryPolynomial.BlockVar blocks coords →₀ ℕ) (a : ℤ) :
    coefficientL1
        (GLRAuxiliary.changeCoordinates T v (MvPolynomial.monomial e a)) ≤
      ‖a‖ * coordinateChangeBase T ^ e.degree := by
  rw [GLRAuxiliary.changeCoordinates, MvPolynomial.eval₂Hom_monomial]
  calc
    coefficientL1
        (MvPolynomial.C a *
          e.prod fun x k ↦
            (∑ j, MvPolynomial.C (T v x.2 j) * MvPolynomial.X (x.1, j)) ^ k) ≤
        coefficientL1 (MvPolynomial.C a) * coefficientL1
          (e.prod fun x k ↦
            (∑ j, MvPolynomial.C (T v x.2 j) * MvPolynomial.X (x.1, j)) ^ k) :=
      coefficientL1_mul_le _ _
    _ ≤ ‖a‖ * coordinateChangeBase T ^ e.degree := by
      rw [coefficientL1_C]
      exact mul_le_mul_of_nonneg_left
        (coefficientL1_finsuppProd_pow_le T v e) (norm_nonneg a)

/-- Total degree over all blocks. -/
def totalDegree {blocks : ℕ} (degree : Fin blocks → ℕ) : ℕ :=
  ∑ h, degree h

@[simp] theorem toFinsupp_degree {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (M : AuxiliaryPolynomial.MonomialIndex blocks coords degree) :
    (AuxiliaryPolynomial.toFinsupp M).degree = totalDegree degree := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  simp [totalDegree, AuxiliaryPolynomial.toFinsupp_apply,
    AuxiliaryPolynomial.sum_exponent_block]

theorem residualFinsupp_degree_le {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (I : GLRAuxiliary.DerivativeIndex blocks coords degree)
    (M : AuxiliaryPolynomial.MonomialIndex blocks coords degree) :
    (AuxiliaryPolynomial.toFinsupp M - GLRAuxiliary.orderFinsupp I).degree ≤
      totalDegree degree := by
  rw [Finsupp.degree_eq_sum, ← toFinsupp_degree M, Finsupp.degree_eq_sum]
  exact Finset.sum_le_sum fun x _ ↦ Nat.sub_le _ _

theorem norm_chooseProduct_le_two_pow_totalDegree {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (I : GLRAuxiliary.DerivativeIndex blocks coords degree)
    (M : AuxiliaryPolynomial.MonomialIndex blocks coords degree) :
    ‖(∏ x, (Nat.choose (AuxiliaryPolynomial.exponent M x)
        (I.order x) : ℤ))‖ ≤
      (2 : ℝ) ^ totalDegree degree := by
  rw [norm_prod]
  calc
    ∏ x, ‖(Nat.choose (AuxiliaryPolynomial.exponent M x) (I.order x) : ℤ)‖ ≤
        ∏ x, (2 : ℝ) ^ AuxiliaryPolynomial.exponent M x := by
      apply Finset.prod_le_prod (fun x _ ↦ norm_nonneg _)
      intro x hx
      rw [Int.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact_mod_cast Nat.choose_le_two_pow
        (AuxiliaryPolynomial.exponent M x) (I.order x)
    _ = (2 : ℝ) ^ ∑ x, AuxiliaryPolynomial.exponent M x := by
      rw [Finset.prod_pow_eq_pow_sum]
    _ = (2 : ℝ) ^ totalDegree degree := by
      congr 1
      rw [Fintype.sum_prod_type]
      simp [totalDegree, AuxiliaryPolynomial.sum_exponent_block]

/-- Every entry of the full divided-derivative coefficient matrix is bounded
by a fixed base to the total multidegree. -/
theorem norm_basisTransformedCoefficient_le {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (v : GLRAuxiliary.Place23)
    (I : GLRAuxiliary.DerivativeIndex blocks coords degree)
    (J : GLRAuxiliary.ResidualMonomialIndex I)
    (M : AuxiliaryPolynomial.MonomialIndex blocks coords degree) :
    ‖GLRAuxiliary.basisTransformedCoefficient T v I J M‖ ≤
      (2 * coordinateChangeBase T) ^ totalDegree degree := by
  let e := AuxiliaryPolynomial.toFinsupp M - GLRAuxiliary.orderFinsupp I
  let a : ℤ := ∏ x, (Nat.choose (AuxiliaryPolynomial.exponent M x)
    (I.order x) : ℤ)
  calc
    ‖GLRAuxiliary.basisTransformedCoefficient T v I J M‖ ≤
        coefficientL1
          (GLRAuxiliary.changeCoordinates T v
            (GLRAuxiliary.dividedDerivativeMonomial I M)) := by
      exact norm_coeff_le_coefficientL1 _ _
    _ = coefficientL1
          (GLRAuxiliary.changeCoordinates T v (MvPolynomial.monomial e a)) := rfl
    _ ≤ ‖a‖ * coordinateChangeBase T ^ e.degree :=
      coefficientL1_changeCoordinates_monomial_le T v e a
    _ ≤ (2 : ℝ) ^ totalDegree degree *
        coordinateChangeBase T ^ totalDegree degree := by
      calc
        ‖a‖ * coordinateChangeBase T ^ e.degree ≤
            (2 : ℝ) ^ totalDegree degree * coordinateChangeBase T ^ e.degree :=
          mul_le_mul_of_nonneg_right
            (norm_chooseProduct_le_two_pow_totalDegree I M)
            (pow_nonneg (coordinateChangeBase_nonneg T) _)
        _ ≤ (2 : ℝ) ^ totalDegree degree *
            coordinateChangeBase T ^ totalDegree degree :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (one_le_coordinateChangeBase T)
              (residualFinsupp_degree_le I M)) (by positivity)
    _ = (2 * coordinateChangeBase T) ^ totalDegree degree := by
      rw [mul_pow]

/-- Sup-norm bound for the whole transformed divided-derivative matrix. -/
theorem norm_fullCoefficientMatrix_le {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ) :
    ‖GLRAuxiliary.fullCoefficientMatrix (degree := degree) T‖ ≤
      (2 * coordinateChangeBase T) ^ totalDegree degree := by
  have hnonneg : 0 ≤ (2 * coordinateChangeBase T) ^ totalDegree degree :=
    pow_nonneg (mul_nonneg (by norm_num) (coordinateChangeBase_nonneg T)) _
  rw [Matrix.norm_le_iff hnonneg]
  intro r M
  exact norm_basisTransformedCoefficient_le T r.1 r.2.1 r.2.2 M

/-- The support-vanishing matrix has the smaller undifferentiated bound. -/
theorem norm_supportVanishingMatrix_le {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (eta : ℚ)
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ) :
    ‖GLRAuxiliary.supportVanishingMatrix (degree := degree) eta T‖ ≤
      coordinateChangeBase T ^ totalDegree degree := by
  have hnonneg : 0 ≤ coordinateChangeBase T ^ totalDegree degree :=
    pow_nonneg (coordinateChangeBase_nonneg T) _
  rw [Matrix.norm_le_iff hnonneg]
  intro r M
  change ‖MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp r.1.2)
      (GLRAuxiliary.changeCoordinates T r.1.1
        (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp M) 1))‖ ≤ _
  calc
    ‖MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp r.1.2)
        (GLRAuxiliary.changeCoordinates T r.1.1
          (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp M) 1))‖ ≤
        coefficientL1
          (GLRAuxiliary.changeCoordinates T r.1.1
            (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp M) 1)) :=
      norm_coeff_le_coefficientL1 _ _
    _ ≤ ‖(1 : ℤ)‖ * coordinateChangeBase T ^
        (AuxiliaryPolynomial.toFinsupp M).degree :=
      coefficientL1_changeCoordinates_monomial_le T r.1.1
        (AuxiliaryPolynomial.toFinsupp M) 1
    _ = coordinateChangeBase T ^ totalDegree degree := by
      rw [norm_one, one_mul, toFinsupp_degree]

theorem succ_le_two_pow_of_pos {d : ℕ} (hd : 0 < d) :
    d + 1 ≤ 2 ^ d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  induction k with
  | zero => norm_num
  | succ k ih =>
      calc
        k.succ.succ + 1 ≤ 2 * (k.succ + 1) := by omega
        _ ≤ 2 * 2 ^ k.succ :=
          Nat.mul_le_mul_left 2 (ih (Nat.succ_pos _))
        _ = 2 ^ k.succ * 2 := Nat.mul_comm _ _
        _ = 2 ^ k.succ.succ := (pow_succ _ _).symm

/-- The number of multihomogeneous monomials is exponential in total
degree with a dimension-only base. -/
theorem card_monomialIndex_le_two_pow {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (hdegree : ∀ h, 0 < degree h) :
    Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree) ≤
      (2 ^ coords) ^ totalDegree degree := by
  calc
    Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree) ≤
        ∏ h, (degree h + 1) ^ coords :=
      AuxiliaryPolynomial.card_monomialIndex_le blocks coords degree
    _ ≤ ∏ h, (2 ^ degree h) ^ coords := by
      exact Finset.prod_le_prod (fun h _ ↦ by positivity)
        (fun h _ ↦ Nat.pow_le_pow_left (succ_le_two_pow_of_pos (hdegree h)) coords)
    _ = ∏ h, (2 ^ coords) ^ degree h := by
      apply Finset.prod_congr rfl
      intro h hh
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = (2 ^ coords) ^ totalDegree degree := by
      rw [Finset.prod_pow_eq_pow_sum]
      rfl

theorem card_monomialIndex_cast_le_two_pow {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (hdegree : ∀ h, 0 < degree h) :
    (Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree) : ℝ) ≤
      ((2 : ℝ) ^ coords) ^ totalDegree degree := by
  exact_mod_cast card_monomialIndex_le_two_pow hdegree

/-- With twice the usual row-count margin, the support equations occupy at
most half of the available coefficient coordinates. -/
theorem two_mul_card_vanishingRow_lt {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (eta : ℚ)
    (hblocks : 0 < blocks) (hcoords : 0 < coords)
    (hdegree : ∀ h, 0 < degree h) (heta : 0 < eta)
    (hmany : (6 : ℚ) * coords < blocks * eta ^ 2) :
    2 * Fintype.card (GLRAuxiliary.VanishingRow blocks coords degree eta) <
      Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree) := by
  classical
  let A : ℚ := Fintype.card (GLRAuxiliary.BadMonomial blocks coords degree eta)
  let N : ℚ := Fintype.card
    (AuxiliaryPolynomial.MonomialIndex blocks coords degree)
  letI : NeZero coords := ⟨hcoords.ne'⟩
  have hA : 0 ≤ A := by positivity
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos :
      0 < Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree))
  have hB : (0 : ℚ) < blocks := by exact_mod_cast hblocks
  have hQ : (0 : ℚ) < coords := by exact_mod_cast hcoords
  have hbadNat := GLRAuxiliary.card_badMonomial_le_sum_badAt
    (blocks := blocks) (coords := coords) (degree := degree) (eta := eta)
  have hbadCast : A ≤
      ∑ i : Fin coords,
        ((GLRAuxiliary.badAtFinset blocks coords degree eta i).card : ℚ) := by
    dsimp [A]
    rw [← Nat.cast_sum]
    exact_mod_cast hbadNat
  have hsum : A * ((blocks : ℚ) * eta) ^ 2 ≤
      (coords : ℚ) * N * blocks := by
    calc
      A * ((blocks : ℚ) * eta) ^ 2 ≤
          (∑ i : Fin coords,
            ((GLRAuxiliary.badAtFinset blocks coords degree eta i).card : ℚ)) *
              ((blocks : ℚ) * eta) ^ 2 :=
        mul_le_mul_of_nonneg_right hbadCast (sq_nonneg _)
      _ = ∑ i : Fin coords,
          ((GLRAuxiliary.badAtFinset blocks coords degree eta i).card : ℚ) *
            ((blocks : ℚ) * eta) ^ 2 := by rw [Finset.sum_mul]
      _ ≤ ∑ _i : Fin coords, N * blocks := by
        apply Finset.sum_le_sum
        intro i hi
        exact GLRAuxiliary.card_badAt_mul_sq_le eta heta.le hcoords hdegree i
      _ = (coords : ℚ) * N * blocks := by simp [mul_assoc]
  have hcancel : A * (blocks : ℚ) * eta ^ 2 ≤ (coords : ℚ) * N := by
    apply (mul_le_mul_iff_of_pos_right hB).mp
    calc
      (A * (blocks : ℚ) * eta ^ 2) * blocks =
          A * ((blocks : ℚ) * eta) ^ 2 := by ring
      _ ≤ (coords : ℚ) * N * blocks := hsum
  have hsix : (6 : ℚ) * A < N := by
    rcases hA.eq_or_lt with hAz | hApos
    · rw [← hAz]
      simpa using hN
    · have hmul := mul_lt_mul_of_pos_left hmany hApos
      have hchain : (6 : ℚ) * A * coords < (coords : ℚ) * N := by
        calc
          (6 : ℚ) * A * coords = A * ((6 : ℚ) * coords) := by ring
          _ < A * (blocks * eta ^ 2) := hmul
          _ = A * blocks * eta ^ 2 := by ring
          _ ≤ (coords : ℚ) * N := hcancel
      exact (mul_lt_mul_iff_of_pos_right hQ).mp (by
        simpa [mul_comm] using hchain)
  rw [GLRAuxiliary.card_vanishingRow]
  dsimp [A, N] at hsix
  have hsixNat :
      6 * Fintype.card (GLRAuxiliary.BadMonomial blocks coords degree eta) <
        Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree) := by
    exact_mod_cast hsix
  omega

/-- The fixed exponential base controlling the Siegel coefficient bound. -/
noncomputable def coefficientHeightBase {coords : ℕ}
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ) : ℝ :=
  (2 : ℝ) ^ coords * coordinateChangeBase T

theorem one_le_coefficientHeightBase {coords : ℕ}
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ) :
    1 ≤ coefficientHeightBase T := by
  calc
    (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (2 : ℝ) ^ coords * coordinateChangeBase T :=
      mul_le_mul (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
        (one_le_coordinateChangeBase T)
        (by positivity) (by positivity)
    _ = coefficientHeightBase T := rfl

/-- Under the doubled row-count margin, the Bombieri--Vaaler exponent is at
most one. -/
theorem coefficientHeightExponent_le_one {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (eta : ℚ)
    (hblocks : 0 < blocks) (hcoords : 0 < coords)
    (hdegree : ∀ h, 0 < degree h) (heta : 0 < eta)
    (hmany : (6 : ℚ) * coords < blocks * eta ^ 2) :
    (Fintype.card (GLRAuxiliary.VanishingRow blocks coords degree eta) : ℝ) /
        (Fintype.card
          (AuxiliaryPolynomial.MonomialIndex blocks coords degree) -
          Fintype.card
            (GLRAuxiliary.VanishingRow blocks coords degree eta)) ≤ 1 := by
  have hhalf := two_mul_card_vanishingRow_lt eta hblocks hcoords hdegree heta hmany
  have hhalfR :
      2 * (Fintype.card
        (GLRAuxiliary.VanishingRow blocks coords degree eta) : ℝ) <
        Fintype.card
          (AuxiliaryPolynomial.MonomialIndex blocks coords degree) := by
    exact_mod_cast hhalf
  apply (div_le_one (by linarith)).2
  linarith

/-- The explicit Siegel coefficient height is bounded by a fixed base to the
total multidegree. -/
theorem coefficientHeightBound_le_pow {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (eta : ℚ)
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (hblocks : 0 < blocks) (hcoords : 0 < coords)
    (hdegree : ∀ h, 0 < degree h) (heta : 0 < eta)
    (hmany : (6 : ℚ) * coords < blocks * eta ^ 2) :
    GLRAuxiliary.coefficientHeightBound (degree := degree) eta T ≤
      coefficientHeightBase T ^ totalDegree degree := by
  letI : NeZero coords := ⟨hcoords.ne'⟩
  let N : ℝ := Fintype.card
    (AuxiliaryPolynomial.MonomialIndex blocks coords degree)
  let S : ℝ := ‖GLRAuxiliary.supportVanishingMatrix
    (degree := degree) eta T‖
  have hN1 : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos :
      0 < Fintype.card
        (AuxiliaryPolynomial.MonomialIndex blocks coords degree))
  have hpowB : 1 ≤ coordinateChangeBase T ^ totalDegree degree :=
    one_le_pow₀ (one_le_coordinateChangeBase T)
  have hS : S ≤ coordinateChangeBase T ^ totalDegree degree := by
    dsimp [S]
    exact norm_supportVanishingMatrix_le eta T
  have hmaxS : max 1 S ≤ coordinateChangeBase T ^ totalDegree degree :=
    max_le hpowB hS
  have hN : N ≤ ((2 : ℝ) ^ coords) ^ totalDegree degree := by
    dsimp [N]
    exact card_monomialIndex_cast_le_two_pow hdegree
  have hbase : N * max 1 S ≤ coefficientHeightBase T ^ totalDegree degree := by
    calc
      N * max 1 S ≤ ((2 : ℝ) ^ coords) ^ totalDegree degree *
          coordinateChangeBase T ^ totalDegree degree :=
        mul_le_mul hN hmaxS (by positivity) (by positivity)
      _ = coefficientHeightBase T ^ totalDegree degree := by
        change ((2 : ℝ) ^ coords) ^ totalDegree degree *
            coordinateChangeBase T ^ totalDegree degree =
          ((2 : ℝ) ^ coords * coordinateChangeBase T) ^ totalDegree degree
        exact (mul_pow _ _ _).symm
  have hinside : 1 ≤ N * max 1 S := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ N * max 1 S :=
        mul_le_mul hN1 (le_max_left _ _) (by positivity) (by positivity)
  change (N * max 1 S) ^
      ((Fintype.card
        (GLRAuxiliary.VanishingRow blocks coords degree eta) : ℝ) /
        (Fintype.card
          (AuxiliaryPolynomial.MonomialIndex blocks coords degree) -
          Fintype.card
            (GLRAuxiliary.VanishingRow blocks coords degree eta))) ≤ _
  exact (Real.rpow_le_self_of_one_le hinside
    (coefficientHeightExponent_le_one eta hblocks hcoords hdegree heta hmany)).trans hbase

/-- A fixed exponential base controlling the monomial count, all transformed
coefficient rows, and the Siegel coefficient bound simultaneously. -/
noncomputable def transformedCoefficientHeightBase {coords : ℕ}
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ) : ℝ :=
  (2 : ℝ) ^ coords * (2 * coordinateChangeBase T) * coefficientHeightBase T

theorem one_le_transformedCoefficientHeightBase {coords : ℕ}
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ) :
    1 ≤ transformedCoefficientHeightBase T := by
  have hA : 1 ≤ (2 : ℝ) ^ coords := one_le_pow₀ (by norm_num)
  have hB : 1 ≤ 2 * coordinateChangeBase T := by
    nlinarith [one_le_coordinateChangeBase T]
  have hC := one_le_coefficientHeightBase T
  dsimp [transformedCoefficientHeightBase]
  nlinarith [mul_le_mul hA hB (by positivity) (by positivity),
    mul_le_mul (mul_le_mul hA hB (by positivity) (by positivity)) hC
      (by positivity) (by positivity)]

/-- The complete transformed-coefficient prefactor has fixed exponential
growth in the total multidegree. -/
theorem transformedCoefficientPrefactor_le_pow {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (eta : ℚ)
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (hblocks : 0 < blocks) (hcoords : 0 < coords)
    (hdegree : ∀ h, 0 < degree h) (heta : 0 < eta)
    (hmany : (6 : ℚ) * coords < blocks * eta ^ 2) :
    (Fintype.card
        (AuxiliaryPolynomial.MonomialIndex blocks coords degree) : ℝ) *
        ‖GLRAuxiliary.fullCoefficientMatrix (degree := degree) T‖ *
        GLRAuxiliary.coefficientHeightBound (degree := degree) eta T ≤
      transformedCoefficientHeightBase T ^ totalDegree degree := by
  have hN := card_monomialIndex_cast_le_two_pow
    (blocks := blocks) (coords := coords) (degree := degree) hdegree
  have hM := norm_fullCoefficientMatrix_le
    (blocks := blocks) (coords := coords) (degree := degree) T
  have hC := coefficientHeightBound_le_pow
    (blocks := blocks) (coords := coords) (degree := degree)
    eta T hblocks hcoords hdegree heta hmany
  have hCnonneg :
      0 ≤ GLRAuxiliary.coefficientHeightBound (degree := degree) eta T := by
    unfold GLRAuxiliary.coefficientHeightBound
    exact Real.rpow_nonneg (by positivity) _
  have hNM :
      (Fintype.card
          (AuxiliaryPolynomial.MonomialIndex blocks coords degree) : ℝ) *
          ‖GLRAuxiliary.fullCoefficientMatrix (degree := degree) T‖ ≤
        (((2 : ℝ) ^ coords) * (2 * coordinateChangeBase T)) ^
          totalDegree degree := by
    calc
      (Fintype.card
          (AuxiliaryPolynomial.MonomialIndex blocks coords degree) : ℝ) *
          ‖GLRAuxiliary.fullCoefficientMatrix (degree := degree) T‖ ≤
          ((2 : ℝ) ^ coords) ^ totalDegree degree *
            (2 * coordinateChangeBase T) ^ totalDegree degree :=
        mul_le_mul hN hM (norm_nonneg _) (by positivity)
      _ = (((2 : ℝ) ^ coords) * (2 * coordinateChangeBase T)) ^
          totalDegree degree := (mul_pow _ _ _).symm
  calc
    (Fintype.card
        (AuxiliaryPolynomial.MonomialIndex blocks coords degree) : ℝ) *
        ‖GLRAuxiliary.fullCoefficientMatrix (degree := degree) T‖ *
        GLRAuxiliary.coefficientHeightBound (degree := degree) eta T ≤
        ((((2 : ℝ) ^ coords) * (2 * coordinateChangeBase T)) ^
          totalDegree degree) *
          coefficientHeightBase T ^ totalDegree degree :=
      mul_le_mul hNM hC hCnonneg
        (pow_nonneg (mul_nonneg (by positivity)
          (by nlinarith [one_le_coordinateChangeBase T])) _)
    _ = transformedCoefficientHeightBase T ^ totalDegree degree := by
      change ((((2 : ℝ) ^ coords) * (2 * coordinateChangeBase T)) ^
          totalDegree degree) * coefficientHeightBase T ^ totalDegree degree =
        (((2 : ℝ) ^ coords) * (2 * coordinateChangeBase T) *
          coefficientHeightBase T) ^ totalDegree degree
      exact (mul_pow _ _ _).symm

theorem totalDegree_cast_eq_sum {blocks : ℕ} (degree : Fin blocks → ℕ) :
    (totalDegree degree : ℝ) = ∑ h, (degree h : ℝ) := by
  simp [totalDegree]

/-- Logarithmic form of the Siegel coefficient-height estimate. -/
theorem log_max_coefficientHeightBound_le {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (eta : ℚ)
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (hblocks : 0 < blocks) (hcoords : 0 < coords)
    (hdegree : ∀ h, 0 < degree h) (heta : 0 < eta)
    (hmany : (6 : ℚ) * coords < blocks * eta ^ 2) :
    Real.log (max 1
      (GLRAuxiliary.coefficientHeightBound (degree := degree) eta T)) ≤
      Real.log (coefficientHeightBase T) * ∑ h, (degree h : ℝ) := by
  have hK := one_le_coefficientHeightBase T
  have hpow : 1 ≤ coefficientHeightBase T ^ totalDegree degree :=
    one_le_pow₀ hK
  have hbound := coefficientHeightBound_le_pow eta T hblocks hcoords hdegree heta hmany
  calc
    Real.log (max 1
        (GLRAuxiliary.coefficientHeightBound (degree := degree) eta T)) ≤
        Real.log (coefficientHeightBase T ^ totalDegree degree) :=
      Real.log_le_log (by positivity) (max_le hpow hbound)
    _ = Real.log (coefficientHeightBase T) * ∑ h, (degree h : ℝ) := by
      rw [Real.log_pow, ← totalDegree_cast_eq_sum]
      ring

/-- Logarithmic form of the full transformed-coefficient prefactor estimate. -/
theorem log_max_transformedCoefficientPrefactor_le {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (eta : ℚ)
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (hblocks : 0 < blocks) (hcoords : 0 < coords)
    (hdegree : ∀ h, 0 < degree h) (heta : 0 < eta)
    (hmany : (6 : ℚ) * coords < blocks * eta ^ 2) :
    Real.log (max 1
      ((Fintype.card
          (AuxiliaryPolynomial.MonomialIndex blocks coords degree) : ℝ) *
        ‖GLRAuxiliary.fullCoefficientMatrix (degree := degree) T‖ *
        GLRAuxiliary.coefficientHeightBound (degree := degree) eta T)) ≤
      Real.log (transformedCoefficientHeightBase T) *
        ∑ h, (degree h : ℝ) := by
  have hK := one_le_transformedCoefficientHeightBase T
  have hpow : 1 ≤ transformedCoefficientHeightBase T ^ totalDegree degree :=
    one_le_pow₀ hK
  have hbound := transformedCoefficientPrefactor_le_pow eta T hblocks hcoords
    hdegree heta hmany
  calc
    Real.log (max 1
      ((Fintype.card
          (AuxiliaryPolynomial.MonomialIndex blocks coords degree) : ℝ) *
        ‖GLRAuxiliary.fullCoefficientMatrix (degree := degree) T‖ *
        GLRAuxiliary.coefficientHeightBound (degree := degree) eta T)) ≤
        Real.log (transformedCoefficientHeightBase T ^ totalDegree degree) :=
      Real.log_le_log (by positivity) (max_le hpow hbound)
    _ = Real.log (transformedCoefficientHeightBase T) *
        ∑ h, (degree h : ℝ) := by
      rw [Real.log_pow, ← totalDegree_cast_eq_sum]
      ring

/-- Existential-constant packaging used by the GLR rank-drop argument. -/
theorem exists_coefficientHeight_logSlope {blocks coords : ℕ}
    (eta : ℚ)
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (hblocks : 0 < blocks) (hcoords : 0 < coords) (heta : 0 < eta)
    (hmany : (6 : ℚ) * coords < blocks * eta ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ degree : Fin blocks → ℕ,
      (∀ h, 0 < degree h) →
      Real.log (max 1
        (GLRAuxiliary.coefficientHeightBound (degree := degree) eta T)) ≤
        C * ∑ h, (degree h : ℝ) := by
  refine ⟨Real.log (coefficientHeightBase T),
    Real.log_nonneg (one_le_coefficientHeightBase T), ?_⟩
  intro degree hdegree
  exact log_max_coefficientHeightBound_le eta T hblocks hcoords hdegree heta hmany

/-- Existential-constant packaging for every factor occurring in transformed
coefficient evaluation. -/
theorem exists_transformedCoefficientPrefactor_logSlope {blocks coords : ℕ}
    (eta : ℚ)
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (hblocks : 0 < blocks) (hcoords : 0 < coords) (heta : 0 < eta)
    (hmany : (6 : ℚ) * coords < blocks * eta ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ degree : Fin blocks → ℕ,
      (∀ h, 0 < degree h) →
      Real.log (max 1
        ((Fintype.card
            (AuxiliaryPolynomial.MonomialIndex blocks coords degree) : ℝ) *
          ‖GLRAuxiliary.fullCoefficientMatrix (degree := degree) T‖ *
          GLRAuxiliary.coefficientHeightBound (degree := degree) eta T)) ≤
        C * ∑ h, (degree h : ℝ) := by
  refine ⟨Real.log (transformedCoefficientHeightBase T),
    Real.log_nonneg (one_le_transformedCoefficientHeightBase T), ?_⟩
  intro degree hdegree
  exact log_max_transformedCoefficientPrefactor_le eta T hblocks hcoords hdegree heta hmany

theorem totalDegree_pos {blocks : ℕ} {degree : Fin blocks → ℕ}
    (hblocks : 0 < blocks) (hdegree : ∀ h, 0 < degree h) :
    0 < totalDegree degree := by
  let i : Fin blocks := ⟨0, hblocks⟩
  unfold totalDegree
  exact Finset.sum_pos' (fun _ _ ↦ Nat.zero_le _) ⟨i, Finset.mem_univ _, hdegree i⟩

/-- Rounding a nonnegative exponentially bounded real number up to a natural
number costs only a factor `2` in the fixed exponential base. -/
theorem log_max_natCeil_le_mul_log_of_le_pow
    {x K : ℝ} {D : ℕ} (hx : 0 ≤ x) (hK : 1 ≤ K) (hD : 0 < D)
    (hbound : x ≤ K ^ D) :
    Real.log (max 1 ⌈x⌉₊) ≤ Real.log (2 * K) * D := by
  have hKD : 1 ≤ K ^ D := one_le_pow₀ hK
  have hceil : (⌈x⌉₊ : ℝ) ≤ 2 * K ^ D := by
    calc
      (⌈x⌉₊ : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx).le
      _ ≤ K ^ D + 1 := by linarith
      _ ≤ K ^ D + K ^ D := by linarith
      _ = 2 * K ^ D := by ring
  have htwo : (2 : ℝ) ≤ 2 ^ D := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hD.ne'
    rw [pow_succ]
    nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := d)]
  have hceilPow : (⌈x⌉₊ : ℝ) ≤ (2 * K) ^ D := by
    calc
      (⌈x⌉₊ : ℝ) ≤ 2 * K ^ D := hceil
      _ ≤ 2 ^ D * K ^ D :=
        mul_le_mul_of_nonneg_right htwo (pow_nonneg (by linarith) _)
      _ = (2 * K) ^ D := (mul_pow _ _ _).symm
  have honePow : (1 : ℝ) ≤ (2 * K) ^ D :=
    one_le_pow₀ (by nlinarith)
  have hmaxReal :
      max (1 : ℝ) (⌈x⌉₊ : ℝ) ≤ (2 * K) ^ D := max_le honePow hceilPow
  calc
    Real.log (max 1 ⌈x⌉₊) ≤ Real.log ((2 * K) ^ D) := by
      apply Real.log_le_log
      · exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
          (le_max_left 1 ⌈x⌉₊))
      · simpa only [Nat.cast_max, Nat.cast_one] using hmaxReal
    _ = Real.log (2 * K) * D := by
      rw [Real.log_pow]
      ring

/-- The ceiling form required by the projective coefficient-height estimate. -/
theorem log_max_ceil_coefficientHeightBound_le {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (eta : ℚ)
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (hblocks : 0 < blocks) (hcoords : 0 < coords)
    (hdegree : ∀ h, 0 < degree h) (heta : 0 < eta)
    (hmany : (6 : ℚ) * coords < blocks * eta ^ 2) :
    Real.log (max 1
      ⌈GLRAuxiliary.coefficientHeightBound (degree := degree) eta T⌉₊) ≤
      Real.log (2 * coefficientHeightBase T) *
        ∑ h, (degree h : ℝ) := by
  have hnonneg :
      0 ≤ GLRAuxiliary.coefficientHeightBound (degree := degree) eta T := by
    unfold GLRAuxiliary.coefficientHeightBound
    exact Real.rpow_nonneg (by positivity) _
  have h := log_max_natCeil_le_mul_log_of_le_pow hnonneg
    (one_le_coefficientHeightBase T) (totalDegree_pos hblocks hdegree)
    (coefficientHeightBound_le_pow eta T hblocks hcoords hdegree heta hmany)
  rw [← totalDegree_cast_eq_sum]
  simpa using h

/-- Existential-constant packaging of the rounded coefficient-height bound. -/
theorem exists_ceilCoefficientHeight_logSlope {blocks coords : ℕ}
    (eta : ℚ)
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (hblocks : 0 < blocks) (hcoords : 0 < coords) (heta : 0 < eta)
    (hmany : (6 : ℚ) * coords < blocks * eta ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ degree : Fin blocks → ℕ,
      (∀ h, 0 < degree h) →
      Real.log (max 1
        ⌈GLRAuxiliary.coefficientHeightBound (degree := degree) eta T⌉₊) ≤
        C * ∑ h, (degree h : ℝ) := by
  refine ⟨Real.log (2 * coefficientHeightBase T),
    Real.log_nonneg (by nlinarith [one_le_coefficientHeightBase T]), ?_⟩
  intro degree hdegree
  exact log_max_ceil_coefficientHeightBound_le eta T hblocks hcoords
    hdegree heta hmany

/-- Rounded logarithmic estimate for the complete transformed-coefficient
prefactor.  This is convenient when an integral coefficient is passed to a
natural-valued projective-height bound. -/
theorem log_max_ceil_transformedCoefficientPrefactor_le {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (eta : ℚ)
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (hblocks : 0 < blocks) (hcoords : 0 < coords)
    (hdegree : ∀ h, 0 < degree h) (heta : 0 < eta)
    (hmany : (6 : ℚ) * coords < blocks * eta ^ 2) :
    Real.log (max 1
      ⌈(Fintype.card
          (AuxiliaryPolynomial.MonomialIndex blocks coords degree) : ℝ) *
        ‖GLRAuxiliary.fullCoefficientMatrix (degree := degree) T‖ *
        GLRAuxiliary.coefficientHeightBound (degree := degree) eta T⌉₊) ≤
      Real.log (2 * transformedCoefficientHeightBase T) *
        ∑ h, (degree h : ℝ) := by
  let X : ℝ :=
    (Fintype.card
        (AuxiliaryPolynomial.MonomialIndex blocks coords degree) : ℝ) *
      ‖GLRAuxiliary.fullCoefficientMatrix (degree := degree) T‖ *
      GLRAuxiliary.coefficientHeightBound (degree := degree) eta T
  have hcoeffNonneg :
      0 ≤ GLRAuxiliary.coefficientHeightBound (degree := degree) eta T := by
    unfold GLRAuxiliary.coefficientHeightBound
    exact Real.rpow_nonneg (by positivity) _
  have hX : 0 ≤ X := by
    dsimp [X]
    positivity
  have h := log_max_natCeil_le_mul_log_of_le_pow hX
    (one_le_transformedCoefficientHeightBase T) (totalDegree_pos hblocks hdegree)
    (transformedCoefficientPrefactor_le_pow eta T hblocks hcoords
      hdegree heta hmany)
  rw [← totalDegree_cast_eq_sum]
  simpa [X] using h

theorem exists_ceilTransformedCoefficientPrefactor_logSlope
    {blocks coords : ℕ} (eta : ℚ)
    (T : GLRAuxiliary.Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (hblocks : 0 < blocks) (hcoords : 0 < coords) (heta : 0 < eta)
    (hmany : (6 : ℚ) * coords < blocks * eta ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ degree : Fin blocks → ℕ,
      (∀ h, 0 < degree h) →
      Real.log (max 1
        ⌈(Fintype.card
            (AuxiliaryPolynomial.MonomialIndex blocks coords degree) : ℝ) *
          ‖GLRAuxiliary.fullCoefficientMatrix (degree := degree) T‖ *
          GLRAuxiliary.coefficientHeightBound (degree := degree) eta T⌉₊) ≤
        C * ∑ h, (degree h : ℝ) := by
  refine ⟨Real.log (2 * transformedCoefficientHeightBase T),
    Real.log_nonneg (by
      nlinarith [one_le_transformedCoefficientHeightBase T]), ?_⟩
  intro degree hdegree
  exact log_max_ceil_transformedCoefficientPrefactor_le eta T hblocks hcoords
    hdegree heta hmany

end


end Erdos407.AuxiliaryHeightEstimates
