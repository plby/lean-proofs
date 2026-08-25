import ErdosProblems.Erdos1141.StepanovBox
import ErdosProblems.Erdos1141.StepanovDerivative
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The linear conditions in the quadratic Stepanov argument

The coefficient box has dimension `2*A*B`.  Vanishing of the reduced
derivatives imposes fewer linear conditions when the displayed parameter
inequality holds, so a nonzero coefficient family exists.
-/

namespace Pollack17.Stepanov

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] {p A B D : ℕ}

abbrev BoxPair (K : Type*) (A B : ℕ) :=
  (Fin A × Fin B → K) × (Fin A × Fin B → K)

noncomputable def conditionHalf (f : K[X]) (t : K) (k : ℕ)
    (a : Fin A × Fin B → K) : K[X] :=
  ∑ i : Fin A × Fin B,
    a i • (reducedDerivative f t (X ^ (i.1 : ℕ)) k * X ^ (i.2 : ℕ))

noncomputable def conditionPolynomial (f : K[X]) (t : K) (k : ℕ)
    (a : BoxPair K A B) : K[X] := conditionHalf f 0 k a.1 + conditionHalf f t k a.2

theorem conditionHalf_natDegree_le (f : K[X]) (t : K) (k : ℕ)
    (a : Fin A × Fin B → K) :
    (conditionHalf f t k a).natDegree ≤ A + B + k * f.natDegree := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  apply (Polynomial.natDegree_smul_le _ _).trans
  have hred := reducedDerivative_natDegree_le f (X ^ (i.1 : ℕ)) t k
  have hmul := Polynomial.natDegree_mul_le
    (p := reducedDerivative f t (X ^ (i.1 : ℕ)) k) (q := X ^ (i.2 : ℕ))
  simp only [natDegree_X_pow] at hred hmul
  have ha := i.1.isLt
  have hb := i.2.isLt
  omega

theorem conditionPolynomial_natDegree_le (f : K[X]) (t : K) (k : ℕ)
    (a : BoxPair K A B) :
    (conditionPolynomial f t k a).natDegree ≤ A + B + k * f.natDegree := by
  exact (Polynomial.natDegree_add_le _ _).trans
    (max_le (conditionHalf_natDegree_le f 0 k a.1) (conditionHalf_natDegree_le f t k a.2))

theorem conditionPolynomial_add (f : K[X]) (t : K) (k : ℕ)
    (a b : BoxPair K A B) :
    conditionPolynomial f t k (a + b) =
      conditionPolynomial f t k a + conditionPolynomial f t k b := by
  simp [conditionPolynomial, conditionHalf, add_smul, Finset.sum_add_distrib,
    add_add_add_comm]

theorem conditionPolynomial_smul (f : K[X]) (t : K) (k : ℕ)
    (c : K) (a : BoxPair K A B) :
    conditionPolynomial f t k (c • a) = c • conditionPolynomial f t k a := by
  simp [conditionPolynomial, conditionHalf, Finset.smul_sum, smul_add, smul_smul]

noncomputable def conditionLinear (f : K[X]) (t : K) (A B D H : ℕ) :
    BoxPair K A B →ₗ[K] (Fin D → Fin H → K) where
  toFun a k j := (conditionPolynomial f t k a).coeff j
  map_add' a b := by
    funext k j
    rw [conditionPolynomial_add, coeff_add]
    rfl
  map_smul' c a := by
    funext k j
    rw [conditionPolynomial_smul, coeff_smul]
    rfl

theorem exists_nonzero_condition_kernel (f : K[X]) (t : K) (A B D H : ℕ)
    (hdim : D * H < 2 * A * B) :
    ∃ a : BoxPair K A B, a ≠ 0 ∧ conditionLinear f t A B D H a = 0 := by
  let T := conditionLinear f t A B D H
  have hker : LinearMap.ker T ≠ ⊥ := by
    intro hbot
    have hle := T.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hbot)
    have hsource : Module.finrank K (BoxPair K A B) = 2 * A * B := by
      simp [BoxPair, Module.finrank_prod]
      ring
    have htarget : Module.finrank K (Fin D → Fin H → K) = D * H := by
      simp [Module.finrank_pi_fintype]
    rw [hsource, htarget] at hle
    exact (not_le_of_gt hdim) hle
  obtain ⟨a, ha, hane⟩ := (LinearMap.ker T).ne_bot_iff.mp hker
  exact ⟨a, hane, ha⟩

theorem exists_nonzero_vanishing_conditions (f : K[X]) (t : K) (A B D : ℕ)
    (hdim : D * (A + B + D * f.natDegree + 1) < 2 * A * B) :
    ∃ a : BoxPair K A B, a ≠ 0 ∧
      ∀ k : ℕ, k < D → conditionPolynomial f t k a = 0 := by
  let H := A + B + D * f.natDegree + 1
  obtain ⟨a, ha, hkernel⟩ := exists_nonzero_condition_kernel f t A B D H hdim
  refine ⟨a, ha, ?_⟩
  intro k hk
  have hdegree : (conditionPolynomial f t k a).natDegree < H := by
    have hdeg := conditionPolynomial_natDegree_le f t k a
    have hmul := Nat.mul_le_mul_right f.natDegree hk.le
    omega
  ext n
  rw [coeff_zero]
  by_cases hn : n < H
  · exact congrFun (congrFun hkernel ⟨k, hk⟩) ⟨n, hn⟩
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdegree.trans_le (Nat.le_of_not_gt hn))

theorem pow_mul_boxPolynomial_eq_sum (f : K[X]) (t : ℕ)
    (a : Fin A × Fin B → K) :
    f ^ t * boxPolynomial (p := p) a =
      ∑ i : Fin A × Fin B, a i • ((f ^ t * X ^ (i.1 : ℕ)) * X ^ (p * i.2)) := by
  classical
  rw [boxPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← C_mul_X_pow_eq_monomial, boxExponent, pow_add, smul_eq_C_mul]
  ring

theorem eval_conditionHalf {p : ℕ} [CharP K p]
    (f : K[X]) (t k : ℕ) (a : Fin A × Fin B → K) (x : K) (hx : x ^ p = x) :
    f.eval x ^ k * (derivative^[k] (f ^ t * boxPolynomial (p := p) a)).eval x =
      f.eval x ^ t * (conditionHalf f (t : K) k a).eval x := by
  classical
  rw [pow_mul_boxPolynomial_eq_sum, Polynomial.iterate_derivative_sum]
  simp only [Polynomial.iterate_derivative_smul, eval_finsetSum, eval_smul,
    conditionHalf, eval_mul, eval_pow, eval_X]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := eval_pow_mul_iterate_derivative_frobenius f (X ^ (i.1 : ℕ)) t k i.2 x hx
  change f.eval x ^ k * (a i * _) = f.eval x ^ t * (a i * (_ * _))
  linear_combination a i * h

theorem eval_conditionPolynomial {p : ℕ} [CharP K p]
    (f : K[X]) (t k : ℕ) (a : BoxPair K A B) (x : K)
    (hx : x ^ p = x) (hft : f.eval x ^ t = 1) :
    f.eval x ^ k *
        (derivative^[k] (boxPolynomial (p := p) a.1 + f ^ t * boxPolynomial (p := p) a.2)).eval x =
      (conditionPolynomial f (t : K) k a).eval x := by
  have h0 := eval_conditionHalf f 0 k a.1 x hx
  have ht := eval_conditionHalf f t k a.2 x hx
  simp only [pow_zero, one_mul, Nat.cast_zero] at h0
  rw [hft, one_mul] at ht
  have hsum : derivative^[k]
      (boxPolynomial (p := p) a.1 + f ^ t * boxPolynomial (p := p) a.2) =
      derivative^[k] (boxPolynomial (p := p) a.1) +
        derivative^[k] (f ^ t * boxPolynomial (p := p) a.2) :=
    iterate_map_add Polynomial.derivative k _ _
  rw [hsum, eval_add, mul_add, h0, ht, conditionPolynomial, eval_add]

end Pollack17.Stepanov
