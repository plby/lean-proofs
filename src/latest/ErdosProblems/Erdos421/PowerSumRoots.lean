import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic

/-! # Recovering a tuple's root polynomial from its power sums -/

namespace Erdos421

open Polynomial

section CommRing

variable {R : Type*} [CommRing R] {n : ℕ}

noncomputable def tupleEsymm (x : Fin n → R) (k : ℕ) : R :=
  (Finset.univ.val.map x).esymm k

theorem tupleEsymm_zero (x : Fin n → R) : tupleEsymm x 0 = 1 := by
  simp [tupleEsymm, Multiset.esymm]

theorem tupleEsymm_newton (x : Fin n → R) (k : ℕ) :
    (k : R) * tupleEsymm x k = (-1 : R) ^ (k + 1) *
      ∑ a ∈ (Finset.antidiagonal k).filter (fun a ↦ a.1 < k),
        (-1 : R) ^ a.1 * tupleEsymm x a.1 * ∑ i : Fin n, x i ^ a.2 := by
  have h := congrArg (MvPolynomial.aeval x) (MvPolynomial.mul_esymm_eq_sum (Fin n) R k)
  simpa only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_X,
    tupleEsymm] using h

/-- Units among the small integers are enough; a characteristic-zero field
is not required. This form also applies to residue rings of prime powers. -/
theorem tupleEsymm_eq_of_power_sums (x y : Fin n → R)
    (hunit : ∀ k : ℕ, 0 < k → k ≤ n → IsUnit (k : R))
    (hp : ∀ k : ℕ, 0 < k → k ≤ n → (∑ i : Fin n, x i ^ k) = ∑ i : Fin n, y i ^ k) :
    ∀ k : ℕ, k ≤ n → tupleEsymm x k = tupleEsymm y k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hkn
    by_cases hk : k = 0
    · subst k
      rw [tupleEsymm_zero, tupleEsymm_zero]
    have hkp : 0 < k := Nat.pos_of_ne_zero hk
    apply (hunit k hkp hkn).mul_left_cancel
    rw [tupleEsymm_newton, tupleEsymm_newton]
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    obtain ⟨haeq, halt⟩ := Finset.mem_filter.mp ha
    have hasum := Finset.mem_antidiagonal.mp haeq
    have ha2 : 0 < a.2 := by omega
    have ha2n : a.2 ≤ n := by omega
    rw [ih a.1 halt (by omega), hp a.2 ha2 ha2n]

theorem tuple_rootPolynomial_eq_of_esymm (x y : Fin n → R)
    (he : ∀ k : ℕ, k ≤ n → tupleEsymm x k = tupleEsymm y k) :
    (∏ i : Fin n, (X - C (x i))) = ∏ i : Fin n, (X - C (y i)) := by
  classical
  have hx := Multiset.prod_X_sub_X_eq_sum_esymm (Finset.univ.val.map x)
  have hy := Multiset.prod_X_sub_X_eq_sum_esymm (Finset.univ.val.map y)
  simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin,
    Multiset.map_map, Function.comp_def] at hx hy
  change (Finset.univ.val.map (fun i ↦ X - C (x i))).prod =
    (Finset.univ.val.map (fun i ↦ X - C (y i))).prod
  rw [hx, hy]
  apply Finset.sum_congr rfl
  intro k hk
  change (-1 : R[X]) ^ k * (C (tupleEsymm x k) * X ^ (n - k)) =
    (-1 : R[X]) ^ k * (C (tupleEsymm y k) * X ^ (n - k))
  rw [he k (by simpa using Finset.mem_range.mp hk)]

theorem tuple_rootPolynomial_eq_of_power_sums (x y : Fin n → R)
    (hunit : ∀ k : ℕ, 0 < k → k ≤ n → IsUnit (k : R))
    (hp : ∀ k : ℕ, 0 < k → k ≤ n → (∑ i : Fin n, x i ^ k) = ∑ i : Fin n, y i ^ k) :
    (∏ i : Fin n, (X - C (x i))) = ∏ i : Fin n, (X - C (y i)) :=
  tuple_rootPolynomial_eq_of_esymm x y (tupleEsymm_eq_of_power_sums x y hunit hp)

end CommRing

end Erdos421
