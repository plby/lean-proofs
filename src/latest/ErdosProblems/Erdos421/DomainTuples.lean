import ErdosProblems.Erdos421.PowerSumRoots
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Perm

/-! # Power sums over a characteristic-zero field, with repeated entries -/

namespace Erdos421

open Polynomial

theorem tuple_perm_of_multiset_eq {R : Type*} {n : ℕ} (x y : Fin n → R)
    (hm : Finset.univ.val.map x = Finset.univ.val.map y) :
    ∃ e : Equiv.Perm (Fin n), ∀ i : Fin n, x i = y (e i) := by
  classical
  have hc : ∀ a : R, Fintype.card {i : Fin n // x i = a} =
      Fintype.card {i : Fin n // y i = a} := by
    intro a
    have h := congrArg (Multiset.count a) hm
    simpa only [Multiset.count_map, Fintype.card_subtype, Finset.card_def,
      Finset.filter_val, eq_comm] using h
  let e (a : R) : {i : Fin n // x i = a} ≃ {i : Fin n // y i = a} :=
    Fintype.equivOfCardEq (hc a)
  exact ⟨Equiv.ofFiberEquiv e, fun i ↦ (Equiv.ofFiberEquiv_map e i).symm⟩

theorem domain_tuple_perm_of_rootPolynomial_eq {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} (x y : Fin n → R)
    (hpoly : (∏ i : Fin n, (X - C (x i))) = ∏ i : Fin n, (X - C (y i))) :
    ∃ e : Equiv.Perm (Fin n), ∀ i : Fin n, x i = y (e i) := by
  apply tuple_perm_of_multiset_eq x y
  have hx := Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map x)
  have hy := Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map y)
  simp only [Multiset.map_map, Function.comp_def] at hx hy
  rw [← hx, ← hy]
  exact congrArg Polynomial.roots hpoly

theorem domain_tuple_perm_of_power_sums {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} (x y : Fin n → R)
    (hunit : ∀ k : ℕ, 0 < k → k ≤ n → IsUnit (k : R))
    (hs : ∀ k : ℕ, 0 < k → k ≤ n → (∑ i : Fin n, x i ^ k) = ∑ i : Fin n, y i ^ k) :
    ∃ e : Equiv.Perm (Fin n), ∀ i : Fin n, x i = y (e i) :=
  domain_tuple_perm_of_rootPolynomial_eq x y
    (tuple_rootPolynomial_eq_of_power_sums x y hunit hs)

theorem field_tuple_perm_of_power_sums {F : Type*} [Field F] [CharZero F]
    {n : ℕ} (x y : Fin n → F)
    (hs : ∀ k : ℕ, 0 < k → k ≤ n → (∑ i : Fin n, x i ^ k) = ∑ i : Fin n, y i ^ k) :
    ∃ e : Equiv.Perm (Fin n), ∀ i : Fin n, x i = y (e i) := by
  apply domain_tuple_perm_of_power_sums x y _ hs
  intro k hk _
  exact isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hk.ne')

end Erdos421
