import ErdosProblems.Erdos421.PowerSumRoots

/-! # Uniqueness up to permutation for tuples with distinct residue roots -/

namespace Erdos421

open Polynomial

section CommRing

variable {R F : Type*} [CommRing R] [CommRing F] [IsDomain F] {n : ℕ}

theorem tuple_root_product_eq_zero (x y : Fin n → R)
    (hpoly : (∏ i : Fin n, (X - C (x i))) = ∏ i : Fin n, (X - C (y i)))
    (i : Fin n) : (∏ j : Fin n, (x i - y j)) = 0 := by
  classical
  have h := congrArg (Polynomial.eval (x i)) hpoly
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
  have hx : (∏ j : Fin n, (x i - x j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  exact h.symm.trans hx

theorem tuple_root_matches_of_distinct_residues (φ : R →+* F)
    (hunit : ∀ a : R, φ a ≠ 0 → IsUnit a) (x y : Fin n → R)
    (hy : Function.Injective (fun i ↦ φ (y i)))
    (hpoly : (∏ i : Fin n, (X - C (x i))) = ∏ i : Fin n, (X - C (y i)))
    (i : Fin n) : ∃ j : Fin n, x i = y j := by
  classical
  have hprod := tuple_root_product_eq_zero x y hpoly i
  have hred : (∏ j : Fin n, (φ (x i) - φ (y j))) = 0 := by
    simpa only [map_prod, map_sub, map_zero] using congrArg φ hprod
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hred
  have hij : φ (x i) = φ (y j) := sub_eq_zero.mp hj
  have hrest : IsUnit (∏ k ∈ Finset.univ.erase j, (x i - y k)) := by
    apply IsUnit.prod_iff.mpr
    intro k hk
    apply hunit
    rw [map_sub]
    apply sub_ne_zero.mpr
    intro he
    have hjk : j = k := hy (hij.symm.trans he)
    exact (Finset.mem_erase.mp hk).1 hjk.symm
  rw [← Finset.mul_prod_erase Finset.univ (fun j ↦ x i - y j) (Finset.mem_univ j)] at hprod
  have hc : x i - y j = 0 := hrest.mul_right_cancel (by simpa only [zero_mul] using hprod)
  exact ⟨j, sub_eq_zero.mp hc⟩

theorem tuple_perm_of_rootPolynomial_eq (φ : R →+* F)
    (hunit : ∀ a : R, φ a ≠ 0 → IsUnit a) (x y : Fin n → R)
    (hy : Function.Injective (fun i ↦ φ (y i)))
    (hpoly : (∏ i : Fin n, (X - C (x i))) = ∏ i : Fin n, (X - C (y i))) :
    ∃ e : Equiv.Perm (Fin n), ∀ i : Fin n, x i = y (e i) := by
  classical
  choose e he using tuple_root_matches_of_distinct_residues φ hunit x y hy hpoly
  have hs : Function.Surjective e := by
    intro j
    have hprod := tuple_root_product_eq_zero y x hpoly.symm j
    have hred : (∏ i : Fin n, (φ (y j) - φ (x i))) = 0 := by
      simpa only [map_prod, map_sub, map_zero] using congrArg φ hprod
    obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hred
    have hji : φ (y j) = φ (x i) := sub_eq_zero.mp hi
    rw [he i] at hji
    exact ⟨i, (hy hji).symm⟩
  exact ⟨Equiv.ofBijective e hs.bijective_of_finite, he⟩

theorem tuple_perm_of_power_sums (φ : R →+* F)
    (hunit : ∀ a : R, φ a ≠ 0 → IsUnit a) (x y : Fin n → R)
    (hy : Function.Injective (fun i ↦ φ (y i)))
    (hsmall : ∀ k : ℕ, 0 < k → k ≤ n → IsUnit (k : R))
    (hp : ∀ k : ℕ, 0 < k → k ≤ n → (∑ i : Fin n, x i ^ k) = ∑ i : Fin n, y i ^ k) :
    ∃ e : Equiv.Perm (Fin n), ∀ i : Fin n, x i = y (e i) :=
  tuple_perm_of_rootPolynomial_eq φ hunit x y hy
    (tuple_rootPolynomial_eq_of_power_sums x y hsmall hp)

end CommRing

end Erdos421
