import ErdosProblems.Erdos421.PrimePowerTuples

/-! # Reducing triangular polynomial systems to power sums -/

namespace Erdos421

open Polynomial

section CommRing

variable {R : Type*} [CommRing R] {m n : ℕ}

theorem sum_eval_eq_sum_coeff_power (x : Fin m → R) (P : R[X]) {k : ℕ}
    (hP : P.natDegree ≤ k) :
    (∑ i : Fin m, P.eval (x i)) =
      ∑ j ∈ Finset.range (k + 1), P.coeff j * ∑ i : Fin m, x i ^ j := by
  simp_rw [Polynomial.eval_eq_sum_range' (p := P) (Nat.lt_succ_of_le hP)]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- Equal sums for polynomials of successive degrees determine the first
power sums when their diagonal coefficients are units. -/
theorem power_sums_eq_of_triangular_polynomials (x y : Fin m → R) (P : Fin n → R[X])
    (hdegree : ∀ j, (P j).natDegree ≤ (j : ℕ) + 1)
    (hunit : ∀ j, IsUnit ((P j).coeff ((j : ℕ) + 1)))
    (hs : ∀ j, (∑ i : Fin m, (P j).eval (x i)) = ∑ i : Fin m, (P j).eval (y i)) :
    ∀ k : ℕ, k ≤ n → (∑ i : Fin m, x i ^ k) = ∑ i : Fin m, y i ^ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hkn
    by_cases hk : k = 0
    · subst k
      simp only [pow_zero]
    have hkp : 0 < k := Nat.pos_of_ne_zero hk
    let j : Fin n := ⟨k - 1, by omega⟩
    have hj : (j : ℕ) + 1 = k := by dsimp only [j]; omega
    have hdeg : (P j).natDegree ≤ k := by simpa only [hj] using hdegree j
    have hu : IsUnit ((P j).coeff k) := by simpa only [hj] using hunit j
    have he := hs j
    rw [sum_eval_eq_sum_coeff_power x (P j) hdeg,
      sum_eval_eq_sum_coeff_power y (P j) hdeg, Finset.sum_range_succ,
      Finset.sum_range_succ] at he
    have hlo : (∑ a ∈ Finset.range k, (P j).coeff a * ∑ i : Fin m, x i ^ a) =
        ∑ a ∈ Finset.range k, (P j).coeff a * ∑ i : Fin m, y i ^ a := by
      apply Finset.sum_congr rfl
      intro a ha
      have hak : a < k := Finset.mem_range.mp ha
      rw [ih a hak (Nat.le_trans (Nat.le_of_lt hak) hkn)]
    rw [hlo] at he
    exact hu.mul_left_cancel (add_left_cancel he)

end CommRing

open scoped Classical in
theorem primePower_polynomial_sum_fiber_card_le {p d n : ℕ} (hp : p.Prime) (hd : 0 < d)
    (hn : n < p) (S : Finset (Fin n → ZMod (p ^ d))) (y : Fin n → ZMod (p ^ d))
    (hy : Function.Injective (fun i ↦ primePowerReduction p d hd (y i)))
    (P : Fin n → (ZMod (p ^ d))[X])
    (hdegree : ∀ j, (P j).natDegree ≤ (j : ℕ) + 1)
    (hunit : ∀ j, IsUnit ((P j).coeff ((j : ℕ) + 1))) :
    (S.filter (fun x : Fin n → ZMod (p ^ d) ↦
      ∀ j, (∑ i : Fin n, (P j).eval (x i)) = ∑ i : Fin n, (P j).eval (y i))).card ≤
      n.factorial := by
  classical
  apply (Finset.card_le_card (t := S.filter (fun x : Fin n → ZMod (p ^ d) ↦
    ∀ k : ℕ, 0 < k → k ≤ n → (∑ i : Fin n, x i ^ k) = ∑ i : Fin n, y i ^ k)) ?_).trans
    (primePower_power_sum_fiber_card_le hp hd hn S y hy)
  intro x hx
  obtain ⟨hxS, hxeq⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hxS, fun k _ hkn ↦ ?_⟩
  exact power_sums_eq_of_triangular_polynomials x y P hdegree hunit hxeq k hkn

open scoped Classical in
/-- Integer triangular families satisfy the same bound whenever the prime
does not divide any diagonal coefficient. -/
theorem primePower_int_polynomial_sum_fiber_card_le {p d n : ℕ} (hp : p.Prime)
    (hd : 0 < d) (hn : n < p) (S : Finset (Fin n → ZMod (p ^ d)))
    (y : Fin n → ZMod (p ^ d))
    (hy : Function.Injective (fun i ↦ primePowerReduction p d hd (y i)))
    (P : Fin n → ℤ[X])
    (hdegree : ∀ j, (P j).natDegree ≤ (j : ℕ) + 1)
    (hcoeff : ∀ j, ¬(p : ℤ) ∣ (P j).coeff ((j : ℕ) + 1)) :
    (S.filter (fun x : Fin n → ZMod (p ^ d) ↦ ∀ j,
      (∑ i : Fin n, ((P j).map (Int.castRingHom (ZMod (p ^ d)))).eval (x i)) =
        ∑ i : Fin n, ((P j).map (Int.castRingHom (ZMod (p ^ d)))).eval (y i))).card ≤
      n.factorial := by
  apply primePower_polynomial_sum_fiber_card_le hp hd hn S y hy
  · intro j
    exact Polynomial.natDegree_map_le.trans (hdegree j)
  · intro j
    rw [Polynomial.coeff_map]
    apply isUnit_of_primePowerReduction_ne_zero hp hd
    simpa only [Int.coe_castRingHom, map_intCast, ne_eq,
      ZMod.intCast_zmod_eq_zero_iff_dvd] using hcoeff j

end Erdos421
