import ErdosProblems.Erdos534.Erdos534PrimeCounting
import ErdosProblems.Erdos534.Erdos534FiniteCertificate

namespace Erdos534

lemma three_primeCounting_le_five_of_ne_seven {x : ℕ}
    (hx5 : 5 ≤ x) (hx7 : x ≠ 7) :
    3 * Nat.primeCounting x ≤ Nat.primeCounting (5 * x) := by
  by_cases hxCut : x ≤ 20000
  · by_cases hx8 : 8 ≤ x
    · have hm := primeMargin_nonneg_eight_to_20000 hx8 hxCut
      have hi : (3 * Nat.primeCounting x : ℤ) ≤
          (Nat.primeCounting (5 * x) : ℤ) := (sub_nonneg.mp hm)
      exact_mod_cast hi
    · have hx : x = 5 ∨ x = 6 := by omega
      rcases hx with rfl | rfl <;> decide
  · have hxLarge : (20000 : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast (by omega : 20000 ≤ x)
    have h := analytic_three_primeCounting_le_five hxLarge
    have hfloor : ⌊5 * (x : ℝ)⌋₊ = 5 * x := by
      rw [show 5 * (x : ℝ) = ((5 * x : ℕ) : ℝ) by norm_num,
        Nat.floor_natCast]
    rw [Nat.floor_natCast, hfloor] at h
    exact_mod_cast h

lemma three_primeCounting_le_five_add_one {x : ℕ} (hx5 : 5 ≤ x) :
    3 * Nat.primeCounting x ≤ Nat.primeCounting (5 * x) + 1 := by
  by_cases hx7 : x = 7
  · subst x
    decide
  · exact (three_primeCounting_le_five_of_ne_seven hx5 hx7).trans
      (Nat.le_succ _)

lemma three_primeCounting_le_square {p : ℕ} (hp5 : 5 ≤ p) :
    3 * Nat.primeCounting p ≤ Nat.primeCounting (p * p) := by
  by_cases hp7 : p = 7
  · subst p
    decide
  · exact (three_primeCounting_le_five_of_ne_seven hp5 hp7).trans
      (Nat.monotone_primeCounting (Nat.mul_le_mul_right p hp5))

lemma indexed_prime_count_of_rho_small {p s rho : ℕ}
    (hs : 3 ≤ s) (hpIndex : Nat.primeCounting p = s)
    (hp : p = oneBasedPrime s) (hrho : rho ≤ 2 * s - 1) :
    ∀ ell, 1 ≤ ell →
      rho + s + 2 * ell - 1 ≤
        Nat.primeCounting (p * oneBasedPrime (s + ell - 1)) := by
  have hs1 : 1 ≤ s := by omega
  have hpPrime : p.Prime := hp.symm ▸ oneBasedPrime_prime hs1
  have hp4 : 4 ≤ p := by
    rw [hp]
    exact (by omega : 4 ≤ s + 1).trans (add_one_le_oneBasedPrime hs1)
  have hp5 : 5 ≤ p := by
    have hpOdd : Odd p := hpPrime.odd_of_ne_two (by omega)
    rcases hpOdd with ⟨k, hk⟩
    omega
  intro ell hell
  by_cases hell1 : ell = 1
  · subst ell
    have hsq := three_primeCounting_le_square hp5
    rw [hpIndex] at hsq
    simp only [add_tsub_cancel_right]
    rw [← hp]
    omega
  · have hell2 : 2 ≤ ell := by omega
    let X := oneBasedPrime (s + ell - 1)
    have hk1 : 1 ≤ s + ell - 1 := by omega
    have hXCount : Nat.primeCounting X = s + ell - 1 := by
      exact primeCounting_oneBasedPrime hk1
    have hXPrime : X.Prime := oneBasedPrime_prime hk1
    have hX5 : 5 ≤ X := by
      have hX4 : 4 ≤ X := by
        exact (by omega : 4 ≤ s + ell - 1 + 1).trans
          (add_one_le_oneBasedPrime hk1)
      have hXOdd : Odd X := hXPrime.odd_of_ne_two (by omega)
      rcases hXOdd with ⟨k, hk⟩
      omega
    have hfive := three_primeCounting_le_five_add_one hX5
    rw [hXCount] at hfive
    have hscale : 5 * X ≤ p * X := Nat.mul_le_mul_right X hp5
    have hmono := Nat.monotone_primeCounting hscale
    change rho + s + 2 * ell - 1 ≤ Nat.primeCounting (p * X)
    omega

lemma primeIntervalExpansion_of_small_rho {T : Finset ℕ}
    {p s rho : ℕ} (hs : 3 ≤ s) (hp : p.Prime)
    (hpIndex : Nat.primeCounting p = s)
    (hpValue : p = oneBasedPrime s)
    (hlarge : (T.filter fun r ↦ p < r).card ≤ rho)
    (hrho : rho ≤ 2 * s - 1) :
    PrimeIntervalExpansion T p := by
  apply primeIntervalExpansion_of_indexed_count hp (by omega) hpIndex hlarge
  exact indexed_prime_count_of_rho_small hs hpIndex hpValue hrho

end Erdos534
