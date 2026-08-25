import ErdosProblems.Erdos964.AffineCoprimeSquarefreeRoots
import ErdosProblems.Erdos964.SelbergPrimeRemoval

/-!
# The scalar divisor condition at a semiprime value

If the larger prime does not divide the squarefree sieve divisor, only
the smaller prime can belong to the distinguished affine value. Removing
that prime gives precisely the coprime root classes counted in the second sum.
-/

namespace Erdos964

open scoped BigOperators

theorem squarefree_prime_quotient_coprime_semiprime (d p r : ℕ)
    (hd : Squarefree d) (hr : r.Prime)
    (hpd : p ∣ d) (hrd : ¬ r ∣ d) : (d / p).Coprime (p * r) := by
  have hmul : p * (d / p) = d := Nat.mul_div_cancel' hpd
  have hpcop : p.Coprime (d / p) := by
    apply Nat.coprime_of_squarefree_mul
    rwa [hmul]
  have hrcop : r.Coprime (d / p) := hr.coprime_iff_not_dvd.mpr
    (fun h => hrd (h.trans (Nat.div_dvd_of_dvd hpd)))
  exact hpcop.symm.mul_right hrcop.symm

theorem affine_semiprime_scalar_divisor_iff (A B : Fin 3 → ℕ) (j : Fin 3)
    (n d p r : ℕ) (hd : Squarefree d) (hp : p.Prime) (hr : r.Prime)
    (hrd : ¬ r ∣ d) (hvalue : A j * n + B j = p * r) :
    d ∣ ∏ i, (A i * n + B i) ↔
      d / Nat.gcd d p ∣ ∏ i, (A i * n + B i) ∧
        (d / Nat.gcd d p).Coprime (A j * n + B j) := by
  by_cases hpd : p ∣ d
  · rw [Nat.gcd_eq_right hpd]
    have hcop := squarefree_prime_quotient_coprime_semiprime d p r hd hr hpd hrd
    rw [← hvalue] at hcop
    rw [and_iff_left hcop]
    have hmul : p * (d / p) = d := Nat.mul_div_cancel' hpd
    have hpcop : p.Coprime (d / p) := by
      apply Nat.coprime_of_squarefree_mul
      rwa [hmul]
    constructor
    · exact fun h => (Nat.div_dvd_of_dvd hpd).trans h
    · intro hquot
      have hpvalue : p ∣ A j * n + B j := by rw [hvalue]; exact dvd_mul_right p r
      have hpprod : p ∣ ∏ i, (A i * n + B i) :=
        hpvalue.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
      have h := hpcop.mul_dvd_of_dvd_of_dvd hpprod hquot
      rwa [hmul] at h
  · have hpcop := (hp.coprime_iff_not_dvd.mpr hpd).symm
    have hrcop := (hr.coprime_iff_not_dvd.mpr hrd).symm
    have hcop : d.Coprime (A j * n + B j) := by
      rw [hvalue]
      exact hpcop.mul_right hrcop
    rw [hpcop.gcd_eq_one, Nat.div_one, and_iff_left hcop]

theorem affine_semiprime_scalar_root_iff (A B : Fin 3 → ℕ) (j : Fin 3)
    (n d p r : ℕ) (hd : Squarefree d) (hp : p.Prime) (hr : r.Prime)
    (hrd : ¬ r ∣ d) (hvalue : A j * n + B j = p * r) :
    d ∣ ∏ i, (A i * n + B i) ↔
      n % (d / Nat.gcd d p) ∈ affineCoprimeProductRoots A B j (d / Nat.gcd d p) := by
  have hdpos := Nat.pos_of_ne_zero hd.ne_zero
  have hgcdpos := Nat.gcd_pos_of_pos_left p hdpos
  have hquotpos : 0 < d / Nat.gcd d p :=
    Nat.div_pos (Nat.gcd_le_left p hdpos) hgcdpos
  rw [mod_mem_affineCoprimeProductRoots_iff A B j _ n hquotpos]
  exact affine_semiprime_scalar_divisor_iff A B j n d p r hd hp hr hrd hvalue

end Erdos964
