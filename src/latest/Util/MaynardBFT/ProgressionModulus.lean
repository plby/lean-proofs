import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
# Adding a fixed arithmetic-progression modulus to the pre-sieve

Once the pre-sieve contains the prime factors of `q`, multiplying its modulus
by `q` changes its size and totient by the same factor, without changing
which integers are coprime to it.  Prime powers in `q` are retained.
-/

namespace MaynardBFT

theorem coprime_of_coprime_primorial {q D d : ℕ}
    (hq : 0 < q) (hD : q ≤ D) (hd : d.Coprime (primorial D)) :
    d.Coprime q := by
  apply Nat.coprime_of_dvd'
  intro p hp hpd hpq
  have hpD : p ≤ D := (Nat.le_of_dvd hq hpq).trans hD
  have hpW := hp.dvd_primorial_iff.mpr hpD
  simpa only [hd.gcd_eq_one] using Nat.dvd_gcd hpd hpW

theorem coprime_mul_primorial_iff {q D d : ℕ} (hq : 0 < q) (hD : q ≤ D) :
    d.Coprime (q * primorial D) ↔ d.Coprime (primorial D) := by
  rw [Nat.coprime_mul_iff_right]
  exact ⟨And.right, fun h => ⟨coprime_of_coprime_primorial hq hD h, h⟩⟩

theorem primeFactors_mul_primorial {q D : ℕ} (hq : 0 < q) (hD : q ≤ D) :
    (q * primorial D).primeFactors = (primorial D).primeFactors := by
  rw [Nat.primeFactors_mul hq.ne' (primorial_pos D).ne']
  apply Finset.union_eq_right.mpr
  intro p hp
  have hpdata := Nat.mem_primeFactors.mp hp
  apply Nat.mem_primeFactors.mpr
  refine ⟨hpdata.1, ?_, (primorial_pos D).ne'⟩
  apply hpdata.1.dvd_primorial_iff.mpr
  exact (Nat.le_of_dvd hq hpdata.2.1).trans hD

theorem totient_mul_primorial {q D : ℕ} (hq : 0 < q) (hD : q ≤ D) :
    (q * primorial D).totient = q * (primorial D).totient := by
  have heq : ((q * primorial D).totient : ℚ) =
      (q : ℚ) * ((primorial D).totient : ℚ) := by
    rw [Nat.totient_eq_mul_prod_factors, primeFactors_mul_primorial hq hD,
      Nat.cast_mul, Nat.totient_eq_mul_prod_factors]
    ring
  exact_mod_cast heq

end MaynardBFT
