import Util.Bernays.LocalParity
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

/-!
# Multiplicative indicators supported on a prescribed set of primes
-/

open scoped Classical

namespace Bernays

def PrimeSupported (S : ℕ → Prop) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → S p

theorem primeSupported_one (S : ℕ → Prop) : PrimeSupported S 1 := by
  intro p hp hdiv
  exact False.elim (hp.not_dvd_one hdiv)

theorem primeSupported_mul_iff (S : ℕ → Prop) (m n : ℕ) :
    PrimeSupported S (m * n) ↔ PrimeSupported S m ∧ PrimeSupported S n := by
  constructor
  · intro h
    exact ⟨fun p hp hd => h p hp (hd.trans (dvd_mul_right m n)),
      fun p hp hd => h p hp (hd.trans (dvd_mul_left n m))⟩
  · rintro ⟨hm, hn⟩ p hp hd
    exact (hp.dvd_mul.mp hd).elim (hm p hp) (hn p hp)

noncomputable def primeSupportAF (S : ℕ → Prop) : ArithmeticFunction ℂ :=
  ⟨fun n => if 0 < n ∧ PrimeSupported S n then 1 else 0, by simp⟩

theorem primeSupportAF_isMultiplicative (S : ℕ → Prop) : (primeSupportAF S).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · simp [primeSupportAF, primeSupported_one]
  · intro m n hm hn _
    simp only [primeSupportAF, ArithmeticFunction.coe_mk, Nat.pos_iff_ne_zero, hm, hn,
      mul_ne_zero hm hn, true_and, primeSupported_mul_iff]
    by_cases h₁ : PrimeSupported S m <;> by_cases h₂ : PrimeSupported S n <;> simp [h₁, h₂, hm, hn]

theorem primeSupportAF_primePower (S : ℕ → Prop) {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 0 < e) :
    primeSupportAF S (p ^ e) = if S p then 1 else 0 := by
  have hs : PrimeSupported S (p ^ e) ↔ S p := by
    constructor
    · exact fun h => h p hp (dvd_pow_self p he.ne')
    · intro h q hq hdiv
      have hqp := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdiv)
      exact hqp ▸ h
  simp only [primeSupportAF, ArithmeticFunction.coe_mk, pow_pos hp.pos e, true_and, hs]

end Bernays
