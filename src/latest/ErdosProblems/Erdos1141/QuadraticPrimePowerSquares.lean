import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

/-!
# Squares in the principal congruence subgroups of prime-power units

Hensel's lemma handles both the odd-prime kernel modulo `p` and the
two-adic kernel modulo `8`.
-/

namespace Pollack17

open Polynomial

theorem isSquare_zmod_prime_pow_of_norm {p : ℕ} [Fact p.Prime]
    (a : ℤ) (n : ℕ) (ha : ‖((1 - a : ℤ) : ℤ_[p])‖ < ‖(2 : ℤ_[p])‖ ^ 2) :
    IsSquare (a : ZMod (p ^ n)) := by
  let F : Polynomial ℤ := X ^ 2 - C a
  have hder : F.derivative.aeval (1 : ℤ_[p]) = (2 : ℤ_[p]) := by
    norm_num [F, derivative_sub, derivative_pow, derivative_X]
    exact map_ofNat (aeval (1 : ℤ_[p])) 2
  have hnorm : ‖F.aeval (1 : ℤ_[p])‖ < ‖F.derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    rw [hder]
    simpa [F] using ha
  obtain ⟨z, hz, _⟩ := hensels_lemma hnorm
  have hsq : z ^ 2 = (a : ℤ_[p]) := by simpa [F, sub_eq_zero] using hz
  refine ⟨PadicInt.toZModPow n z, ?_⟩
  have hmap := congrArg (PadicInt.toZModPow n) hsq
  simpa only [map_pow, map_mul, map_intCast, pow_two] using hmap.symm

theorem isSquare_zmod_odd_prime_pow_of_one_mod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (a : ℤ) (n : ℕ) (ha : (p : ℤ) ∣ 1 - a) : IsSquare (a : ZMod (p ^ n)) := by
  have : Fact p.Prime := ⟨hp⟩
  apply isSquare_zmod_prime_pow_of_norm a n
  have hnorm : ‖(2 : ℤ_[p])‖ = 1 :=
    PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  rw [hnorm, one_pow]
  exact (PadicInt.norm_int_lt_one_iff_dvd (1 - a)).mpr ha

theorem isSquare_zmod_two_pow_of_one_mod_eight (a : ℤ) (n : ℕ)
    (ha : (8 : ℤ) ∣ 1 - a) : IsSquare (a : ZMod (2 ^ n)) := by
  apply isSquare_zmod_prime_pow_of_norm a n
  have hnorm : ‖((1 - a : ℤ) : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-(3 : ℕ) : ℤ) :=
    PadicInt.norm_int_le_pow_iff_dvd.mpr (by simpa using ha)
  have htwo : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := PadicInt.norm_p
  rw [htwo]
  refine hnorm.trans_lt ?_
  norm_num

end Pollack17
