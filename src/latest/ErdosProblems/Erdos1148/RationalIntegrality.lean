import Mathlib

/-!
# Rational integrality detected at all primes

The global-to-local orbit injection uses this criterion on matrix entries.
-/

namespace Erdos1148.DukeArithmetic

lemma exists_int_of_forall_padic_norm_le_one (q : ℚ)
    (h : ∀ (p : ℕ) [Fact p.Prime], ‖(q : Padic p)‖ ≤ 1) :
    ∃ z : ℤ, (z : ℚ) = q := by
  suffices hden : q.den = 1 from ⟨q.num, Rat.coe_int_num_of_den_eq_one hden⟩
  by_contra hden
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hden
  let : Fact p.Prime := ⟨hp⟩
  have hunit := PadicInt.isUnit_den (p := p) q (h p)
  have heq := PadicInt.isUnit_iff.mp hunit
  have hlt : ‖(q.den : PadicInt p)‖ < 1 := PadicInt.norm_natCast_lt_one_iff.mpr hpdvd
  rw [heq] at hlt
  exact (lt_irrefl (1 : ℝ)) hlt

lemma exists_int_of_forall_padic_integral (q : ℚ)
    (h : ∀ (p : ℕ) [Fact p.Prime], ∃ z : PadicInt p, (z : Padic p) = (q : Padic p)) :
    ∃ z : ℤ, (z : ℚ) = q := by
  apply exists_int_of_forall_padic_norm_le_one q
  intro p hp
  obtain ⟨z, hz⟩ := h p
  rw [← hz]
  exact z.2

end Erdos1148.DukeArithmetic
