import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-! # Lifting a quadratic root to make the norm quotient coprime -/

namespace Erdos941

theorem root_coprime_twice {a b n : ℕ} (hroot : a ∣ b ^ 2 + n)
    (han : a.Coprime (2 * n)) : a.Coprime (2 * b) := by
  have ha2 : a.Coprime 2 := han.of_dvd_right (dvd_mul_right _ _)
  have han' : a.Coprime n := han.of_dvd_right (dvd_mul_left _ _)
  have hab : a.Coprime b := by
    apply Nat.coprime_of_dvd'
    intro p hp hpa hpb
    have hpsq : p ∣ b ^ 2 := dvd_trans hpb (dvd_pow_self b (by decide))
    have hpsum : p ∣ b ^ 2 + n := dvd_trans hpa hroot
    have hpn : p ∣ n := (Nat.dvd_add_right hpsq).mp hpsum
    exact dvd_trans (Nat.dvd_gcd hpa hpn) (by rw [han'.gcd_eq_one])
  exact ha2.mul_right hab

theorem exists_coprime_root_lift {a b n : ℕ} (ha : 0 < a)
    (hroot : a ∣ b ^ 2 + n) (hab : a.Coprime (2 * b)) :
    ∃ B k : ℕ, B % a = b % a ∧ B ^ 2 + n = a * k ∧ a.Coprime k := by
  obtain ⟨k, hk⟩ := hroot
  let r : ℕ := a - k % a + 1
  obtain ⟨t, htlt, ht⟩ := Nat.exists_mul_mod_eq_of_coprime r hab.symm ha.ne'
  have hmod : (k + 2 * b * t) % a = 1 % a := by
    rw [Nat.add_mod, ht]
    have hka := Nat.mod_lt k ha
    have hkr : k % a + r = a + 1 := by dsimp [r]; omega
    calc
      (k % a + r % a) % a = (k % a + r) % a := by simp only [Nat.add_mod, Nat.mod_mod]
      _ = (a + 1) % a := congrArg (· % a) hkr
      _ = 1 % a := by simp
  refine ⟨b + a * t, k + 2 * b * t + a * t ^ 2, ?_, ?_, ?_⟩
  · simp only [Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod]
  · nlinarith [hk]
  · apply Nat.Coprime.symm
    apply Nat.coprime_of_mul_modEq_one 1
    change ((k + 2 * b * t + a * t ^ 2) * 1) % a = 1 % a
    simpa only [mul_one, Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod] using hmod

end Erdos941
