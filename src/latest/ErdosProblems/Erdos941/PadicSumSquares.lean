import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-! # An isotropic vector for three squares at every odd prime -/

namespace Erdos941

theorem padic_exists_sq_add_sq_neg_one (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ a b : PadicInt p, a ^ 2 + b ^ 2 = -1 := by
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (-1)
  have hchoice : ∃ a b : ZMod p, a ≠ 0 ∧ a ^ 2 + b ^ 2 = -1 := by
    by_cases ha : a = 0
    · refine ⟨b, a, ?_, by rw [add_comm]; exact hab⟩
      intro hb
      rw [ha, hb] at hab
      norm_num at hab
    · exact ⟨a, b, ha, hab⟩
  obtain ⟨a, b, ha, hab⟩ := hchoice
  let a0 : PadicInt p := a.val
  let b0 : PadicInt p := b.val
  have haNorm : ‖a0‖ = 1 := by
    apply PadicInt.norm_natCast_eq_one_iff.mpr
    apply hp.out.coprime_iff_not_dvd.mpr
    intro hdiv
    have hz := (ZMod.natCast_eq_zero_iff a.val p).mpr hdiv
    rw [ZMod.natCast_zmod_val] at hz
    exact ha hz
  have htwoNorm : ‖(2 : PadicInt p)‖ = 1 := by
    apply PadicInt.norm_natCast_eq_one_iff.mpr
    apply hp.out.coprime_iff_not_dvd.mpr
    intro hdiv
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hdiv |>.resolve_left hp.out.ne_one)
  have hsmall : ‖a0 ^ 2 + b0 ^ 2 + 1‖ < 1 := by
    have he : a0 ^ 2 + b0 ^ 2 + 1 = ((a.val ^ 2 + b.val ^ 2 + 1 : ℕ) : PadicInt p) := by
      dsimp [a0, b0]
      push_cast
      rfl
    rw [he, PadicInt.norm_natCast_lt_one_iff]
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hab, neg_add_cancel]
  let F : Polynomial (PadicInt p) := Polynomial.X ^ 2 + Polynomial.C (b0 ^ 2 + 1)
  have hF (x : PadicInt p) : F.aeval x = x ^ 2 + b0 ^ 2 + 1 := by
    simp [F, add_assoc]
  have hF' : F.derivative.aeval a0 = 2 * a0 := by
    simp [F, Polynomial.derivative_pow]
  have hH : ‖F.aeval a0‖ < ‖F.derivative.aeval a0‖ ^ 2 := by
    rw [hF, hF', norm_mul, htwoNorm, haNorm, mul_one, one_pow]
    exact hsmall
  obtain ⟨x, hx, _⟩ := hensels_lemma hH
  rw [hF] at hx
  exact ⟨x, b0, eq_neg_of_add_eq_zero_left hx⟩

end Erdos941
