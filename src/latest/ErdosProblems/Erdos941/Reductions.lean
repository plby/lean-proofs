import ErdosProblems.Erdos941.Forms
import Mathlib.Data.ZMod.Basic

/-!
# Arithmetic reductions and the exceptional congruence classes
-/

namespace Erdos941

theorem four_mul_identity (A B t : ℤ) :
    (A + B) ^ 2 + (A - B) ^ 2 + 8 * t ^ 2 =
      2 * norm3 A B (2 * t) := by
  unfold norm3
  ring

theorem even_coordinate_of_even_norm {A B C m : ℤ}
    (h : norm3 A B C = 2 * m) :
    (2 : ℤ) ∣ A ∨ (2 : ℤ) ∣ B ∨ (2 : ℤ) ∣ C := by
  have hres : ∀ a b c : ZMod 2,
      a ^ 2 + b ^ 2 + c ^ 2 = 0 → a = 0 ∨ b = 0 ∨ c = 0 := by decide
  have hh := congrArg (fun z : ℤ => (z : ZMod 2)) h
  simp only [norm3, Int.cast_add, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] at hh
  rw [show (2 : ZMod 2) = 0 from rfl, zero_mul] at hh
  rcases hres A B C hh with hA | hB | hC
  · exact Or.inl ((ZMod.intCast_zmod_eq_zero_iff_dvd A 2).mp hA)
  · exact Or.inr (Or.inl ((ZMod.intCast_zmod_eq_zero_iff_dvd B 2).mp hB))
  · exact Or.inr (Or.inr ((ZMod.intCast_zmod_eq_zero_iff_dvd C 2).mp hC))

theorem four_mul_form_of_two_mul_squares {m A B C : ℤ}
    (h : norm3 A B C = 2 * m) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 8 * z ^ 2 = 4 * m := by
  have base : ∀ A B C : ℤ, norm3 A B C = 2 * m → (2 : ℤ) ∣ C →
      ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 8 * z ^ 2 = 4 * m := by
    intro A B C hv hC
    obtain ⟨t, rfl⟩ := hC
    refine ⟨A + B, A - B, t, ?_⟩
    rw [four_mul_identity, hv]
    ring
  rcases even_coordinate_of_even_norm h with hA | hB | hC
  · apply base C B A
    · simpa [norm3, add_comm, add_left_comm, add_assoc] using h
    · exact hA
  · apply base A C B
    · simpa [norm3, add_comm, add_left_comm, add_assoc] using h
    · exact hB
  · exact base A B C h hC

theorem representable_four_mul_of_two_mul_squares {m : ℕ} (hm : 0 < m)
    {A B C : ℤ} (h : norm3 A B C = 2 * m) : Representable (4 * m) := by
  obtain ⟨x, y, z, hs⟩ := four_mul_form_of_two_mul_squares h
  apply representable_of_int_cube_form (by omega) 1 1 2 x y z
  norm_num
  exact hs

theorem representable_four_pow_mul_of_two_mul_squares {m : ℕ} (hm : 0 < m)
    (a : ℕ) {A B C : ℤ} (h : norm3 A B C = 2 * m) :
    Representable (4 ^ (a + 1) * m) := by
  have hr := (representable_four_mul_of_two_mul_squares hm h).mul_sq
    (pow_pos (by norm_num : 0 < (2 : ℕ)) a)
  convert hr using 1
  have hpow : (2 ^ a) ^ 2 = (4 : ℕ) ^ a := by
    rw [← pow_mul, Nat.mul_comm a 2, pow_mul]
    norm_num
  rw [hpow, pow_succ]
  ring

theorem representable_twenty_seven_mul_of_squares {m : ℕ} (hm : 0 < m)
    {A B C : ℤ} (h : norm3 A B C = m) : Representable (27 * m) := by
  have hr := representable_of_three_squares hm A B C h
  exact hr.mul (by simpa using powerful_cube 3) (by norm_num)

/-- The two classes where the target sphere uses 5 or 13. -/
theorem odd_seven_mod_eight_three_unit {n : ℕ} (hn : n % 8 = 7)
    (h3 : ¬ 3 ∣ n) : n % 24 = 7 ∨ n % 24 = 23 := by omega

/-- The two classes where the target sphere uses 7 or 14. -/
theorem odd_seven_mod_eight_exactly_one_three {n : ℕ} (hn : n % 8 = 7)
    (h3 : 3 ∣ n) (h9 : ¬ 9 ∣ n) : n % 72 = 15 ∨ n % 72 = 39 := by omega

theorem div_nine_seven_mod_eight {n : ℕ} (hn : n % 8 = 7) (h9 : 9 ∣ n) :
    n / 9 % 8 = 7 := by omega

theorem div_nine_three_unit {n : ℕ} (h9 : 9 ∣ n) (h27 : ¬ 27 ∣ n) :
    ¬ 3 ∣ n / 9 := by omega

theorem div_twenty_seven_five_mod_eight {n : ℕ} (hn : n % 8 = 7)
    (h27 : 27 ∣ n) : n / 27 % 8 = 5 := by omega

theorem representable_of_div_nine {n : ℕ} (h9 : 9 ∣ n)
    (h : Representable (n / 9)) : Representable n := by
  have hh := h.mul_sq (by norm_num : 0 < (3 : ℕ))
  norm_num at hh
  rwa [Nat.mul_div_cancel' h9] at hh

theorem representable_of_div_twenty_seven_squares {n : ℕ} (hn : 0 < n)
    (h27 : 27 ∣ n) {A B C : ℤ} (h : norm3 A B C = (n / 27 : ℕ)) :
    Representable n := by
  have hpos : 0 < n / 27 := by omega
  have hh := representable_twenty_seven_mul_of_squares hpos h
  rwa [Nat.mul_div_cancel' h27] at hh

end Erdos941
