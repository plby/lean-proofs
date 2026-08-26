import ErdosProblems.Erdos941.ThreeSquares
import ErdosProblems.Erdos941.Reductions

/-! # Unconditional representations outside the remaining odd classes -/

namespace Erdos941

theorem representable_four_free {n : ℕ} (hn : 0 < n) (h4 : ¬ 4 ∣ n)
    (h8 : n % 8 ≠ 7) : Representable n := by
  obtain ⟨X, Y, Z, hXYZ⟩ := three_squares_four_free hn h4 h8
  exact representable_of_three_squares hn X Y Z hXYZ

theorem representable_four_pow_mul_of_three_squares {m : ℕ} (hm : 0 < m)
    (a : ℕ) {X Y Z : ℤ} (h : norm3 X Y Z = m) : Representable (4 ^ a * m) := by
  have hr := (representable_of_three_squares hm X Y Z h).mul_sq
    (pow_pos (by norm_num : 0 < (2 : ℕ)) a)
  have hpow : (2 ^ a) ^ 2 = (4 : ℕ) ^ a := by
    rw [← pow_mul, Nat.mul_comm a 2, pow_mul]
    norm_num
  rwa [hpow] at hr

theorem representable_not_seven_mod_eight {n : ℕ} (hn : 0 < n) (h8 : n % 8 ≠ 7) :
    Representable n := by
  obtain ⟨a, m, h4, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 4 (by norm_num)
  have hm : 0 < m := by
    by_contra hh
    have : m = 0 := by omega
    simp only [this, mul_zero] at heq
    omega
  by_cases hm8 : m % 8 = 7
  · have ha : a ≠ 0 := by
      intro hh
      simp only [hh, pow_zero, one_mul] at heq
      exact h8 (heq ▸ hm8)
    obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
    have h2m : 0 < 2 * m := by omega
    have hfour : ¬ 4 ∣ 2 * m := by omega
    have heighth : (2 * m) % 8 ≠ 7 := by omega
    obtain ⟨X, Y, Z, hXYZ⟩ := three_squares_four_free h2m hfour heighth
    have hXYZ' : norm3 X Y Z = 2 * (m : ℤ) := by simpa using hXYZ
    rw [heq]
    exact representable_four_pow_mul_of_two_mul_squares hm b hXYZ'
  · obtain ⟨X, Y, Z, hXYZ⟩ := three_squares_four_free hm h4 hm8
    rw [heq]
    exact representable_four_pow_mul_of_three_squares hm a hXYZ

theorem representable_of_twenty_seven_dvd {n : ℕ} (hn : 0 < n) (h27 : 27 ∣ n) :
    Representable n := by
  by_cases h8 : n % 8 = 7
  · have hq8 := div_twenty_seven_five_mod_eight h8 h27
    have hqpos : 0 < n / 27 := by omega
    obtain ⟨X, Y, Z, hXYZ⟩ := three_squares_four_free hqpos (by omega) (by omega)
    exact representable_of_div_twenty_seven_squares hn h27 hXYZ
  · exact representable_not_seven_mod_eight hn h8

end Erdos941
