import ErdosProblems.Erdos941.SevenHitting
import ErdosProblems.Erdos941.EasyCases

/-! # The four remaining congruence classes and the final arithmetic reduction -/

namespace Erdos941

theorem exists_large_seven_mod_twenty_four :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → n % 24 = 7 → Representable n := by
  obtain ⟨N, hN, hhit⟩ := exists_large_five_sphere_target
  refine ⟨N, hN, ?_⟩
  intro n hn h24
  obtain ⟨v, hv, hC⟩ := hhit (5 * n) (by omega) (by omega) (by omega) (by omega)
    (dvd_mul_right 5 n)
  have hv' : norm3 v.1 v.2.1 v.2.2 = 5 * (n : ℤ) := by simpa only [tripleNorm, Nat.cast_mul, Nat.cast_ofNat] using hv
  obtain ⟨x, y, z, hform⟩ := sphere_five_to_form hv' hC
  exact representable_of_five_form (hN.trans_le hn) hform

theorem exists_large_twenty_three_mod_twenty_four :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → n % 24 = 23 → Representable n := by
  obtain ⟨N, hN, hhit⟩ := exists_large_thirteen_sphere_target
  refine ⟨N, hN, ?_⟩
  intro n hn h24
  obtain ⟨v, hv, hC⟩ := hhit (13 * n) (by omega) (by omega) (by omega) (by omega)
    (dvd_mul_right 13 n)
  have hv' : norm3 v.1 v.2.1 v.2.2 = 13 * (n : ℤ) := by
    simpa only [tripleNorm, Nat.cast_mul, Nat.cast_ofNat] using hv
  obtain ⟨x, y, z, hform⟩ := sphere_thirteen_to_form hv' hC
  exact representable_of_thirteen_form (hN.trans_le hn) hform

theorem exists_large_fifteen_mod_seventy_two :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → n % 72 = 15 → Representable n := by
  obtain ⟨N, hN, hhit⟩ := exists_large_seven_sphere_target
  refine ⟨3 * N, by omega, ?_⟩
  intro n hn h72
  obtain ⟨v, hv, hT⟩ := hhit (7 * (n / 3)) (by omega) (by omega) (by omega)
    (dvd_mul_right 7 (n / 3))
  have hv' : norm3 v.1 v.2.1 v.2.2 = 7 * ((n / 3 : ℕ) : ℤ) := by
    simpa only [tripleNorm, Nat.cast_mul, Nat.cast_ofNat] using hv
  obtain ⟨x, y, z, hform⟩ := seven_target_to_form hv' hT
  have hn3 : (3 : ℤ) * ((n / 3 : ℕ) : ℤ) = n := by exact_mod_cast (show 3 * (n / 3) = n by omega)
  rw [hn3] at hform
  exact representable_of_seven_form (by omega) hform

theorem exists_large_thirty_nine_mod_seventy_two :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → n % 72 = 39 → Representable n := by
  obtain ⟨N, hN, hhit⟩ := exists_large_fourteen_sphere_target
  refine ⟨3 * N, by omega, ?_⟩
  intro n hn h72
  obtain ⟨v, hv, hT⟩ := hhit (14 * (n / 3)) (by omega) (by omega) (by omega)
    (by omega)
  have hv' : norm3 v.1 v.2.1 v.2.2 = 14 * ((n / 3 : ℕ) : ℤ) := by
    simpa only [tripleNorm, Nat.cast_mul, Nat.cast_ofNat] using hv
  obtain ⟨x, y, z, hform⟩ := fourteen_target_to_form hv' hT
  have hn3 : (3 : ℤ) * ((n / 3 : ℕ) : ℤ) = n := by exact_mod_cast (show 3 * (n / 3) = n by omega)
  rw [hn3] at hform
  exact representable_of_fourteen_form (by omega) hform

theorem exists_large_three_unit_representable :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → n % 8 = 7 → ¬3 ∣ n → Representable n := by
  obtain ⟨N₅, hN₅, h₅⟩ := exists_large_seven_mod_twenty_four
  obtain ⟨N₁₃, hN₁₃, h₁₃⟩ := exists_large_twenty_three_mod_twenty_four
  refine ⟨N₅ + N₁₃, by omega, ?_⟩
  intro n hn h8 h3
  rcases odd_seven_mod_eight_three_unit h8 h3 with h | h
  · exact h₅ n (by omega) h
  · exact h₁₃ n (by omega) h

theorem exists_large_exactly_one_three_representable :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → n % 8 = 7 → 3 ∣ n → ¬9 ∣ n → Representable n := by
  obtain ⟨N₇, hN₇, h₇⟩ := exists_large_fifteen_mod_seventy_two
  obtain ⟨N₁₄, hN₁₄, h₁₄⟩ := exists_large_thirty_nine_mod_seventy_two
  refine ⟨N₇ + N₁₄, by omega, ?_⟩
  intro n hn h8 h3 h9
  rcases odd_seven_mod_eight_exactly_one_three h8 h3 h9 with h | h
  · exact h₇ n (by omega) h
  · exact h₁₄ n (by omega) h

theorem exists_eventually_representable :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → Representable n := by
  obtain ⟨Nu, hNu, hu⟩ := exists_large_three_unit_representable
  obtain ⟨Nd, hNd, hd⟩ := exists_large_exactly_one_three_representable
  refine ⟨9 * (Nu + Nd), by omega, ?_⟩
  intro n hn
  have hn0 : 0 < n := by omega
  by_cases h8 : n % 8 = 7
  · by_cases h27 : 27 ∣ n
    · exact representable_of_twenty_seven_dvd hn0 h27
    · by_cases h9 : 9 ∣ n
      · apply representable_of_div_nine h9
        exact hu (n / 9) (by omega) (div_nine_seven_mod_eight h8 h9)
          (div_nine_three_unit h9 h27)
      · by_cases h3 : 3 ∣ n
        · exact hd n (by omega) h8 h3 h9
        · exact hu n (by omega) h8 h3
  · exact representable_not_seven_mod_eight hn0 h8

end Erdos941
