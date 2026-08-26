import ErdosProblems.Erdos941.AuxiliaryEven

/-! # Three squares away from the classical obstruction -/

namespace Erdos941

theorem three_squares_squarefree {m : ℕ} (hm : 0 < m) (hsq : Squarefree m)
    (hm8 : m % 8 ≠ 7) : ∃ X Y Z : ℤ, norm3 X Y Z = m := by
  by_cases h2 : 2 ∣ m
  · exact three_squares_squarefree_even hm hsq h2
  · by_cases h4 : m % 4 = 1
    · exact three_squares_squarefree_one_mod_four hm hsq h4
    · have hm3 : m % 8 = 3 := by omega
      exact three_squares_squarefree_three_mod_eight hm hsq hm3

theorem odd_sq_mod_eight {n : ℕ} (h : Odd n) : n ^ 2 % 8 = 1 := by
  have h2 := Nat.odd_iff.mp h
  have hh : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  rw [Nat.pow_mod]
  rcases hh with h | h | h | h <;> rw [h]

theorem three_squares_four_free {n : ℕ} (hn : 0 < n) (h4 : ¬ 4 ∣ n)
    (h8 : n % 8 ≠ 7) : ∃ X Y Z : ℤ, norm3 X Y Z = n := by
  obtain ⟨m, s, heq, hsq⟩ := Nat.sq_mul_squarefree n
  have hm : 0 < m := by
    by_contra h
    have : m = 0 := by omega
    simp only [this, mul_zero] at heq
    omega
  have hs2 : ¬ 2 ∣ s := by
    intro hd
    apply h4
    rw [← heq]
    exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hd 2) m
  have hso : Odd s := Nat.odd_iff.mpr (by omega)
  have hs8 := odd_sq_mod_eight hso
  have hmod : n % 8 = m % 8 := by
    rw [← heq, Nat.mul_mod, hs8, one_mul, Nat.mod_mod]
  obtain ⟨X, Y, Z, hXYZ⟩ := three_squares_squarefree hm hsq (hmod ▸ h8)
  refine ⟨s * X, s * Y, s * Z, ?_⟩
  have hn' : (s : ℤ) ^ 2 * m = n := by exact_mod_cast heq
  dsimp [norm3] at hXYZ ⊢
  calc
    _ = (s : ℤ) ^ 2 * (X ^ 2 + Y ^ 2 + Z ^ 2) := by ring
    _ = n := by rw [hXYZ]; exact hn'

/-- The existence direction of Legendre's three-square theorem. -/
theorem three_squares_of_no_obstruction {n : ℕ} (hn : 0 < n)
    (hobs : ∀ a b : ℕ, n ≠ 4 ^ a * (8 * b + 7)) :
    ∃ X Y Z : ℤ, norm3 X Y Z = n := by
  obtain ⟨a, m, h4, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' 4 (by norm_num)
  have hm : 0 < m := by
    by_contra h
    have : m = 0 := by omega
    simp only [this, mul_zero] at heq
    omega
  have h8 : m % 8 ≠ 7 := by
    intro hh
    apply hobs a (m / 8)
    rw [heq]
    congr 1
    omega
  obtain ⟨X, Y, Z, hXYZ⟩ := three_squares_four_free hm h4 h8
  refine ⟨(2 : ℤ) ^ a * X, (2 : ℤ) ^ a * Y, (2 : ℤ) ^ a * Z, ?_⟩
  have hs : ((2 : ℤ) ^ a) ^ 2 = 4 ^ a := by
    rw [← pow_mul, Nat.mul_comm a 2, pow_mul]
    norm_num
  dsimp [norm3] at hXYZ ⊢
  calc
    _ = ((2 : ℤ) ^ a) ^ 2 * (X ^ 2 + Y ^ 2 + Z ^ 2) := by ring
    _ = n := by rw [hs, hXYZ]; exact_mod_cast heq.symm

end Erdos941
