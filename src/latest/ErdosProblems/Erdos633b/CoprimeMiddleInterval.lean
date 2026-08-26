import ErdosProblems.Erdos633b.RationalSineNonzero
import Mathlib.Data.ZMod.Units

/-! Explicit coprime residues in the negative-cosine half-circle.
No search cutoff or asymptotic estimate is used. -/

namespace Erdos633b

theorem exists_coprime_middle_residue (D : ℕ) (hD : 6 < D) :
    ∃ r : ℕ, r.Coprime D ∧ D < 4 * r ∧ 4 * r < 3 * D := by
  by_cases hodd : Odd D
  · let r := (D - 1) / 2
    have he : D = 2 * r + 1 := by
      obtain ⟨t, ht⟩ := hodd
      dsimp only [r]
      omega
    refine ⟨r, ?_, by omega, by omega⟩
    rw [he, Nat.coprime_mul_right_add_right]
    simp
  · have hmod : D % 4 = 0 ∨ D % 4 = 2 := by
      rw [Nat.odd_iff] at hodd
      omega
    rcases hmod with hm | hm
    · let r := D / 2 - 1
      have he : D = 2 * r + 2 := by dsimp only [r]; omega
      have hr : Odd r := by rw [Nat.odd_iff]; dsimp only [r]; omega
      refine ⟨r, ?_, by dsimp only [r]; omega, by dsimp only [r]; omega⟩
      rw [he, Nat.coprime_mul_right_add_right]
      exact Nat.coprime_two_right.mpr hr
    · let r := D / 2 - 2
      have he : D = 2 * r + 4 := by dsimp only [r]; omega
      have hr : Odd r := by rw [Nat.odd_iff]; dsimp only [r]; omega
      refine ⟨r, ?_, by dsimp only [r]; omega, by dsimp only [r]; omega⟩
      rw [he, Nat.coprime_mul_right_add_right]
      simpa using (Nat.coprime_two_right.mpr hr).pow_right 2

theorem cosine_middle_residue_neg (D r : ℕ) (hD : 0 < D)
    (hl : D < 4 * r) (hu : 4 * r < 3 * D) :
    Real.cos (2 * Real.pi * r / D) < 0 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hl' : (D : ℝ) < 4 * r := by exact_mod_cast hl
  have hu' : (4 : ℝ) * r < 3 * D := by exact_mod_cast hu
  apply Real.cos_neg_of_pi_div_two_lt_of_lt
  · rw [lt_div_iff₀ hD']
    nlinarith [Real.pi_pos]
  · rw [div_lt_iff₀ hD']
    nlinarith [Real.pi_pos]

end Erdos633b
