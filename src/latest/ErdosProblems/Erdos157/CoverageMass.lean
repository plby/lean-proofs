import ErdosProblems.Erdos157.LocalChoiceCounts
import ErdosProblems.Erdos157.GoodFibers

/-! The large coefficient field makes the supply of trials exceed the cost of all choices. -/

namespace Erdos157.Elementary

open AuxiliaryModuli

theorem level_excess_dyadic_lower (k : ℕ) :
    50 * k ^ 2 ≤ 1024 * (3 * levelDegree k - k ^ 2) := by
  have hreal := levelDegree_lower k
  have hr : (7 : ℝ) * (k : ℝ) ^ 2 ≤ 20 * (levelDegree k : ℝ) := by linarith
  have hn : 7 * k ^ 2 ≤ 20 * levelDegree k := by exact_mod_cast hr
  have hs := Nat.sub_add_cancel (square_le_triple_levelDegree k)
  nlinarith

theorem coverage_mass_nat (k : ℕ) (hk : 400 ≤ k) :
    1024 * levelDegree k ^ 3 * Fintype.card (LocalChoice CoefficientField k) ^ 3 * 2 ^ (k ^ 2) ≤
      Fintype.card CoefficientField ^ (3 * levelDegree k - k ^ 2) := by
  have hd : levelDegree k ≤ k ^ 2 := by have := double_levelDegree_lt_square k (by omega); omega
  have hdpow : levelDegree k ^ 3 ≤ 2 ^ (6 * k) := by
    calc
      _ ≤ (k ^ 2) ^ 3 := Nat.pow_le_pow_left hd _
      _ = k ^ 6 := by rw [← pow_mul]
      _ ≤ (2 ^ k) ^ 6 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
      _ = _ := by rw [← pow_mul, mul_comm k 6]
  have hchoice : Fintype.card (LocalChoice CoefficientField k) ^ 3 ≤ 2 ^ (21 * k ^ 2 + 9282 * k) := by
    calc
      _ ≤ (2 ^ (7 * k ^ 2 + 3094 * k)) ^ 3 := Nat.pow_le_pow_left (card_localChoice_coefficientField_le k) _
      _ = _ := by rw [← pow_mul]; congr 1; ring
  calc
    _ ≤ (2 ^ 10 * 2 ^ (6 * k)) * 2 ^ (21 * k ^ 2 + 9282 * k) * 2 ^ (k ^ 2) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left 1024 hdpow) hchoice)
    _ = 2 ^ (22 * k ^ 2 + 9288 * k + 10) := by
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 1
      ring
    _ ≤ 2 ^ (50 * k ^ 2) := Nat.pow_le_pow_right (by decide) (by nlinarith)
    _ ≤ 2 ^ (1024 * (3 * levelDegree k - k ^ 2)) :=
      Nat.pow_le_pow_right (by decide) (level_excess_dyadic_lower k)
    _ = _ := by rw [card_coefficientField, pow_mul]

theorem coverage_trial_mass (k : ℕ) (hk : 400 ≤ k) :
    (2 : ℝ) ^ (k ^ 2) ≤ fiberThreshold (K := CoefficientField) k /
      (Fintype.card (LocalChoice CoefficientField k) : ℝ) ^ 3 := by
  have hdpos : (0 : ℝ) < levelDegree k := by
    have h := levelDegree_lower k
    have hk' : (400 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hcpos : (0 : ℝ) < Fintype.card (LocalChoice CoefficientField k) := by
    exact_mod_cast Fintype.card_pos (α := LocalChoice CoefficientField k)
  have hn := coverage_mass_nat k hk
  have hr : (1024 : ℝ) * (levelDegree k : ℝ) ^ 3 *
      (Fintype.card (LocalChoice CoefficientField k) : ℝ) ^ 3 * (2 : ℝ) ^ (k ^ 2) ≤
        (Fintype.card CoefficientField : ℝ) ^ (3 * levelDegree k - k ^ 2) := by exact_mod_cast hn
  unfold fiberThreshold
  apply (le_div_iff₀ (pow_pos hcpos 3)).mpr
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ = (1024 : ℝ) * (levelDegree k : ℝ) ^ 3 *
        (Fintype.card (LocalChoice CoefficientField k) : ℝ) ^ 3 * (2 : ℝ) ^ (k ^ 2) := by ring
    _ ≤ _ := hr

end Erdos157.Elementary
