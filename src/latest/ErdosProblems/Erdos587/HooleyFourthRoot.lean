import Mathlib

/-! # Integer fourth-root scales for short progressions -/

namespace Erdos587

def deltaFourthRoot (Y : ℕ) : ℕ := Nat.sqrt (Nat.sqrt Y)

lemma deltaFourthRoot_pow_le (Y : ℕ) : deltaFourthRoot Y ^ 4 ≤ Y := by
  calc
    _ = (deltaFourthRoot Y ^ 2) ^ 2 := by ring
    _ ≤ (Nat.sqrt Y) ^ 2 := Nat.pow_le_pow_left (Nat.sqrt_le' (Nat.sqrt Y)) 2
    _ ≤ Y := Nat.sqrt_le' Y

lemma lt_deltaFourthRoot_succ_pow (Y : ℕ) : Y < (deltaFourthRoot Y + 1) ^ 4 := by
  have hinner := Nat.lt_succ_sqrt' Y
  have houter := Nat.lt_succ_sqrt' (Nat.sqrt Y)
  calc
    _ < (Nat.sqrt Y + 1) ^ 2 := hinner
    _ ≤ ((deltaFourthRoot Y + 1) ^ 2) ^ 2 :=
      Nat.pow_le_pow_left (Nat.succ_le_of_lt houter) 2
    _ = _ := by ring

lemma deltaFourthRoot_two_le {Y : ℕ} (hY : 16 ≤ Y) : 2 ≤ deltaFourthRoot Y := by
  apply Nat.le_sqrt'.mpr
  apply Nat.le_sqrt'.mpr
  simpa using hY

lemma deltaFourthRoot_power_size {N Y r : ℕ} (hN : N ≤ Y ^ r) :
    N ≤ (deltaFourthRoot Y + 1) ^ (4 * r) := by
  calc
    _ ≤ Y ^ r := hN
    _ ≤ ((deltaFourthRoot Y + 1) ^ 4) ^ r :=
      Nat.pow_le_pow_left (lt_deltaFourthRoot_succ_pow Y).le r
    _ = _ := (pow_mul _ _ _).symm

end Erdos587
