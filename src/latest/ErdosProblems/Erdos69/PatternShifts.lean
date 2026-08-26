import ErdosProblems.Erdos69.CompositeDilations

/-! # The retained shifts and their unique smallest element -/

open scoped BigOperators

namespace Erdos69.Elementary

def patternShift (m P : ℕ) (i : PatternLabel m) (h : ℕ) : ℕ :=
  patternDilation m P i * h - patternOffset m P i

theorem patternIntercept_le_digit_mul {m h : ℕ} (hh : 6 * m ≤ h) (i : PatternLabel m) :
    patternIntercept m i ≤ patternDigit m i * h := by
  calc
    patternIntercept m i ≤ 6 * m * patternDigit m i := patternIntercept_le m i
    _ ≤ h * patternDigit m i := Nat.mul_le_mul_right _ hh
    _ = _ := Nat.mul_comm _ _

theorem patternShift_eq {m P h : ℕ} (hh : 6 * m ≤ h) (i : PatternLabel m) :
    patternShift m P i h = (primorial P + 1) * h +
      primorial P * (patternDigit m i * h - patternIntercept m i) := by
  unfold patternShift patternDilation roughDilation patternOffset
  have hle := patternIntercept_le_digit_mul hh i
  have heq : (1 + primorial P * (1 + patternDigit m i)) * h =
      (primorial P + 1) * h + primorial P * (patternDigit m i * h) := by ring
  rw [heq, Nat.add_sub_assoc (Nat.mul_le_mul_left _ hle), Nat.mul_sub_left_distrib]

theorem patternShift_zero (m P h : ℕ) :
    patternShift m P (patternZero m) h = (primorial P + 1) * h := by
  simp [patternShift, patternDilation, roughDilation, patternOffset,
    patternDigit_zero, patternIntercept_zero, add_comm]

theorem patternShift_lower {m P h : ℕ} (hh : 6 * m ≤ h) (i : PatternLabel m) :
    (primorial P + 1) * h ≤ patternShift m P i h := by
  rw [patternShift_eq hh]
  omega

theorem patternShift_strict_of_ne_zero {m P h : ℕ} (hh : 6 * m < h)
    (i : PatternLabel m) (hi : i ≠ patternZero m) :
    (primorial P + 1) * h < patternShift m P i h := by
  have hd : 0 < patternDigit m i := by
    have hne : patternDigit m i ≠ 0 := by
      intro hz
      exact hi ((patternDigit_eq_zero_iff m i).mp hz)
    omega
  have hmul : 6 * m * patternDigit m i < patternDigit m i * h := by
    simpa only [Nat.mul_comm (6 * m)] using Nat.mul_lt_mul_of_pos_left hh hd
  have hsub : 0 < patternDigit m i * h - patternIntercept m i :=
    Nat.sub_pos_of_lt ((patternIntercept_le m i).trans_lt hmul)
  rw [patternShift_eq hh.le]
  exact Nat.lt_add_of_pos_right (Nat.mul_pos (primorial_pos P) hsub)

theorem patternShift_pos {m P h : ℕ} (hh : 6 * m < h) (i : PatternLabel m) :
    0 < patternShift m P i h := by
  have hbase : 0 < (primorial P + 1) * h := Nat.mul_pos (by omega) (by omega)
  exact hbase.trans_le (patternShift_lower hh.le i)

theorem patternShift_minimal {m P h : ℕ} (hh : 6 * m < h) (i : PatternLabel m) :
    (primorial P + 1) * (6 * m + 1) ≤ patternShift m P i h := by
  exact (Nat.mul_le_mul_left _ (by omega : 6 * m + 1 ≤ h)).trans
    (patternShift_lower hh.le i)

theorem patternShift_eq_minimal_iff {m P h : ℕ} (hh : 6 * m < h) (i : PatternLabel m) :
    patternShift m P i h = (primorial P + 1) * (6 * m + 1) ↔
      i = patternZero m ∧ h = 6 * m + 1 := by
  constructor
  · intro heq
    have hbase := patternShift_lower (P := P) hh.le i
    have hh' : h = 6 * m + 1 := by
      rw [heq] at hbase
      have hle : h ≤ 6 * m + 1 := by nlinarith
      omega
    refine ⟨?_, hh'⟩
    by_contra hi
    have hs := patternShift_strict_of_ne_zero hh i hi (P := P)
    rw [heq, hh'] at hs
    exact (lt_irrefl _ hs)
  · rintro ⟨rfl, rfl⟩
    exact patternShift_zero m P _

theorem patternShift_le_dilation_mul (m P h : ℕ) (i : PatternLabel m) :
    patternShift m P i h ≤ patternDilation m P i * h := Nat.sub_le _ _

end Erdos69.Elementary
