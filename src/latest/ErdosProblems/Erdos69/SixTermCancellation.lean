import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Six-term cancellation

The two explicit six-point patterns cancel the directions `{1,2,4}` and
`{3,5,6}`. Their product cancels six consecutive directions using only
36 signed terms, rather than 64.
-/

open scoped BigOperators

namespace Erdos69.Elementary

def hexDigit : Fin 6 → ℕ := ![0, 1, 2, 4, 5, 6]

def hexSign : Fin 6 → ℤ := ![1, -1, -1, 1, 1, -1]

def hexInterceptA : Fin 6 → ℕ := ![0, 4, 2, 10, 8, 12]

def hexInterceptB : Fin 6 → ℕ := ![0, 3, 12, 18, 27, 30]

theorem hexDigit_lt_seven (i : Fin 6) : hexDigit i < 7 := by
  fin_cases i <;> norm_num [hexDigit]

theorem hexDigit_injective : Function.Injective hexDigit := by
  decide

@[simp] theorem hexDigit_eq_zero_iff (i : Fin 6) : hexDigit i = 0 ↔ i = 0 := by
  fin_cases i <;> norm_num [hexDigit]

theorem hexSign_sq (i : Fin 6) : hexSign i ^ 2 = 1 := by
  fin_cases i <;> norm_num [hexSign]

theorem hexSign_abs (i : Fin 6) : |hexSign i| = 1 := by
  fin_cases i <;> norm_num [hexSign]

theorem hexInterceptA_le (i : Fin 6) : hexInterceptA i ≤ 6 * hexDigit i := by
  fin_cases i <;> norm_num [hexInterceptA, hexDigit]

theorem hexInterceptB_le (i : Fin 6) : hexInterceptB i ≤ 6 * hexDigit i := by
  fin_cases i <;> norm_num [hexInterceptB, hexDigit]

theorem sum_hexSign : ∑ i : Fin 6, hexSign i = 0 := by
  norm_num [Fin.sum_univ_succ, hexSign]

def hexSignedSum (mu : Fin 6 → ℕ) (h : ℤ) (f : ℤ → ℝ) : ℝ :=
  ∑ i : Fin 6, (hexSign i : ℝ) * f ((hexDigit i : ℤ) * h - mu i)

theorem hexSignedSum_A_one (f : ℤ → ℝ) : hexSignedSum hexInterceptA 1 f = 0 := by
  norm_num [hexSignedSum, Fin.sum_univ_succ, hexSign, hexDigit, hexInterceptA]

theorem hexSignedSum_A_two (f : ℤ → ℝ) : hexSignedSum hexInterceptA 2 f = 0 := by
  norm_num [hexSignedSum, Fin.sum_univ_succ, hexSign, hexDigit, hexInterceptA]
  ring

theorem hexSignedSum_A_four (f : ℤ → ℝ) : hexSignedSum hexInterceptA 4 f = 0 := by
  norm_num [hexSignedSum, Fin.sum_univ_succ, hexSign, hexDigit, hexInterceptA]

theorem hexSignedSum_B_three (f : ℤ → ℝ) : hexSignedSum hexInterceptB 3 f = 0 := by
  norm_num [hexSignedSum, Fin.sum_univ_succ, hexSign, hexDigit, hexInterceptB]

theorem hexSignedSum_B_five (f : ℤ → ℝ) : hexSignedSum hexInterceptB 5 f = 0 := by
  norm_num [hexSignedSum, Fin.sum_univ_succ, hexSign, hexDigit, hexInterceptB]
  ring

theorem hexSignedSum_B_six (f : ℤ → ℝ) : hexSignedSum hexInterceptB 6 f = 0 := by
  norm_num [hexSignedSum, Fin.sum_univ_succ, hexSign, hexDigit, hexInterceptB]

abbrev BlockLabel := Fin 6 × Fin 6

def blockDigit (i : BlockLabel) : ℕ := hexDigit i.1 + 7 * hexDigit i.2

def blockIntercept (i : BlockLabel) : ℕ := hexInterceptA i.1 + 7 * hexInterceptB i.2

def blockSign (i : BlockLabel) : ℤ := hexSign i.1 * hexSign i.2

theorem blockDigit_lt (i : BlockLabel) : blockDigit i < 49 := by
  have h₁ := hexDigit_lt_seven i.1
  have h₂ := hexDigit_lt_seven i.2
  dsimp [blockDigit]
  omega

theorem blockDigit_injective : Function.Injective blockDigit := by
  intro i j hij
  have hi := hexDigit_lt_seven i.1
  have hj := hexDigit_lt_seven j.1
  have h₁ : hexDigit i.1 = hexDigit j.1 := by
    dsimp [blockDigit] at hij
    omega
  have h₂ : hexDigit i.2 = hexDigit j.2 := by
    dsimp [blockDigit] at hij
    omega
  exact Prod.ext (hexDigit_injective h₁) (hexDigit_injective h₂)

theorem blockIntercept_le (i : BlockLabel) : blockIntercept i ≤ 6 * blockDigit i := by
  have h₁ := hexInterceptA_le i.1
  have h₂ := hexInterceptB_le i.2
  dsimp [blockIntercept, blockDigit]
  omega

theorem blockSign_abs (i : BlockLabel) : |blockSign i| = 1 := by
  simp [blockSign, abs_mul, hexSign_abs]

theorem sum_blockSign : ∑ i : BlockLabel, blockSign i = 0 := by
  simp [blockSign, Fintype.sum_prod_type, ← Finset.mul_sum, sum_hexSign]

def blockSignedSum (h : ℤ) (f : ℤ → ℝ) : ℝ :=
  ∑ i : BlockLabel, (blockSign i : ℝ) *
    f ((blockDigit i : ℤ) * h - blockIntercept i)

theorem blockSignedSum_first (h : ℤ) (f : ℤ → ℝ) :
    blockSignedSum h f = ∑ j : Fin 6, (hexSign j : ℝ) *
      hexSignedSum hexInterceptA h
        (fun t ↦ f (t + 7 * ((hexDigit j : ℤ) * h - hexInterceptB j))) := by
  unfold blockSignedSum
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [hexSignedSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have harg : ((blockDigit (i, j) : ℕ) : ℤ) * h - blockIntercept (i, j) =
      ((hexDigit i : ℤ) * h - hexInterceptA i) +
        7 * ((hexDigit j : ℤ) * h - hexInterceptB j) := by
    simp only [blockDigit, blockIntercept, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [harg]
  simp only [blockSign, Int.cast_mul]
  ring

theorem blockSignedSum_second (h : ℤ) (f : ℤ → ℝ) :
    blockSignedSum h f = ∑ i : Fin 6, (hexSign i : ℝ) *
      hexSignedSum hexInterceptB h
        (fun t ↦ f (((hexDigit i : ℤ) * h - hexInterceptA i) + 7 * t)) := by
  unfold blockSignedSum
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [hexSignedSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have harg : ((blockDigit (i, j) : ℕ) : ℤ) * h - blockIntercept (i, j) =
      ((hexDigit i : ℤ) * h - hexInterceptA i) +
        7 * ((hexDigit j : ℤ) * h - hexInterceptB j) := by
    simp only [blockDigit, blockIntercept, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [harg]
  simp only [blockSign, Int.cast_mul]
  ring

theorem blockSignedSum_vanish {h : ℕ} (hpos : 1 ≤ h) (hle : h ≤ 6)
    (f : ℤ → ℝ) : blockSignedSum h f = 0 := by
  interval_cases h
  · simp [blockSignedSum_first, hexSignedSum_A_one]
  · simp [blockSignedSum_first, hexSignedSum_A_two]
  · simp [blockSignedSum_second, hexSignedSum_B_three]
  · simp [blockSignedSum_first, hexSignedSum_A_four]
  · simp [blockSignedSum_second, hexSignedSum_B_five]
  · simp [blockSignedSum_second, hexSignedSum_B_six]

end Erdos69.Elementary
