import ErdosProblems.Erdos633b.OrderedCornerColumns
import Mathlib.Tactic.IntervalCases

/-! Explicit small tables for a local angle deficit. All bounds follow from
strict angle order and the actual linear angle equation. -/

namespace Erdos633b

theorem nat_lt_of_real_mul_lt (b : ℝ) (hb : 0 < b) (q m : ℕ)
    (h : (q : ℝ) * b < (m : ℝ) * b) : q < m := by
  exact_mod_cast (mul_lt_mul_iff_left₀ hb).mp h

def OneZeroPattern (q r : ℕ) : Prop :=
  (r = 0 ∧ 3 ≤ q ∧ q ≤ 5) ∨ (r = 2 ∧ q = 0)

def TwoZeroPattern (q r : ℕ) : Prop :=
  (r = 0 ∧ 5 ≤ q ∧ q ≤ 11) ∨ (r = 1 ∧ 4 ≤ q ∧ q ≤ 7) ∨
  (r = 2 ∧ q = 3) ∨ (r = 3 ∧ q ≤ 2) ∨ (r = 4 ∧ q ≤ 1) ∨ (r = 5 ∧ q = 0)

def TwoOnePattern (q r : ℕ) : Prop :=
  (r = 0 ∧ 5 ≤ q ∧ q ≤ 10) ∨ (r = 1 ∧ 4 ≤ q ∧ q ≤ 6) ∨
  (r = 3 ∧ q ≤ 1) ∨ (r = 4 ∧ q = 0)

theorem one_zero_pattern (α β γ : ℝ) (hα : 0 < α) (h01 : α < β) (h12 : β < γ)
    (hs : α + β + γ = Real.pi) (hγ : γ ≤ 2 * Real.pi / 3)
    (q r : ℕ) (hr : r ≤ 5) (he : (q : ℝ) * β + (r : ℝ) * γ = Real.pi) :
    OneZeroPattern q r := by
  have hb : 0 < β := hα.trans h01
  have hb6 : Real.pi / 6 < β := by linarith
  have hb2 : β < Real.pi / 2 := by linarith
  have hc3 : Real.pi / 3 < γ := by linarith
  have hq0 : 0 ≤ (q : ℝ) * β := mul_nonneg (Nat.cast_nonneg _) hb.le
  unfold OneZeroPattern
  interval_cases r <;> norm_num at he
  · have hlo := nat_lt_of_real_mul_lt β hb 2 q (by norm_num; linarith)
    have hhi := nat_lt_of_real_mul_lt β hb q 6 (by norm_num; linarith)
    exact Or.inl ⟨rfl, by omega, by omega⟩
  · have hlo := nat_lt_of_real_mul_lt β hb 1 q (by norm_num; linarith)
    have hhi := nat_lt_of_real_mul_lt β hb q 2 (by norm_num; linarith)
    omega
  · have hhi := nat_lt_of_real_mul_lt β hb q 1 (by norm_num; linarith)
    exact Or.inr ⟨rfl, by omega⟩
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith

theorem two_zero_pattern (α β γ : ℝ) (hα : 0 < α) (h01 : α < β) (h12 : β < γ)
    (hs : α + β + γ = Real.pi) (hγ : γ ≤ 2 * Real.pi / 3)
    (q r : ℕ) (hr : r ≤ 5) (he : (q : ℝ) * β + (r : ℝ) * γ = 2 * Real.pi) :
    TwoZeroPattern q r := by
  have hb : 0 < β := hα.trans h01
  have hb6 : Real.pi / 6 < β := by linarith
  have hb2 : β < Real.pi / 2 := by linarith
  unfold TwoZeroPattern
  interval_cases r <;> norm_num at he
  · have hlo := nat_lt_of_real_mul_lt β hb 4 q (by norm_num; linarith)
    have hhi := nat_lt_of_real_mul_lt β hb q 12 (by norm_num; linarith)
    exact Or.inl ⟨rfl, by omega, by omega⟩
  · have hlo := nat_lt_of_real_mul_lt β hb 3 q (by norm_num; linarith)
    have hhi := nat_lt_of_real_mul_lt β hb q 8 (by norm_num; linarith)
    exact Or.inr (Or.inl ⟨rfl, by omega, by omega⟩)
  · have hlo := nat_lt_of_real_mul_lt β hb 2 q (by norm_num; linarith)
    have hhi := nat_lt_of_real_mul_lt β hb q 4 (by norm_num; linarith)
    exact Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))
  · have hhi := nat_lt_of_real_mul_lt β hb q 3 (by norm_num; linarith)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩)))
  · have hhi := nat_lt_of_real_mul_lt β hb q 2 (by norm_num; linarith)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))))
  · have hhi := nat_lt_of_real_mul_lt β hb q 1 (by norm_num; linarith)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, by omega⟩))))

theorem two_one_pattern (α β γ : ℝ) (hα : 0 < α) (h01 : α < β) (h12 : β < γ)
    (hs : α + β + γ = Real.pi) (hγ : γ ≤ 2 * Real.pi / 3)
    (q r : ℕ) (hr : r ≤ 5)
    (he : α + (q : ℝ) * β + (r : ℝ) * γ = 2 * Real.pi) : TwoOnePattern q r := by
  have hb : 0 < β := hα.trans h01
  have hb6 : Real.pi / 6 < β := by linarith
  have hb2 : β < Real.pi / 2 := by linarith
  have hc3 : Real.pi / 3 < γ := by linarith
  have hq0 : 0 ≤ (q : ℝ) * β := mul_nonneg (Nat.cast_nonneg _) hb.le
  unfold TwoOnePattern
  interval_cases r <;> norm_num at he
  · have hlo := nat_lt_of_real_mul_lt β hb 4 q (by norm_num; linarith)
    have hhi := nat_lt_of_real_mul_lt β hb q 11 (by norm_num; linarith)
    exact Or.inl ⟨rfl, by omega, by omega⟩
  · have hlo := nat_lt_of_real_mul_lt β hb 3 q (by norm_num; linarith)
    have hhi := nat_lt_of_real_mul_lt β hb q 7 (by norm_num; linarith)
    exact Or.inr (Or.inl ⟨rfl, by omega, by omega⟩)
  · have hlo := nat_lt_of_real_mul_lt β hb 2 q (by norm_num; linarith)
    have hhi := nat_lt_of_real_mul_lt β hb q 3 (by norm_num; linarith)
    omega
  · have hhi := nat_lt_of_real_mul_lt β hb q 2 (by norm_num; linarith)
    exact Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩))
  · have hhi := nat_lt_of_real_mul_lt β hb q 1 (by norm_num; linarith)
    exact Or.inr (Or.inr (Or.inr ⟨rfl, by omega⟩))
  · exfalso; linarith

end Erdos633b
