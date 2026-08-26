import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Explicit positive dimensions and exact finite counts for the group-2 construction. -/

namespace Erdos633b.GroupTwoDimensions

def scale (a b : ℕ) : ℕ := a + b + 2
def rowU (a b i : ℕ) : ℕ := a * (b - 1) + (i + 1) * b
def rowV (a b : ℕ) : ℕ := b * (a - 1) + a
def rowCount (a b i : ℕ) : ℕ := (2 * (scale a b + i) + 1) * (a * b)

theorem scale_pos (a b : ℕ) : 0 < scale a b := by unfold scale; omega

theorem rowU_pos (a b i : ℕ) (hb : 0 < b) : 0 < rowU a b i := by
  have h : 0 < (i + 1) * b := Nat.mul_pos (by omega) hb
  unfold rowU
  omega

theorem rowV_pos (a b : ℕ) (ha : 0 < a) : 0 < rowV a b := by unfold rowV; omega

theorem width_identity (a b i : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (scale a b + i) * (a * b) = a ^ 2 + b ^ 2 + (rowU a b i * a + rowV a b * b) := by
  cases a with
  | zero => omega
  | succ a =>
    cases b with
    | zero => omega
    | succ b =>
      simp only [scale, rowU, rowV, Nat.succ_sub_one]
      ring

theorem row_count_identity (a b c i : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (a ^ 2 + b ^ 2 + c ^ 2) + (2 * a * rowU a b i + 2 * rowV a b * b) = rowCount a b i := by
  calc
    _ = 2 * (a ^ 2 + b ^ 2 + (rowU a b i * a + rowV a b * b)) + a * b := by
      rw [hrel]
      ring
    _ = 2 * ((scale a b + i) * (a * b)) + a * b := by rw [width_identity a b i ha hb]
    _ = rowCount a b i := by unfold rowCount; ring

theorem sum_row_counts (a b n : ℕ) :
    (∑ i ∈ Finset.range n, rowCount a b i) = n * (2 * scale a b + n) * (a * b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    unfold rowCount
    ring

theorem stack_count_step (k n y : ℕ) :
    n * (2 * (k + 1) + n) * y + (2 * k + 1) * y = (n + 1) * (2 * k + (n + 1)) * y := by
  ring

theorem equilateral_count (a b : ℕ) :
    3 * (scale a b * (2 * scale a b + scale a b) * (a * b)) =
      9 * scale a b ^ 2 * (a * b) := by ring

end Erdos633b.GroupTwoDimensions
