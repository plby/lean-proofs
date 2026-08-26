/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Truncating a dyadic interval at a bulk boundary preserves its relative width.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.DyadicIntervals

namespace Erdos521

theorem dyadicPoint_width (k : ℕ) : dyadicPoint (k + 1) - dyadicPoint k = 1 - dyadicPoint (k + 1) := by
  unfold dyadicPoint
  rw [pow_succ]
  field_simp
  ring

theorem relative_width_min {u v b : ℝ} (huv : u ≤ v) (hwidth : v - u ≤ 1 - v) (hb : b ≤ 1) :
    min v b - min u b ≤ 1 - min v b := by
  rcases le_total u b with hu | hu <;> rcases le_total v b with hv | hv
  · rw [min_eq_left hu, min_eq_left hv]
    exact hwidth
  · rw [min_eq_left hu, min_eq_right hv]
    linarith
  · rw [min_eq_right hu, min_eq_left hv]
    linarith
  · rw [min_eq_right hu, min_eq_right hv]
    linarith

theorem clamped_dyadic_width (k : ℕ) {b : ℝ} (hb : b ≤ 1) :
    min (dyadicPoint (k + 1)) b - min (dyadicPoint k) b ≤ 1 - min (dyadicPoint (k + 1)) b :=
  relative_width_min (dyadicPoint_mono (Nat.le_succ k)) (dyadicPoint_width k).le hb

end Erdos521
