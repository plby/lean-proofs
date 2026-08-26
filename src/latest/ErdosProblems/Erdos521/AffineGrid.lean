/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite affine subdivisions with an explicit relative cell-width bound.
Formal proof: Codex.
-/
import Mathlib

namespace Erdos521

noncomputable def affineGrid (a b : ℝ) (M i : ℕ) : ℝ := a + (b - a) * (i : ℝ) / M

theorem affineGrid_zero (a b : ℝ) (M : ℕ) : affineGrid a b M 0 = a := by simp [affineGrid]

theorem affineGrid_end (a b : ℝ) {M : ℕ} (hM : 0 < M) : affineGrid a b M M = b := by
  have hM₀ : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [affineGrid, mul_div_cancel_right₀ _ hM₀]
  ring

theorem affineGrid_mono {a b : ℝ} (hab : a ≤ b) (M : ℕ) : Monotone (affineGrid a b M) := by
  intro i k hik
  unfold affineGrid
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hik) (sub_nonneg.mpr hab)

theorem affineGrid_mem {a b : ℝ} (hab : a ≤ b) {M i : ℕ} (hM : 0 < M) (hi : i ≤ M) :
    affineGrid a b M i ∈ Set.Icc a b := by
  constructor
  · calc
      a = affineGrid a b M 0 := (affineGrid_zero _ _ _).symm
      _ ≤ _ := affineGrid_mono hab M (Nat.zero_le i)
  · calc
      _ ≤ affineGrid a b M M := affineGrid_mono hab M hi
      _ = b := affineGrid_end _ _ hM

theorem affineGrid_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (M i : ℕ) :
    0 < affineGrid a b M i := by
  have h : 0 ≤ (b - a) * (i : ℝ) / M := by positivity
  unfold affineGrid
  linarith

theorem affineGrid_width (a b : ℝ) (M i : ℕ) :
    affineGrid a b M (i + 1) - affineGrid a b M i = (b - a) / M := by
  unfold affineGrid
  push_cast
  ring

theorem affineGrid_relative_width {a b : ℝ} (hab : a ≤ b) (hwidth : b - a ≤ 1 - b)
    {M i : ℕ} (hM : 0 < M) (hi : i < M) :
    affineGrid a b M (i + 1) - affineGrid a b M i ≤
      (1 / (M : ℝ)) * (1 - affineGrid a b M (i + 1)) := by
  have hupper := (affineGrid_mem hab hM (show i + 1 ≤ M by omega)).2
  rw [affineGrid_width]
  calc
    (b - a) / (M : ℝ) ≤ (1 - b) / M := div_le_div_of_nonneg_right hwidth (Nat.cast_nonneg M)
    _ ≤ (1 - affineGrid a b M (i + 1)) / M :=
      div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg M)
    _ = _ := by ring

end Erdos521
