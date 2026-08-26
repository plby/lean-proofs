/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Polynomially fine sign grids on the dyadic spatial bins.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.AffineGrid
import ErdosProblems.Erdos521.ClampedDyadicGrid

namespace Erdos521

def fineGridLength (j : ℕ) : ℕ := j ^ 18

noncomputable def fineGridThreshold (j : ℕ) : ℝ := ((j : ℝ) ^ 24)⁻¹

noncomputable def fineGridRelativeWidth (j : ℕ) : ℝ := ((j : ℝ) ^ 18)⁻¹

noncomputable def dyadicFineGrid (j k : ℕ) : ℕ → ℝ :=
  affineGrid (dyadicPoint k) (dyadicPoint (k + 1)) (fineGridLength j)

theorem fineGridLength_pos {j : ℕ} (hj : 0 < j) : 0 < fineGridLength j := pow_pos hj 18

theorem fineGridThreshold_pos {j : ℕ} (hj : 0 < j) : 0 < fineGridThreshold j := by
  have hj₀ : (0 : ℝ) < j := by exact_mod_cast hj
  exact inv_pos.mpr (pow_pos hj₀ 24)

theorem fineGridRelativeWidth_pos {j : ℕ} (hj : 0 < j) : 0 < fineGridRelativeWidth j := by
  have hj₀ : (0 : ℝ) < j := by exact_mod_cast hj
  exact inv_pos.mpr (pow_pos hj₀ 18)

theorem dyadicFineGrid_zero (j k : ℕ) : dyadicFineGrid j k 0 = dyadicPoint k := affineGrid_zero _ _ _

theorem dyadicFineGrid_end {j : ℕ} (hj : 0 < j) (k : ℕ) :
    dyadicFineGrid j k (fineGridLength j) = dyadicPoint (k + 1) := affineGrid_end _ _ (fineGridLength_pos hj)

theorem dyadicFineGrid_mono (j k : ℕ) : Monotone (dyadicFineGrid j k) :=
  affineGrid_mono (dyadicPoint_mono (Nat.le_succ k)) _

theorem dyadicFineGrid_strictMono {j : ℕ} (hj : 0 < j) (k : ℕ) : StrictMono (dyadicFineGrid j k) := by
  have hwidth : 0 < dyadicPoint (k + 1) - dyadicPoint k := by
    rw [dyadicPoint_width]
    exact sub_pos.mpr (dyadicPoint_lt_one (k + 1))
  have hM : (0 : ℝ) < fineGridLength j := by exact_mod_cast fineGridLength_pos hj
  intro i l hil
  have h := div_lt_div_of_pos_right
    (mul_lt_mul_of_pos_left (show (i : ℝ) < l by exact_mod_cast hil) hwidth) hM
  unfold dyadicFineGrid affineGrid
  linarith

theorem dyadicFineGrid_pos (j k : ℕ) (hk : 0 < dyadicPoint k) (i : ℕ) : 0 < dyadicFineGrid j k i :=
  affineGrid_pos hk (dyadicPoint_mono (Nat.le_succ k)) _ _

theorem dyadicFineGrid_mem {j : ℕ} (hj : 0 < j) (k : ℕ) {i : ℕ} (hi : i ≤ fineGridLength j) :
    dyadicFineGrid j k i ∈ Set.Icc (dyadicPoint k) (dyadicPoint (k + 1)) :=
  affineGrid_mem (dyadicPoint_mono (Nat.le_succ k)) (fineGridLength_pos hj) hi

theorem dyadicFineGrid_relative_width {j : ℕ} (hj : 0 < j) (k : ℕ) {i : ℕ} (hi : i < fineGridLength j) :
    dyadicFineGrid j k (i + 1) - dyadicFineGrid j k i ≤
      fineGridRelativeWidth j * (1 - dyadicFineGrid j k (i + 1)) := by
  have h := affineGrid_relative_width (dyadicPoint_mono (Nat.le_succ k)) (dyadicPoint_width k).le
    (fineGridLength_pos hj) hi
  simpa only [dyadicFineGrid, fineGridLength, Nat.cast_pow, one_div, fineGridRelativeWidth] using h

theorem fineGrid_energy_balance {j : ℕ} (hj : 0 < j) :
    fineGridRelativeWidth j ^ 4 / fineGridThreshold j ^ 2 = fineGridThreshold j := by
  have hj₀ : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  unfold fineGridRelativeWidth fineGridThreshold
  field_simp

end Erdos521
