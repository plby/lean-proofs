import Mathlib

/-!
# Logarithmic windows for two close diagonal-flow trajectories

In coordinates `v = (s-t)/2` and `w = (s+t)/2`, three entries of the
relative matrix are `α*exp(v)`, `β*exp(-w)`, and `γ*exp(w)`.
Closeness to the identity confines `(v,w)` to an explicit rectangle.
-/

namespace Erdos1148.DukeArithmetic

def CloseFlowCoordinates (α β γ η v w : ℝ) : Prop :=
  |α * Real.exp v - 1| ≤ η ∧
    |β * Real.exp (-w)| ≤ η ∧ |γ * Real.exp w| ≤ η

lemma closeFlowCoordinates_diagonal_bounds {α β γ η v w : ℝ}
    (hη : η < 1) (h : CloseFlowCoordinates α β γ η v w) :
    0 < α ∧ Real.log (1 - η) - Real.log α ≤ v ∧
      v ≤ Real.log (1 + η) - Real.log α := by
  have habs := abs_le.mp h.1
  have hlo : 1 - η ≤ α * Real.exp v := by linarith
  have hhi : α * Real.exp v ≤ 1 + η := by linarith
  have hη0 : 0 ≤ η := (abs_nonneg _).trans h.1
  have hprod : 0 < α * Real.exp v := lt_of_lt_of_le (by linarith) hlo
  have hα : 0 < α := (mul_pos_iff_of_pos_right (Real.exp_pos v)).mp hprod
  have hloglo := Real.log_le_log (by linarith : 0 < 1 - η) hlo
  have hloghi := Real.log_le_log hprod hhi
  rw [Real.log_mul hα.ne' (Real.exp_ne_zero _), Real.log_exp] at hloglo hloghi
  exact ⟨hα, by linarith, by linarith⟩

lemma closeFlowCoordinates_offDiagonal_bounds {α β γ η v w : ℝ}
    (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (h : CloseFlowCoordinates α β γ η v w) :
    Real.log |β| - Real.log η ≤ w ∧ w ≤ Real.log η - Real.log |γ| := by
  have hb := h.2.1
  have hg := h.2.2
  rw [abs_mul, abs_of_pos (Real.exp_pos _)] at hb hg
  have hlogb := Real.log_le_log
    (mul_pos (abs_pos.mpr hβ) (Real.exp_pos _)) hb
  have hlogg := Real.log_le_log
    (mul_pos (abs_pos.mpr hγ) (Real.exp_pos _)) hg
  rw [Real.log_mul (abs_ne_zero.mpr hβ) (Real.exp_ne_zero _), Real.log_exp] at hlogb
  rw [Real.log_mul (abs_ne_zero.mpr hγ) (Real.exp_ne_zero _), Real.log_exp] at hlogg
  exact ⟨by linarith, by linarith⟩

lemma diagonal_log_window_le {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) :
    Real.log (1 + η) - Real.log (1 - η) ≤ 4 * η := by
  have hlo : 0 < 1 - η := by linarith
  have hhi : 0 < 1 + η := by linarith
  rw [← Real.log_div hhi.ne' hlo.ne']
  refine (Real.log_le_sub_one_of_pos (div_pos hhi hlo)).trans ?_
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ hlo).mpr
  nlinarith

lemma offDiagonal_log_window_le {β γ η d : ℝ}
    (hd : 0 < d) (hη0 : 0 < η) (hη : η ≤ 1)
    (hprod : 1 / (4 * d) ≤ |β * γ|) :
    (Real.log η - Real.log |γ|) - (Real.log |β| - Real.log η) ≤
      Real.log (4 * d) := by
  have hd4 : 0 < 4 * d := by positivity
  have hbg : 0 < |β * γ| := lt_of_lt_of_le (by positivity) hprod
  have hβ : β ≠ 0 := left_ne_zero_of_mul (abs_pos.mp hbg)
  have hγ : γ ≠ 0 := right_ne_zero_of_mul (abs_pos.mp hbg)
  have hlog := Real.log_le_log (by positivity : 0 < 1 / (4 * d)) hprod
  rw [Real.log_div one_ne_zero hd4.ne', Real.log_one, zero_sub,
    abs_mul, Real.log_mul (abs_ne_zero.mpr hβ) (abs_ne_zero.mpr hγ)] at hlog
  have hlogη : Real.log η ≤ 0 := Real.log_nonpos hη0.le hη
  linarith

lemma closeFlowCoordinates_time_difference_le {α β γ η d v w v' w' : ℝ}
    (hd : 0 < d) (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (hprod : 1 / (4 * d) ≤ |β * γ|)
    (h : CloseFlowCoordinates α β γ η v w)
    (h' : CloseFlowCoordinates α β γ η v' w') :
    |(w - v) - (w' - v')| ≤ Real.log (4 * d) + 4 * η := by
  have hbg : β * γ ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by positivity) hprod)
  obtain ⟨hα, hvlo, hvhi⟩ := closeFlowCoordinates_diagonal_bounds (by linarith) h
  obtain ⟨_, hvlo', hvhi'⟩ := closeFlowCoordinates_diagonal_bounds (by linarith) h'
  obtain ⟨hwlo, hwhi⟩ := closeFlowCoordinates_offDiagonal_bounds
    (left_ne_zero_of_mul hbg) (right_ne_zero_of_mul hbg) h
  obtain ⟨hwlo', hwhi'⟩ := closeFlowCoordinates_offDiagonal_bounds
    (left_ne_zero_of_mul hbg) (right_ne_zero_of_mul hbg) h'
  have hvwidth := diagonal_log_window_le hη0.le hη
  have hwwidth := offDiagonal_log_window_le hd hη0 (by linarith) hprod
  apply abs_le.mpr
  constructor <;> linarith

end Erdos1148.DukeArithmetic
