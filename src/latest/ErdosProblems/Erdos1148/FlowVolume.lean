import ErdosProblems.Erdos1148.FlowWindows

/-!
# Area of the close-flow parameter set

The linear change `(t,s) ↦ ((s-t)/2,(s+t)/2)` has determinant `-1/2`.
The logarithmic rectangle from `FlowWindows` therefore bounds the area
of close parameter pairs by `8*η*log(4*d)`.
-/

namespace Erdos1148.DukeArithmetic

open MeasureTheory

noncomputable def flowCoordinates : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  Matrix.toLin' !![-1 / 2, 1 / 2; 1 / 2, 1 / 2]

lemma flowCoordinates_apply (x : Fin 2 → ℝ) :
    flowCoordinates x = ![(x 1 - x 0) / 2, (x 1 + x 0) / 2] := by
  ext i
  fin_cases i <;> simp [flowCoordinates, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail] <;> ring

lemma det_flowCoordinates : LinearMap.det flowCoordinates = -1 / 2 := by
  norm_num [flowCoordinates, LinearMap.det_toLin', Matrix.det_fin_two]

noncomputable def flowWindowRectangle (α β γ η : ℝ) : Set (Fin 2 → ℝ) :=
  Set.Icc ![Real.log (1 - η) - Real.log α, Real.log |β| - Real.log η]
    ![Real.log (1 + η) - Real.log α, Real.log η - Real.log |γ|]

def closeFlowTimes (α β γ η : ℝ) : Set (Fin 2 → ℝ) :=
  {x | CloseFlowCoordinates α β γ η ((x 1 - x 0) / 2) ((x 1 + x 0) / 2)}

lemma closeFlowTimes_subset_rectangle {α β γ η : ℝ} (hη : η < 1)
    (hβ : β ≠ 0) (hγ : γ ≠ 0) :
    closeFlowTimes α β γ η ⊆ flowCoordinates ⁻¹' flowWindowRectangle α β γ η := by
  intro x hx
  obtain ⟨_, hvlo, hvhi⟩ := closeFlowCoordinates_diagonal_bounds hη hx
  obtain ⟨hwlo, hwhi⟩ := closeFlowCoordinates_offDiagonal_bounds hβ hγ hx
  rw [Set.mem_preimage, flowCoordinates_apply]
  constructor
  · intro i
    fin_cases i
    · exact hvlo
    · exact hwlo
  · intro i
    fin_cases i
    · exact hvhi
    · exact hwhi

lemma volume_flowWindowRectangle_le {α β γ η d : ℝ}
    (hd : 0 < d) (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (hprod : 1 / (4 * d) ≤ |β * γ|) :
    volume (flowWindowRectangle α β γ η) ≤
      ENNReal.ofReal (4 * η) * ENNReal.ofReal (Real.log (4 * d)) := by
  rw [flowWindowRectangle, Real.volume_Icc_pi, Fin.prod_univ_two]
  apply mul_le_mul'
  · apply ENNReal.ofReal_le_ofReal
    change (Real.log (1 + η) - Real.log α) -
      (Real.log (1 - η) - Real.log α) ≤ 4 * η
    have := diagonal_log_window_le hη0.le hη
    linarith
  · apply ENNReal.ofReal_le_ofReal
    exact offDiagonal_log_window_le hd hη0 (by linarith) hprod

lemma volume_flowCoordinates_preimage (s : Set (Fin 2 → ℝ)) :
    volume (flowCoordinates ⁻¹' s) = 2 * volume s := by
  have hdet : LinearMap.det flowCoordinates ≠ 0 := by rw [det_flowCoordinates]; norm_num
  rw [Measure.addHaar_preimage_linearMap volume hdet, det_flowCoordinates]
  norm_num

theorem volume_closeFlowTimes_le {α β γ η d : ℝ}
    (hd : 0 < d) (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (hprod : 1 / (4 * d) ≤ |β * γ|) :
    volume (closeFlowTimes α β γ η) ≤ ENNReal.ofReal (8 * η * Real.log (4 * d)) := by
  have hbg : β * γ ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by positivity) hprod)
  calc
    volume (closeFlowTimes α β γ η) ≤
        volume (flowCoordinates ⁻¹' flowWindowRectangle α β γ η) :=
      measure_mono (closeFlowTimes_subset_rectangle (by linarith)
        (left_ne_zero_of_mul hbg) (right_ne_zero_of_mul hbg))
    _ = 2 * volume (flowWindowRectangle α β γ η) := volume_flowCoordinates_preimage _
    _ ≤ 2 * (ENNReal.ofReal (4 * η) * ENNReal.ofReal (Real.log (4 * d))) :=
      mul_le_mul' le_rfl (volume_flowWindowRectangle_le hd hη0 hη hprod)
    _ = ENNReal.ofReal (8 * η * Real.log (4 * d)) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 8 * η)]
      have heq : ENNReal.ofReal (8 * η) = 2 * ENNReal.ofReal (4 * η) := by
        rw [show 8 * η = 2 * (4 * η) by ring, ENNReal.ofReal_mul (by norm_num)]
        norm_num
      rw [heq, mul_assoc]

end Erdos1148.DukeArithmetic
