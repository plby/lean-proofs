import ErdosProblems.Erdos1148.LogarithmicObservationTime

/-! # The refined global mass bound decays at a logarithmic observation scale -/

namespace Erdos1148.DukeArithmetic

theorem refined_global_mass_scale_bound {D α ε σ β : ℝ}
    (hD : 1 ≤ D) (hα : α ≤ 1) (hε : 0 ≤ ε) (hβ : 0 ≤ β) :
    (D ^ β + 1) ^ 11 *
      Real.exp ((1 + ε) * (packetObservationTime D : ℝ) -
        (α * (packetObservationTime D : ℝ)) / 2) *
      (D ^ (-1 / 2 + σ) + D ^ σ * Real.exp (-(packetObservationTime D : ℝ))) ≤
      (2 ^ 11 * (1 + Real.exp 1)) * D ^ (11 * β + ε / 2 - α / 4 + σ) := by
  have hDpos : 0 < D := by linarith
  have hexp : Real.exp ((1 + ε) * (packetObservationTime D : ℝ) -
      (α * (packetObservationTime D : ℝ)) / 2) ≤ D ^ ((1 + ε - α / 2) / 2) := by
    have heq : (1 + ε) * (packetObservationTime D : ℝ) -
        (α * (packetObservationTime D : ℝ)) / 2 =
        (1 + ε - α / 2) * (packetObservationTime D : ℝ) := by ring
    rw [heq]
    exact exp_mul_packetObservationTime_le hD (by linarith)
  have hterm : D ^ σ * Real.exp (-(packetObservationTime D : ℝ)) ≤
      Real.exp 1 * D ^ (-1 / 2 + σ) := by
    calc
      _ ≤ D ^ σ * (Real.exp 1 * D ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (exp_neg_packetObservationTime_le hD) (Real.rpow_nonneg hDpos.le σ)
      _ = Real.exp 1 * (D ^ σ * D ^ (-(1 / 2 : ℝ))) := by ring
      _ = Real.exp 1 * D ^ (σ + -(1 / 2 : ℝ)) := by rw [← Real.rpow_add hDpos]
      _ = _ := by congr 1; congr 1; ring
  have hpair : D ^ (-1 / 2 + σ) + D ^ σ * Real.exp (-(packetObservationTime D : ℝ)) ≤
      (1 + Real.exp 1) * D ^ (-1 / 2 + σ) := by
    calc
      _ ≤ D ^ (-1 / 2 + σ) + Real.exp 1 * D ^ (-1 / 2 + σ) := add_le_add le_rfl hterm
      _ = _ := by ring
  have hfirst := mul_le_mul (power_height_eleven_bound hD hβ) hexp (Real.exp_pos _).le (by positivity)
  calc
    _ ≤ (2 ^ 11 * D ^ (11 * β) * D ^ ((1 + ε - α / 2) / 2)) *
        ((1 + Real.exp 1) * D ^ (-1 / 2 + σ)) :=
      mul_le_mul hfirst hpair (by positivity) (by positivity)
    _ = (2 ^ 11 * (1 + Real.exp 1)) *
        ((D ^ (11 * β) * D ^ ((1 + ε - α / 2) / 2)) * D ^ (-1 / 2 + σ)) := by ring
    _ = (2 ^ 11 * (1 + Real.exp 1)) *
        D ^ ((11 * β + (1 + ε - α / 2) / 2) + (-1 / 2 + σ)) := by
      rw [← Real.rpow_add hDpos, ← Real.rpow_add hDpos]
    _ = _ := by congr 1; congr 1; ring

theorem refined_global_mass_scale_decay {D α : ℝ} (hD : 1 ≤ D) (hαpos : 0 < α) (hα : α ≤ 1) :
    (D ^ (α / 176) + 1) ^ 11 *
      Real.exp ((1 + α / 8) * (packetObservationTime D : ℝ) -
        (α * (packetObservationTime D : ℝ)) / 2) *
      (D ^ (-1 / 2 + α / 16) + D ^ (α / 16) * Real.exp (-(packetObservationTime D : ℝ))) ≤
      (2 ^ 11 * (1 + Real.exp 1)) * D ^ (-α / 16) := by
  have h := refined_global_mass_scale_bound (α := α) (ε := α / 8) (σ := α / 16) (β := α / 176)
    hD hα (by positivity) (by positivity)
  have heq : 11 * (α / 176) + (α / 8) / 2 - α / 4 + α / 16 = -α / 16 := by ring
  simpa only [heq] using h

end Erdos1148.DukeArithmetic
