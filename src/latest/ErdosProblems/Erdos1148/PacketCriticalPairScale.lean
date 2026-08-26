import ErdosProblems.Erdos1148.LogarithmicObservationTime
import ErdosProblems.Erdos1148.ForwardPairTimeBound

/-! # An exponential pair bound at the logarithmic packet observation time -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Filter

theorem packetObservationTime_tendsto : Tendsto packetObservationTime atTop atTop := by
  exact tendsto_nat_floor_atTop.comp (Real.tendsto_log_atTop.atTop_div_const (by norm_num))

theorem packet_critical_pair_scale {D σ : ℝ} (hD : 1 ≤ D) (hσ : σ ≤ 1 / 2) :
    D ^ (-1 / 2 + σ) + D ^ σ * Real.exp (-(packetObservationTime D : ℝ)) ≤
      (1 + Real.exp 1) * Real.exp ((-1 + 2 * σ) * (packetObservationTime D : ℝ)) := by
  have hDpos : 0 < D := by linarith
  have hterm : D ^ σ * Real.exp (-(packetObservationTime D : ℝ)) ≤
      Real.exp 1 * D ^ (-1 / 2 + σ) := by
    calc
      _ ≤ D ^ σ * (Real.exp 1 * D ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (exp_neg_packetObservationTime_le hD) (Real.rpow_nonneg hDpos.le σ)
      _ = Real.exp 1 * (D ^ σ * D ^ (-(1 / 2 : ℝ))) := by ring
      _ = Real.exp 1 * D ^ (σ + -(1 / 2 : ℝ)) := by rw [← Real.rpow_add hDpos]
      _ = _ := by congr 1; congr 1; ring
  have hpow : D ^ (-1 / 2 + σ) ≤
      Real.exp ((-1 + 2 * σ) * (packetObservationTime D : ℝ)) := by
    rw [Real.rpow_def_of_pos hDpos]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonpos_right (packetObservationTime_le hD)
      (show -1 / 2 + σ ≤ 0 by linarith)
    nlinarith
  calc
    _ ≤ (1 + Real.exp 1) * D ^ (-1 / 2 + σ) := by nlinarith [hterm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

theorem exists_unconditional_packet_critical_forward_pair_bound {σ : ℝ}
    (hσpos : 0 < σ) (hσ : σ ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (hd : 0 < (d : ℤ)) (hns : ¬IsSquare (d : ℤ)),
      IntegralDiscrForm d → ∀ r : ℝ, 0 < r → r ≤ 1 / 6 →
        ((normalizedDiscriminantPacket hd hns).prod
          (normalizedDiscriminantPacket hd hns)).real
            (modularForwardBowenPairs r (packetObservationTime (d : ℝ) : ℝ)) ≤
          C * Real.exp ((-1 + 2 * σ) * (packetObservationTime (d : ℝ) : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_unconditional_forwardPairs_time_bound hσpos
  refine ⟨C * (1 + Real.exp 1), by positivity, ?_⟩
  intro d hd hns base r hr hrlim
  have hD : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hpair := hbound d hd hns base r
    (packetObservationTime (d : ℝ)) (packetObservationTime (d : ℝ)) hr hrlim
    (Nat.cast_nonneg _) le_rfl
  have hscale := mul_le_mul_of_nonneg_left (packet_critical_pair_scale hD hσ) hC.le
  exact hpair.trans (by simpa only [mul_assoc] using hscale)

end Erdos1148.DukeArithmetic
