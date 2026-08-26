import ErdosProblems.Erdos1148.PowerHeightBands
import ErdosProblems.Erdos1148.NaturalCuspScaleAlgebra

/-! # An unconditional upper bound for packet mass high in the cusp -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory

theorem exists_unconditional_normalizedPacket_cusp_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (hd : 0 < (d : ℤ)) (hns : ¬IsSquare (d : ℤ)),
      16 ≤ d → IntegralDiscrForm d → ∀ H : ℝ, 2 ≤ H →
        (normalizedDiscriminantPacket hd hns).real (modularCusp H) ^ 2 ≤
          C * ((d : ℝ) ^ (ε / 4) / H ^ 2 + (d : ℝ) ^ (-1 / 8 + ε / 4)) := by
  obtain ⟨K, hK, hpair⟩ := exists_naturalScale_normalizedPacketProduct_close_le hε
  let A : ℝ := 2 * (2 * Real.pi + 1)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨200 * A * K, by positivity, ?_⟩
  intro d hd hns hd16 base H hH
  let μ := normalizedDiscriminantPacket hd hns
  let : IsProbabilityMeasure μ := normalizedDiscriminantPacket_isProbability hd hns base
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  let η : ℝ := (d : ℝ) ^ (-(1 / 4 : ℝ))
  have hη : 0 < η := Real.rpow_pos_of_pos hdR _
  have hηhalf : η ≤ 1 / 2 := naturalPairScale_le_half hd16
  obtain ⟨J, hJmax, hJ⟩ := exists_power_height_band_count hd1
  have hmax : (d : ℝ) ^ (1 / 4 : ℝ) < (2 : ℝ) ^ J * H := by
    exact hJmax.trans_le (le_mul_of_one_le_right (by positivity) (by linarith))
  have hcap : μ (modularCusp ((d : ℝ) ^ (1 / 4 : ℝ))) = 0 := by
    simpa only [Int.cast_natCast] using normalizedDiscriminantPacket_cusp_fourth_root hd hns
  have hcover := cusp_mass_sq_le_pair_mass_of_height_cap μ hH
    (Real.rpow_pos_of_pos hdR (1 / 4)) (div_pos hη (by norm_num : (0 : ℝ) < 5))
    (show η / 5 ≤ 1 by linarith) hcap hmax
  have hpairReal : (μ.prod μ).real (modularClosePairs η) ≤ K * η ^ (3 - ε) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hpair d hd hns hd16 base)
    change (μ.prod μ).real (modularClosePairs η) ≤
      (ENNReal.ofReal (K * η ^ (3 - ε))).toReal at h
    rwa [ENNReal.toReal_ofReal (by positivity)] at h
  have hclose : 5 * (η / 5) = η := by ring
  rw [hclose] at hcover
  have hcoeff : 0 ≤ A * ((4 / 3) / ((η / 5) ^ 3 * H ^ 2) + J / (η / 5) ^ 2) := by
    positivity
  exact hcover.trans ((mul_le_mul_of_nonneg_left hpairReal hcoeff).trans
    (naturalCuspScale_coefficient_bound hdR (by linarith) hA.le hK.le ε hJ))

end Erdos1148.DukeArithmetic
