import ErdosProblems.Erdos1148.NormalizedPairBound
import ErdosProblems.Erdos1148.UnconditionalPacketMass

/-! # Removing all unknown packet-volume factors from the close-pair estimate -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped ENNReal

lemma rpow_div_mul_rpow {x c : ℝ} (hx : 0 < x) (hc : c ≠ 0) (s t : ℝ) :
    x ^ s / (c * x ^ t) = c⁻¹ * x ^ (s - t) := by
  rw [Real.rpow_sub hx]
  ring

theorem exists_unconditional_normalizedPacketProduct_close_le {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (d : ℕ) (hd : 0 < (d : ℤ)) (hns : ¬IsSquare (d : ℤ)),
      IntegralDiscrForm d → ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
      (normalizedDiscriminantPacket hd hns).prod (normalizedDiscriminantPacket hd hns)
          (modularClosePairs η) ≤
        ENNReal.ofReal (K * ((d : ℝ) ^ (-1 / 2 + ε) * η + (d : ℝ) ^ ε * η ^ 3)) := by
  have he : 0 < ε / 3 := div_pos hε (by norm_num)
  obtain ⟨C, hC, hpair⟩ := exists_normalizedPacketProduct_close_le he
  obtain ⟨c, hc, hmass⟩ := exists_unconditional_packetMass_lower_bound he
  let K := 4 / c + C / c ^ 2
  have hK : 0 < K := add_pos (div_pos (by norm_num) hc) (div_pos hC (sq_pos_of_pos hc))
  refine ⟨K, hK, ?_⟩
  intro d hd hns base η hη hηsmall
  have hdN : 0 < d := by exact_mod_cast hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdN
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdN
  have hv := hmass d hd hns base
  simp only [Int.cast_natCast] at hv
  have hvR : 0 < c * (d : ℝ) ^ (1 / 2 - ε / 3) :=
    mul_pos hc (Real.rpow_pos_of_pos hdR _)
  have hbound := (hpair d hd hns base η hη hηsmall).trans
    (add_le_add (ENNReal.div_le_div_left hv _) (ENNReal.div_le_div_left (pow_le_pow_left' hv 2) _))
  rw [← ENNReal.ofReal_div_of_pos hvR, ← ENNReal.ofReal_pow hvR.le,
    ← ENNReal.ofReal_div_of_pos (sq_pos_of_pos hvR),
    ← ENNReal.ofReal_add (by positivity) (by positivity)] at hbound
  apply hbound.trans
  apply ENNReal.ofReal_le_ofReal
  have hfirst : 4 * η / (c * (d : ℝ) ^ (1 / 2 - ε / 3)) =
      (4 / c) * (d : ℝ) ^ (-1 / 2 + ε / 3) * η := by
    rw [div_eq_mul_inv, mul_inv_rev, ← Real.rpow_neg hdR.le]
    have hexp : -(1 / 2 - ε / 3) = -1 / 2 + ε / 3 := by ring
    rw [hexp]
    ring
  have hsecond : C * (d : ℝ) ^ (1 + ε / 3) * η ^ 3 /
      (c * (d : ℝ) ^ (1 / 2 - ε / 3)) ^ 2 = (C / c ^ 2) * (d : ℝ) ^ ε * η ^ 3 := by
    rw [mul_pow, ← Real.rpow_mul_natCast hdR.le]
    have hexp : (1 + ε / 3) - (1 / 2 - ε / 3) * (2 : ℕ) = ε := by norm_num; ring
    rw [show C * (d : ℝ) ^ (1 + ε / 3) * η ^ 3 /
        (c ^ 2 * (d : ℝ) ^ ((1 / 2 - ε / 3) * (2 : ℕ))) =
      (C * η ^ 3) * ((d : ℝ) ^ (1 + ε / 3) /
        (c ^ 2 * (d : ℝ) ^ ((1 / 2 - ε / 3) * (2 : ℕ)))) by ring,
      rpow_div_mul_rpow hdR (pow_ne_zero _ hc.ne'), hexp]
    ring
  rw [hfirst, hsecond]
  have hp := Real.rpow_le_rpow_of_exponent_le hd1
    (by linarith : -1 / 2 + ε / 3 ≤ -1 / 2 + ε)
  have hcoeff1 : 4 / c ≤ K := le_add_of_nonneg_right (by positivity)
  have hcoeff2 : C / c ^ 2 ≤ K := le_add_of_nonneg_left (by positivity)
  calc
    _ ≤ K * (d : ℝ) ^ (-1 / 2 + ε) * η + K * (d : ℝ) ^ ε * η ^ 3 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul hcoeff1 hp (Real.rpow_nonneg hdR.le _) hK.le) hη.le
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoeff2 (Real.rpow_nonneg hdR.le _)) (by positivity)
    _ = _ := by ring

end Erdos1148.DukeArithmetic
