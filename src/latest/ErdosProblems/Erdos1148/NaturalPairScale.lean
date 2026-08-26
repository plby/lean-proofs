import ErdosProblems.Erdos1148.UnconditionalPairBound

/-! # The close-pair estimate at the natural scale d^(-1/4) -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory

lemma naturalPairScale_le_half {d : ℕ} (hd : 16 ≤ d) : (d : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 1 / 2 := by
  have hdR : (16 : ℝ) ≤ d := by exact_mod_cast hd
  calc
    _ ≤ (16 : ℝ) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hdR (by norm_num)
    _ = _ := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num,
        ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num

theorem exists_naturalScale_normalizedPacketProduct_close_le {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (d : ℕ) (hd : 0 < (d : ℤ)) (hns : ¬IsSquare (d : ℤ)),
      16 ≤ d → IntegralDiscrForm d →
      (normalizedDiscriminantPacket hd hns).prod (normalizedDiscriminantPacket hd hns)
          (modularClosePairs ((d : ℝ) ^ (-(1 / 4 : ℝ)))) ≤
        ENNReal.ofReal (K * ((d : ℝ) ^ (-(1 / 4 : ℝ))) ^ (3 - ε)) := by
  obtain ⟨C, hC, hbound⟩ := exists_unconditional_normalizedPacketProduct_close_le
    (div_pos hε (by norm_num : (0 : ℝ) < 4))
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro d hd hns hd16 base
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h := hbound d hd hns base ((d : ℝ) ^ (-(1 / 4 : ℝ)))
    (Real.rpow_pos_of_pos hdR _) (naturalPairScale_le_half hd16)
  have hpow1 : (d : ℝ) ^ (-1 / 2 + ε / 4) * (d : ℝ) ^ (-(1 / 4 : ℝ)) =
      (d : ℝ) ^ (-3 / 4 + ε / 4) := by
    rw [← Real.rpow_add hdR]
    congr 1
    ring
  have hpow2 : (d : ℝ) ^ (ε / 4) * ((d : ℝ) ^ (-(1 / 4 : ℝ))) ^ 3 =
      (d : ℝ) ^ (-3 / 4 + ε / 4) := by
    rw [← Real.rpow_mul_natCast hdR.le, ← Real.rpow_add hdR]
    congr 1
    norm_num
    ring
  have hpow3 : ((d : ℝ) ^ (-(1 / 4 : ℝ))) ^ (3 - ε) =
      (d : ℝ) ^ (-3 / 4 + ε / 4) := by
    rw [← Real.rpow_mul hdR.le]
    congr 1
    ring
  rw [hpow1, hpow2] at h
  rw [hpow3]
  convert h using 2 <;> ring

end Erdos1148.DukeArithmetic
