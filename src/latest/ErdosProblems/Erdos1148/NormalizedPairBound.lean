import ErdosProblems.Erdos1148.PacketClosePairs

/-! # The normalized packet close-pair estimate with its exact volume dependence -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped ENNReal

lemma normalize_pair_bound {V : ℝ≥0∞} (hV0 : V ≠ 0) (hVtop : V ≠ ∞) (a b : ℝ≥0∞) :
    V⁻¹ * (V⁻¹ * (a * V + b)) = a / V + b / V ^ 2 := by
  rw [mul_add, mul_add]
  congr 1
  · calc
      V⁻¹ * (V⁻¹ * (a * V)) = (a * V⁻¹) * (V⁻¹ * V) := by ac_rfl
      _ = a / V := by rw [ENNReal.inv_mul_cancel hV0 hVtop, mul_one, div_eq_mul_inv]
  · rw [div_eq_mul_inv, ENNReal.inv_pow, pow_two]
    ac_rfl

lemma normalizedPacketProduct_apply {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    (E : Set (ModularOrbitSpace × ModularOrbitSpace)) :
    (normalizedDiscriminantPacket hd hns).prod (normalizedDiscriminantPacket hd hns) E =
      (discriminantPacket hd hns Set.univ)⁻¹ * ((discriminantPacket hd hns Set.univ)⁻¹ *
        (discriminantPacket hd hns).prod (discriminantPacket hd hns) E) := by
  simp only [normalizedDiscriminantPacket, Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.smul_apply, smul_eq_mul]

theorem exists_normalizedPacketProduct_close_le {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (d : ℕ) (hd : 0 < (d : ℤ)) (hns : ¬IsSquare (d : ℤ)),
      IntegralDiscrForm d → ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
      (normalizedDiscriminantPacket hd hns).prod (normalizedDiscriminantPacket hd hns)
          (modularClosePairs η) ≤
        ENNReal.ofReal (4 * η) / discriminantPacket hd hns Set.univ +
          ENNReal.ofReal (K * (d : ℝ) ^ (1 + ε) * η ^ 3) /
            (discriminantPacket hd hns Set.univ) ^ 2 := by
  obtain ⟨K, hK, hbound⟩ := exists_packetProduct_close_le hε
  refine ⟨K, hK, ?_⟩
  intro d hd hns base η hη0 hη
  rw [normalizedPacketProduct_apply]
  have hV0 := (discriminantPacket_univ_pos hd hns base).ne'
  have hVtop : discriminantPacket hd hns Set.univ ≠ ∞ := measure_ne_top _ _
  rw [← normalize_pair_bound hV0 hVtop]
  exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (hbound d hd hns η hη0 hη))

end Erdos1148.DukeArithmetic
