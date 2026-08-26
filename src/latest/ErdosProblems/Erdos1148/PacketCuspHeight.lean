import ErdosProblems.Erdos1148.PacketShortVectors

/-! # The cusp as a measurable set and the maximum height of a packet -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

lemma continuous_modularVectorLengthSq (u v : ℤ) : Continuous (fun g => modularVectorLengthSq g u v) := by
  unfold modularVectorLengthSq modularVector
  fun_prop

def modularCusp (H : ℝ) : Set ModularOrbitSpace :=
  ⋃ (u : ℤ) (v : ℤ) (_ : u ≠ 0 ∨ v ≠ 0),
    modularMk '' {g : SL(2, ℝ) | modularVectorLengthSq g u v < (H ^ 2)⁻¹}

lemma isOpen_modularCusp (H : ℝ) : IsOpen (modularCusp H) := by
  apply isOpen_iUnion
  intro u
  apply isOpen_iUnion
  intro v
  apply isOpen_iUnion
  intro huv
  exact (MulAction.isOpenQuotientMap_quotientMk (Γ := SL(2, ℤ))
    (T := SL(2, ℝ))).isOpenMap _ ((continuous_modularVectorLengthSq u v).isOpen_preimage _ isOpen_Iio)

lemma measurableSet_modularCusp (H : ℝ) : MeasurableSet (modularCusp H) :=
  (isOpen_modularCusp H).measurableSet

theorem packet_carrier_disjoint_cusp_of_scale {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    (q : IntegralFormOrbits d) {H : ℝ} (hscale : Real.sqrt (d : ℝ) * (H ^ 2)⁻¹ ≤ 2) :
    Disjoint (packetOrbit hd hns q).carrier (modularCusp H) := by
  apply Set.disjoint_left.mpr
  intro x hx hcusp
  simp only [modularCusp, Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq] at hcusp
  obtain ⟨u, v, huv, g, hg, hgx⟩ := hcusp
  have hρ : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  rw [← hgx] at hx
  have hlower := packet_vector_lengthSq_lower hd hns hx huv
  have hupper := mul_lt_mul_of_pos_left hg hρ
  exact (not_lt_of_ge hlower) (hupper.trans_le hscale)

theorem discriminantPacket_cusp_eq_zero_of_scale {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    {H : ℝ} (hscale : Real.sqrt (d : ℝ) * (H ^ 2)⁻¹ ≤ 2) :
    discriminantPacket hd hns (modularCusp H) = 0 := by
  rw [discriminantPacket, Measure.sum_apply _ (measurableSet_modularCusp H)]
  apply ENNReal.tsum_eq_zero.mpr
  intro q
  apply measure_mono_null _ (packetOrbit hd hns q).measure_compl_carrier
  intro x hx hc
  exact Set.disjoint_left.mp (packet_carrier_disjoint_cusp_of_scale hd hns q hscale) hc hx

theorem normalizedDiscriminantPacket_cusp_eq_zero_of_scale {d : ℤ}
    (hd : 0 < d) (hns : ¬IsSquare d) {H : ℝ}
    (hscale : Real.sqrt (d : ℝ) * (H ^ 2)⁻¹ ≤ 2) :
    normalizedDiscriminantPacket hd hns (modularCusp H) = 0 := by
  rw [normalizedDiscriminantPacket, Measure.smul_apply,
    discriminantPacket_cusp_eq_zero_of_scale hd hns hscale, smul_zero]

theorem normalizedDiscriminantPacket_cusp_fourth_root {d : ℤ}
    (hd : 0 < d) (hns : ¬IsSquare d) :
    normalizedDiscriminantPacket hd hns (modularCusp ((d : ℝ) ^ (1 / 4 : ℝ))) = 0 := by
  apply normalizedDiscriminantPacket_cusp_eq_zero_of_scale hd hns
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hdR.le]
  norm_num only [Nat.cast_ofNat, show (1 / 4 : ℝ) * 2 = 1 / 2 by norm_num]
  rw [mul_inv_cancel₀ (Real.rpow_pos_of_pos hdR _).ne']
  norm_num

end Erdos1148.DukeArithmetic
