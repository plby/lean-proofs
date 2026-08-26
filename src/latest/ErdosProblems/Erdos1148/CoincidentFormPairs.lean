import ErdosProblems.Erdos1148.PacketPairMeasure
import ErdosProblems.Erdos1148.ShortOrbitPairs

/-! # The linear close-pair contribution from coincident integral forms -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups ENNReal

lemma abs_le_of_entryCloseOne_diagonalFlow {η t : ℝ}
    (h : EntryCloseOne η (diagonalFlow t)) : |t| ≤ 2 * η := by
  have h₀ := (abs_le.mp h.1).2
  have h₁ := (abs_le.mp h.2.2.2).2
  change Real.exp (t / 2) - 1 ≤ η at h₀
  change Real.exp (-(t / 2)) - 1 ≤ η at h₁
  apply abs_le.mpr
  constructor
  · linarith [Real.add_one_le_exp (-(t / 2))]
  · linarith [Real.add_one_le_exp (t / 2)]

lemma not_entryCloseOne_neg_diagonalFlow {η : ℝ} (hη : η < 1) (t : ℝ) :
    ¬EntryCloseOne η (-diagonalFlow t) := by
  intro h
  have h₀ := (abs_le.mp h.1).1
  change -η ≤ -Real.exp (t / 2) - 1 at h₀
  linarith [Real.exp_pos (t / 2)]

theorem exists_short_flow_of_equal_form {g h : SL(2, ℝ)} {η : ℝ} (hη : η < 1)
    (heq : formAction g (splitForm ℝ) = formAction h (splitForm ℝ))
    (hclose : EntryCloseOne η (g⁻¹ * h)) :
    ∃ s : ℝ, |s| ≤ 2 * η ∧ h = g * diagonalFlow s := by
  obtain ⟨s, hs | hs⟩ := exists_signed_flow_of_formAction_eq heq
  · rw [hs, inv_mul_cancel_left] at hclose
    exact ⟨s, abs_le_of_entryCloseOne_diagonalFlow hclose, hs⟩
  · rw [hs, mul_neg, inv_mul_cancel_left] at hclose
    exact (not_entryCloseOne_neg_diagonalFlow hη s hclose).elim

def coincidentFormClosePairs (d : ℤ) (η : ℝ) : Set (ModularOrbitSpace × ModularOrbitSpace) :=
  {z | ∃ (t : IntegralDiscrForm d) (g h : SL(2, ℝ)),
    z = (modularMk g, modularMk h) ∧
    Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t.1 ∧
    Real.sqrt (d : ℝ) • formAction h (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t.1 ∧
    EntryCloseOne η (g⁻¹ * h)}

theorem coincidentFormClosePairs_subset_shortPairs {d : ℤ} (hd : 0 < d)
    (hns : ¬IsSquare d) {η : ℝ} (hη : η < 1) :
    coincidentFormClosePairs d η ⊆
      ⋃ q : IntegralFormOrbits d, (packetOrbit hd hns q).shortPairs (2 * η) := by
  rintro z ⟨t, g, h, rfl, hg, hh, hclose⟩
  have hρ : Real.sqrt (d : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  obtain ⟨s, hs, rfl⟩ := exists_short_flow_of_equal_form hη
    (formAction_eq_of_scaled_eq hρ (hg.trans hh.symm)) hclose
  apply Set.mem_iUnion.mpr
  refine ⟨integralFormOrbitMk t, ?_⟩
  exact (packetOrbit hd hns (integralFormOrbitMk t)).mem_shortPairs_of_flow
    (mem_packet_carrier_of_integral_form hd hns t rfl hg) hs

theorem packetProduct_coincidentClose_le {d : ℤ} (hd : 0 < d)
    (hns : ¬IsSquare d) {η : ℝ} (hη : η < 1) :
    (discriminantPacket hd hns).prod (discriminantPacket hd hns)
        (coincidentFormClosePairs d η) ≤
      ENNReal.ofReal (4 * η) * discriminantPacket hd hns Set.univ := by
  calc
    _ ≤ (discriminantPacket hd hns).prod (discriminantPacket hd hns)
        (⋃ q : IntegralFormOrbits d, (packetOrbit hd hns q).shortPairs (2 * η)) :=
      measure_mono (coincidentFormClosePairs_subset_shortPairs hd hns hη)
    _ ≤ ∑' q : IntegralFormOrbits d, (discriminantPacket hd hns).prod
        (discriminantPacket hd hns) ((packetOrbit hd hns q).shortPairs (2 * η)) :=
      measure_iUnion_le _
    _ ≤ ∑' q : IntegralFormOrbits d,
        ENNReal.ofReal (4 * η) * ENNReal.ofReal (packetOrbit hd hns q).period := by
      apply ENNReal.tsum_le_tsum
      intro q
      rw [packetProduct_apply_of_subset_carriers hd hns q q
        ((packetOrbit hd hns q).shortPairs_subset_carriers (2 * η))]
      simpa only [show 2 * (2 * η) = 4 * η by ring] using
        (packetOrbit hd hns q).measure_shortPairs_le (2 * η)
    _ = _ := by rw [discriminantPacket_univ, ENNReal.tsum_mul_left]

end Erdos1148.DukeArithmetic
