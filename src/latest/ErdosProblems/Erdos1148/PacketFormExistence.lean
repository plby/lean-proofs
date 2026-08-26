import ErdosProblems.Erdos1148.PacketOpenExistence
import ErdosProblems.Erdos1148.LocalRepresentation

/-! # From positive packet mass to integral forms in a prescribed real open set -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

lemma continuous_formAction_splitForm :
    Continuous (fun g : SL(2, ℝ) => formAction g (splitForm ℝ)) := by
  unfold formAction transform
  fun_prop

lemma ae_mem_normalizedDiscriminantPacketCarrier {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d) :
    ∀ᵐ x ∂normalizedDiscriminantPacket hd hns, x ∈ discriminantPacketCarrier hd hns :=
  Measure.ae_smul_measure (ae_mem_discriminantPacketCarrier hd hns) _

theorem integral_form_of_positive_packet_image {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    {V : Set SL(2, ℝ)} (hpos : 0 < normalizedDiscriminantPacket hd hns (modularMk '' V)) :
    ∃ (g : SL(2, ℝ)) (t : IntegralDiscrForm d), g ∈ V ∧
      Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t.1 := by
  have hinter := Measure.measure_inter_eq_of_ae (ae_mem_normalizedDiscriminantPacketCarrier hd hns)
    (s := modularMk '' V)
  have hne : (discriminantPacketCarrier hd hns ∩ (modularMk '' V)).Nonempty := by
    apply MeasureTheory.nonempty_of_measure_ne_zero
    rw [hinter]
    exact hpos.ne'
  obtain ⟨x, hcarrier, g, hg, rfl⟩ := hne
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hcarrier
  obtain ⟨t, _, ht⟩ := integral_form_of_mem_packet_carrier hd hns hq
  exact ⟨g, t, hg, ht⟩

theorem eventually_integral_form_in_open {W : Set (ℝ × ℝ × ℝ)}
    (hW : IsOpen W) (hne : ∃ t ∈ W, discr t = 1) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → ∀ (hd : 0 < (d : ℤ)) (hns : ¬IsSquare (d : ℤ))
      (_base : IntegralDiscrForm (d : ℤ)), ∃ (g : SL(2, ℝ)) (t : IntegralDiscrForm (d : ℤ)),
        formAction g (splitForm ℝ) ∈ W ∧
        Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t.1 := by
  let V := (fun g : SL(2, ℝ) => formAction g (splitForm ℝ)) ⁻¹' W
  have hV : IsOpen V := hW.preimage continuous_formAction_splitForm
  have hVne : V.Nonempty := by
    obtain ⟨t, htW, ht⟩ := hne
    obtain ⟨g, hg⟩ := exists_formAction_splitForm (by norm_num : (1 : ℝ) ≠ 0)
      (by simpa only [one_pow] using ht)
    simp only [one_smul] at hg
    exact ⟨g, by change formAction g (splitForm ℝ) ∈ W; rwa [hg]⟩
  have hq : IsOpenQuotientMap modularMk := MulAction.isOpenQuotientMap_quotientMk
  obtain ⟨D, hD⟩ := normalizedPacket_eventually_open_pos (hq.isOpenMap V hV) (hVne.image modularMk)
  refine ⟨D, ?_⟩
  intro d hdD hd hns base
  obtain ⟨g, t, hg, ht⟩ := integral_form_of_positive_packet_image hd hns (hD d hdD hd hns base)
  exact ⟨g, t, hg, by simpa only [Int.cast_natCast] using ht⟩

end Erdos1148.DukeArithmetic
