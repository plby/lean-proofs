import ErdosProblems.Erdos1148.NoncentralPacketPairs
import ErdosProblems.Erdos1148.CoincidentFormPairs

/-! # The close-pair estimate for the entire discriminant packet -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups ENNReal

def modularClosePairs (η : ℝ) : Set (ModularOrbitSpace × ModularOrbitSpace) :=
  {z | ∃ g h : SL(2, ℝ), z = (modularMk g, modularMk h) ∧ EntryCloseOne η (g⁻¹ * h)}

lemma measurableSet_modularClosePairs (η : ℝ) : MeasurableSet (modularClosePairs η) := by
  let : SigmaCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SigmaCompactSpace (Fin 2 → Fin 2 → ℝ))
  let : SigmaCompactSpace SL(2, ℝ) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.sigmaCompactSpace
  have himage : modularClosePairs η =
      Prod.map modularMk modularMk ''
        {p : SL(2, ℝ) × SL(2, ℝ) | EntryCloseOne η (p.1⁻¹ * p.2)} := by
    ext z
    constructor
    · rintro ⟨g, h, hz, hclose⟩
      exact ⟨(g, h), hclose, hz.symm⟩
    · rintro ⟨⟨g, h⟩, hclose, rfl⟩
      exact ⟨g, h, rfl, hclose⟩
  rw [himage]
  exact measurableSet_image_of_isClosed_sigmaCompact
    (continuous_modularMk.prodMap continuous_modularMk)
    ((isClosed_entryCloseOne η).preimage (continuous_fst.inv.mul continuous_snd))

noncomputable def discriminantPacketCarrier {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d) :
    Set ModularOrbitSpace :=
  ⋃ q : IntegralFormOrbits d, (packetOrbit hd hns q).carrier

lemma measurableSet_discriminantPacketCarrier {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d) :
    MeasurableSet (discriminantPacketCarrier hd hns) :=
  MeasurableSet.iUnion (fun q => (packetOrbit hd hns q).measurableSet_carrier)

lemma ae_mem_discriminantPacketCarrier {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d) :
    ∀ᵐ x ∂discriminantPacket hd hns, x ∈ discriminantPacketCarrier hd hns := by
  rw [discriminantPacket, Measure.ae_sum_iff]
  intro q
  filter_upwards [(packetOrbit hd hns q).ae_mem_carrier] with x hx
  exact Set.mem_iUnion.mpr ⟨q, hx⟩

lemma ae_mem_discriminantPacketCarrier_prod {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d) :
    ∀ᵐ z ∂(discriminantPacket hd hns).prod (discriminantPacket hd hns),
      z ∈ discriminantPacketCarrier hd hns ×ˢ discriminantPacketCarrier hd hns := by
  have hm := measurableSet_discriminantPacketCarrier hd hns
  apply (Measure.ae_prod_mem_iff_ae_ae_mem (hm.prod hm)).mpr
  filter_upwards [ae_mem_discriminantPacketCarrier hd hns] with x hx
  filter_upwards [ae_mem_discriminantPacketCarrier hd hns] with y hy
  exact ⟨hx, hy⟩

theorem packet_closePairs_subset_split {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d) (η : ℝ) :
    (discriminantPacketCarrier hd hns ×ˢ discriminantPacketCarrier hd hns) ∩
        modularClosePairs η ⊆ coincidentFormClosePairs d η ∪ distinctFormClosePairs d η := by
  classical
  rintro z ⟨⟨hx, hy⟩, g, h, rfl, hclose⟩
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hy
  obtain ⟨t, _, ht⟩ := integral_form_of_mem_packet_carrier hd hns hp
  obtain ⟨u, _, hu⟩ := integral_form_of_mem_packet_carrier hd hns hq
  by_cases htu : t.1 = u.1
  · exact Or.inl ⟨t, g, h, rfl, ht, htu.symm ▸ hu, hclose⟩
  · exact Or.inr ⟨t, u, g, h, rfl, htu, ht, hu, hclose⟩

theorem packetProduct_close_le_split {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d) (η : ℝ) :
    (discriminantPacket hd hns).prod (discriminantPacket hd hns) (modularClosePairs η) ≤
      (discriminantPacket hd hns).prod (discriminantPacket hd hns)
        (coincidentFormClosePairs d η) +
      (discriminantPacket hd hns).prod (discriminantPacket hd hns)
        (distinctFormClosePairs d η) := by
  calc
    _ = (discriminantPacket hd hns).prod (discriminantPacket hd hns)
        ((discriminantPacketCarrier hd hns ×ˢ discriminantPacketCarrier hd hns) ∩
          modularClosePairs η) :=
      (Measure.measure_inter_eq_of_ae (ae_mem_discriminantPacketCarrier_prod hd hns)).symm
    _ ≤ (discriminantPacket hd hns).prod (discriminantPacket hd hns)
        (coincidentFormClosePairs d η ∪ distinctFormClosePairs d η) :=
      measure_mono (packet_closePairs_subset_split hd hns η)
    _ ≤ _ := measure_union_le _ _

theorem exists_packetProduct_close_le {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (d : ℕ) (hd : 0 < (d : ℤ)) (hns : ¬IsSquare (d : ℤ)) (η : ℝ),
      0 < η → η ≤ 1 / 2 →
      (discriminantPacket hd hns).prod (discriminantPacket hd hns) (modularClosePairs η) ≤
        ENNReal.ofReal (4 * η) * discriminantPacket hd hns Set.univ +
          ENNReal.ofReal (K * (d : ℝ) ^ (1 + ε) * η ^ 3) := by
  obtain ⟨K, hK, hbound⟩ := exists_packetProduct_distinctClose_le hε
  refine ⟨K, hK, ?_⟩
  intro d hd hns η hη0 hη
  exact (packetProduct_close_le_split hd hns η).trans
    (add_le_add (packetProduct_coincidentClose_le hd hns (by linarith))
      (hbound d hd hns η hη0 hη))

end Erdos1148.DukeArithmetic
