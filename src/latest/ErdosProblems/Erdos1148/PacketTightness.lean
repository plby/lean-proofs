import ErdosProblems.Erdos1148.PacketVisitExceedanceDecay
import ErdosProblems.Erdos1148.VisitCountTailBound

/-! # Unconditional fixed-height nonescape for normalized discriminant packets -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Filter
open scoped Topology

theorem normalizedPacket_cusp_eventually_small {ι : Type*} {l : Filter ι} {d : ι → ℕ}
    (hd : ∀ i, 0 < (d i : ℤ)) (hns : ∀ i, ¬IsSquare (d i : ℤ))
    (base : ∀ i, IntegralDiscrForm (d i)) (hlim : Tendsto d l atTop)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ H : ℝ, 1 < H ∧ ∀ᶠ i in l,
      (normalizedDiscriminantPacket (hd i) (hns i)).real (modularCusp H) < δ := by
  let α := min (δ / 2) 1
  have hαpos : 0 < α := lt_min (half_pos hδ) zero_lt_one
  have hαone : α ≤ 1 := min_le_right _ _
  have hαδ : α ≤ δ / 2 := min_le_left _ _
  have hgap : 0 < δ - α := by linarith
  obtain ⟨H, hH, hdecay⟩ := normalizedPacket_cusp_visit_exceedance_tendsto_zero
    hd hns base hlim hαpos hαone
  refine ⟨H, hH, ?_⟩
  have hsmall := (hdecay H le_rfl).eventually (gt_mem_nhds hgap)
  have hdRlim : Tendsto (fun i => (d i : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hlim
  filter_upwards [hsmall, hdRlim.eventually (eventually_ge_atTop (Real.exp 2))] with i hi hdi
  let μ := normalizedDiscriminantPacket (hd i) (hns i)
  let : IsProbabilityMeasure μ := normalizedDiscriminantPacket_isProbability (hd i) (hns i) (base i)
  have hcount := invariant_cusp_mass_le_visit_exceedance μ
    (normalizedDiscriminantPacket_flow_invariant (hd i) (hns i)) H
    (packetObservationTime (d i : ℝ)) (packetObservationTime_pos hdi) hαpos.le
  exact hcount.trans_lt (by linarith [hi])

theorem normalizedPacket_eventually_tight {ι : Type*} {l : Filter ι} {d : ι → ℕ}
    (hd : ∀ i, 0 < (d i : ℤ)) (hns : ∀ i, ¬IsSquare (d i : ℤ))
    (base : ∀ i, IntegralDiscrForm (d i)) (hlim : Tendsto d l atTop)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : Set ModularOrbitSpace, IsCompact K ∧ ∀ᶠ i in l,
      (normalizedDiscriminantPacket (hd i) (hns i)).real Kᶜ < δ := by
  obtain ⟨H, hH, hsmall⟩ := normalizedPacket_cusp_eventually_small hd hns base hlim hδ
  refine ⟨modularCompactCore H, isCompact_modularCompactCore H, ?_⟩
  have hsub : (modularCompactCore H)ᶜ ⊆ modularCusp H := by
    intro x hx
    by_contra hnot
    exact hx (modularCusp_compl_subset_compactCore (by linarith : 0 < H) hnot)
  filter_upwards [hsmall] with i hi
  let μ := normalizedDiscriminantPacket (hd i) (hns i)
  let : IsProbabilityMeasure μ := normalizedDiscriminantPacket_isProbability (hd i) (hns i) (base i)
  exact (measureReal_mono (μ := μ) hsub).trans_lt hi

end Erdos1148.DukeArithmetic
