import ErdosProblems.Erdos1148.ClosedOrbitCarrier

/-! # Short flow displacements on a closed orbit -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups ENNReal

def circleClosePairs (T r : ℝ) : Set (AddCircle T × AddCircle T) :=
  {z | dist z.1 z.2 ≤ r}

lemma isClosed_circleClosePairs (T r : ℝ) : IsClosed (circleClosePairs T r) :=
  isClosed_le (continuous_fst.dist continuous_snd) continuous_const

lemma volume_circleClosePairs_le (T r : ℝ) [Fact (0 < T)] :
    (volume : Measure (AddCircle T)).prod volume (circleClosePairs T r) ≤
      ENNReal.ofReal (2 * r) * ENNReal.ofReal T := by
  rw [Measure.prod_apply (isClosed_circleClosePairs T r).measurableSet]
  have hslice (x : AddCircle T) :
      Prod.mk x ⁻¹' circleClosePairs T r = Metric.closedBall x r := by
    ext y
    simp only [Set.mem_preimage, circleClosePairs, Set.mem_ofPred_eq, Metric.mem_closedBall,
      dist_comm x y]
  simp_rw [hslice, AddCircle.volume_closedBall]
  rw [lintegral_const, AddCircle.measure_univ]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (min_le_right _ _)) le_rfl

noncomputable def ClosedFlowOrbit.shortPairs (o : ClosedFlowOrbit) (r : ℝ) :
    Set (ModularOrbitSpace × ModularOrbitSpace) :=
  Prod.map (closedOrbitCurve o.period_mem) (closedOrbitCurve o.period_mem) ''
    circleClosePairs o.period r

lemma ClosedFlowOrbit.isCompact_shortPairs (o : ClosedFlowOrbit) (r : ℝ) :
    IsCompact (o.shortPairs r) := by
  let : Fact (0 < o.period) := ⟨o.period_pos⟩
  exact (isClosed_circleClosePairs o.period r).isCompact.image
    ((continuous_closedOrbitCurve o.period_mem).prodMap
      (continuous_closedOrbitCurve o.period_mem))

lemma ClosedFlowOrbit.shortPairs_subset_carriers (o : ClosedFlowOrbit) (r : ℝ) :
    o.shortPairs r ⊆ o.carrier ×ˢ o.carrier := by
  rintro z ⟨x, _, rfl⟩
  constructor
  · rw [ClosedFlowOrbit.carrier, ← range_closedOrbitCurve o.period_mem]
    exact ⟨x.1, rfl⟩
  · rw [ClosedFlowOrbit.carrier, ← range_closedOrbitCurve o.period_mem]
    exact ⟨x.2, rfl⟩

theorem ClosedFlowOrbit.measure_shortPairs_le (o : ClosedFlowOrbit) (r : ℝ) :
    o.measure.prod o.measure (o.shortPairs r) ≤
      ENNReal.ofReal (2 * r) * ENNReal.ofReal o.period := by
  let : Fact (0 < o.period) := ⟨o.period_pos⟩
  have hc := (continuous_closedOrbitCurve o.period_mem).measurable
  have hi := closedOrbitCurve_injective o.period_mem o.period_group
  rw [ClosedFlowOrbit.measure, closedOrbitMeasure, Measure.map_prod_map volume volume hc hc,
    Measure.map_apply (hc.prodMap hc) (o.isCompact_shortPairs r).measurableSet,
    ClosedFlowOrbit.shortPairs, Set.preimage_image_eq _ (hi.prodMap hi)]
  exact volume_circleClosePairs_le o.period r

theorem ClosedFlowOrbit.mem_shortPairs_of_flow (o : ClosedFlowOrbit)
    {x : ModularOrbitSpace} (hx : x ∈ o.carrier) {t r : ℝ} (ht : |t| ≤ r) :
    (x, modularRightTranslate (diagonalFlow t) x) ∈ o.shortPairs r := by
  rw [ClosedFlowOrbit.carrier, ← range_closedOrbitCurve o.period_mem] at hx
  obtain ⟨s, rfl⟩ := hx
  refine ⟨(s, s + (t : AddCircle o.period)), ?_, ?_⟩
  · change dist s (s + (t : AddCircle o.period)) ≤ r
    calc
      _ = ‖(t : AddCircle o.period)‖ := by
        rw [dist_comm, dist_eq_norm, add_sub_cancel_left]
      _ ≤ |t| := QuotientAddGroup.norm_mk_le_norm
      _ ≤ r := ht
  · simp only [Prod.map_apply, closedOrbitCurve_translate]

end Erdos1148.DukeArithmetic
