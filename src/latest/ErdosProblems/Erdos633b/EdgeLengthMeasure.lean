import ErdosProblems.Erdos633b.BoundaryTopology
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Actual open triangle edges have finite one-dimensional Hausdorff
measure equal to their side lengths. Their constant weights are integrable. -/

namespace Erdos633b

open MeasureTheory

noncomputable def edgeLengthMeasure : Measure Plane := Measure.hausdorffMeasure 1

instance : NullSingletonClass edgeLengthMeasure :=
  Measure.nullSingletonClass_hausdorff Plane (by norm_num : (0 : ℝ) < 1)

namespace Triangle

theorem openEdge_measurableSet (S : Triangle) (j : Fin 3) :
    MeasurableSet (S.openEdge j) := by
  have he : S.openEdge j = {p | S.coord j p = 0} ∩
      ⋂ k : {k : Fin 3 // k ≠ j}, {p | 0 < S.coord k.val p} := by
    ext p
    simp only [openEdge, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      Subtype.forall]
  rw [he]
  apply MeasurableSet.inter
  · exact (isClosed_eq (continuous_barycentric_coord S.affineBasis j)
      continuous_const).measurableSet
  · exact MeasurableSet.iInter (fun k =>
      (isOpen_lt continuous_const (continuous_barycentric_coord S.affineBasis k.val)).measurableSet)

theorem edge_ae_eq_openEdge (S : Triangle) (j : Fin 3) :
    S.edge j =ᵐ[edgeLengthMeasure] S.openEdge j := by
  apply ae_eq_set.mpr
  constructor
  · apply measure_mono_null (t := {S.points (j + 1), S.points (j + 2)})
    · intro p hp
      by_contra hn
      apply hp.2
      rw [S.openEdge_eq_openSegment]
      apply mem_openSegment_of_ne_left_right
      · intro he
        exact hn (Or.inl he.symm)
      · intro he
        exact hn (Or.inr he.symm)
      · simpa only [S.edge_eq_segment] using hp.1
    · exact (Set.toFinite _).measure_zero edgeLengthMeasure
  · rw [Set.sdiff_eq_empty.mpr (S.openEdge_subset_edge j)]
    exact measure_empty

theorem openEdge_lengthMeasure (S : Triangle) (j : Fin 3) :
    edgeLengthMeasure (S.openEdge j) = ENNReal.ofReal (S.side j) := by
  rw [← measure_congr (S.edge_ae_eq_openEdge j), S.edge_eq_segment]
  change Measure.hausdorffMeasure 1 (segment ℝ _ _) = _
  rw [hausdorffMeasure_segment, edist_dist]
  rfl

theorem openEdge_real_lengthMeasure (S : Triangle) (j : Fin 3) :
    edgeLengthMeasure.real (S.openEdge j) = S.side j := by
  rw [Measure.real, S.openEdge_lengthMeasure, ENNReal.toReal_ofReal (S.side_pos j).le]

theorem openEdge_integrable_indicator (S : Triangle) (j : Fin 3) (c : ℝ) :
    Integrable ((S.openEdge j).indicator (fun _ : Plane => c)) edgeLengthMeasure := by
  apply IntegrableOn.integrable_indicator _ (S.openEdge_measurableSet j)
  exact integrableOn_const (by rw [S.openEdge_lengthMeasure]; exact ENNReal.ofReal_ne_top)

theorem integral_openEdge_indicator (S : Triangle) (j : Fin 3) (c : ℝ) :
    (∫ p, (S.openEdge j).indicator (fun _ : Plane => c) p ∂edgeLengthMeasure) =
      S.side j * c := by
  rw [integral_indicator_const c (S.openEdge_measurableSet j),
    S.openEdge_real_lengthMeasure, smul_eq_mul]

end Triangle
end Erdos633b
