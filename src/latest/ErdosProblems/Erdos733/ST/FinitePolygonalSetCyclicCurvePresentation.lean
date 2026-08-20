import ErdosProblems.Erdos733.ST.SimpleClosedPolygonalCurve
import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.FinitePolygonalSet
import ErdosProblems.Erdos733.ST.CyclicCurvePresentation
import ErdosProblems.Erdos733.ST.FinitePolygonalSetCarrierEqSimpleClosedCurvePointsTwo
import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicSuccessorOrder
import ErdosProblems.Erdos733.ST.FinitePolygonalSetCyclicSuccessorPiecesContained
import ErdosProblems.Erdos733.ST.FinitePolygonalSetListedSegmentsCoveredByCyclicPieces
import ErdosProblems.Erdos733.ST.FinitePolygonalSetOpenIntersectionPartition

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetCyclicCurvePresentation]
lemma FinitePolygonalSetCyclicCurvePresentation
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier) :
    Nonempty (CyclicCurvePresentation J K) := by
-- BODY
  have points_card_two_le : 2 ≤ K.points.card :=
    FinitePolygonalSetCarrierEqSimpleClosedCurvePointsTwo J K hKJ
  have hpoints_nonempty : K.points.Nonempty := by
    exact Finset.card_pos.mp (by omega)
  have vertices_on_curve :
      ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ K.points → p ∈ J.carrier := by
    intro p hp
    rw [← hKJ, K.carrier_eq]
    exact Or.inl hp
  rcases FinitePolygonalSetCyclicSuccessorOrder J K hKJ with ⟨D⟩
  rcases FinitePolygonalSetCyclicSuccessorPiecesContained J K hKJ D with
    ⟨hcarrier, hrefine, _harcCarrier, _hopen_subset, _hno_listed_open,
      _hopen_disjoint⟩
  have hsegrefine :=
    FinitePolygonalSetListedSegmentsCoveredByCyclicPieces J K hKJ D
  have hpartition :=
    FinitePolygonalSetOpenIntersectionPartition J K hKJ D
  refine ⟨⟨K.points, hKJ, ?_, hpoints_nonempty, ?_, D.successor, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rfl
  · exact vertices_on_curve
  · exact D.successor_single_cycle
  · exact D.successor_nondegenerate
  · exact hcarrier
  · exact hrefine
  · exact hsegrefine
  · exact hpartition
  · intro s t hs ht hst p hps hpt
    exact K.segment_intersections_listed s t hs ht hst p hps hpt
