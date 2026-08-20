import ErdosProblems.Erdos733.ST.SimpleClosedPolygonalCurve
import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.FinitePolygonalSet
import ErdosProblems.Erdos733.ST.SimpleClosedCurveAsFinitePolygonalSet

open Classical
noncomputable section

-- [TABLET NODE: SimpleClosedPolygonalCurveComplementOpen]
lemma SimpleClosedPolygonalCurveComplementOpen
    (J : SimpleClosedPolygonalCurve) : IsOpen J.carrierᶜ := by
-- BODY
  rcases SimpleClosedCurveAsFinitePolygonalSet J with ⟨K, hKJ⟩
  have hpoints_closed : IsClosed (K.points : Set (EuclideanSpace ℝ (Fin 2))) := by
    exact K.points.finite_toSet.isClosed
  have hsegments_closed :
      IsClosed (⋃ s : {s // s ∈ K.segments}, segment ℝ s.1.1 s.1.2) := by
    refine isClosed_iUnion_of_finite ?_
    intro s
    rw [← convexHull_pair (𝕜 := ℝ) s.1.1 s.1.2]
    exact (by
      simp : ({s.1.1, s.1.2} : Set (EuclideanSpace ℝ (Fin 2))).Finite).isClosed_convexHull ℝ
  have hKclosed : IsClosed K.carrier := by
    rw [K.carrier_eq]
    exact hpoints_closed.union hsegments_closed
  simpa [hKJ] using hKclosed.isOpen_compl
