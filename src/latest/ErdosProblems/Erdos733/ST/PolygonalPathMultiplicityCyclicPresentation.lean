import ErdosProblems.Erdos733.ST.CyclicCurvePresentation
import ErdosProblems.Erdos733.ST.CyclicCurvePresentationIntersectionMultiplicity
import ErdosProblems.Erdos733.ST.FinitePolygonalSet
import ErdosProblems.Erdos733.ST.PolygonalPath
import ErdosProblems.Erdos733.ST.PolygonalPathIntersectionMultiplicity
import ErdosProblems.Erdos733.ST.PolygonalPathInGeneralPosition

open Classical
noncomputable section

-- [TABLET NODE: PolygonalPathMultiplicityCyclicPresentation]
lemma PolygonalPathMultiplicityCyclicPresentation
    (J : SimpleClosedPolygonalCurve) (Γ : PolygonalPath)
    (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier)
    (hgp : PolygonalPathInGeneralPosition Γ K)
    (R : CyclicCurvePresentation J K) :
    PolygonalPathIntersectionMultiplicity Γ K =
      CyclicCurvePresentationIntersectionMultiplicity Γ R := by
-- BODY
  unfold PolygonalPathIntersectionMultiplicity CyclicCurvePresentationIntersectionMultiplicity
  refine Finset.sum_congr rfl ?_
  intro i hi_mem
  by_cases hi : i + 1 < Γ.vertices.length
  · simp [hi]
    by_cases hsame : Γ.vertices[i] = Γ.vertices[i + 1]
    · simp [hsame]
    · simp [hsame]
      exact R.open_intersection_cardinality_partition Γ.vertices[i] Γ.vertices[i + 1] (by
        intro v hv hvin
        exact hgp.2.1 v hv (by
          rw [Γ.carrier_eq]
          exact Or.inr ⟨i, hi,
            openSegment_subset_segment ℝ Γ.vertices[i] Γ.vertices[i + 1] hvin⟩)) (by
        intro s hs
        exact hgp.2.2.1 i hi s hs)
  · simp [hi]
