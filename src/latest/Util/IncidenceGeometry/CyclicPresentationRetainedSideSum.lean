import Util.IncidenceGeometry.CyclicCurvePresentationIntersectionMultiplicity

open Classical
noncomputable section

lemma CyclicPresentationRetainedSideSum
    (γ : PolygonalPath) {J : SimpleClosedPolygonalCurve} {K : FinitePolygonalSet}
    (R : CyclicCurvePresentation J K) :
    CyclicCurvePresentationIntersectionMultiplicity γ R =
      ((Finset.range γ.vertices.length).filter fun i =>
        if hi : i + 1 < γ.vertices.length then
          γ.vertices[i] ≠ γ.vertices[i + 1]
        else
          False).sum (fun i =>
            if hi : i + 1 < γ.vertices.length then
              R.vertices.attach.sum fun p =>
                Set.ncard (openSegment ℝ γ.vertices[i] γ.vertices[i + 1] ∩
                  openSegment ℝ p.1 (R.successor p).1)
            else
              0) := by
  rw [CyclicCurvePresentationIntersectionMultiplicity]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hlt : i + 1 < γ.vertices.length
  · by_cases hne : γ.vertices[i] ≠ γ.vertices[i + 1]
    · simp [hlt, hne]
    · simp [hlt, hne]
  · simp [hlt]
