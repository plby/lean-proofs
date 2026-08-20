import ErdosProblems.Erdos733.ST.CyclicCurvePresentation
import ErdosProblems.Erdos733.ST.CyclicCurvePresentationIntersectionMultiplicity
import ErdosProblems.Erdos733.ST.CyclicFanMiddleSumEven
import ErdosProblems.Erdos733.ST.CyclicPresentationTriangleFanMiddleSumEven
import ErdosProblems.Erdos733.ST.CyclicPresentationTriangleGeneralPosition
import ErdosProblems.Erdos733.ST.CyclicPresentationRetainedSideSum
import ErdosProblems.Erdos733.ST.CyclicPresentationRetainedSideFanBridge
import ErdosProblems.Erdos733.ST.CyclicPresentationRetainedApexBasicAvoidance
import ErdosProblems.Erdos733.ST.PolygonalPathInGeneralPosition
import ErdosProblems.Erdos733.ST.TriangleBoundaryCyclicIntersectionMultiplicity
import ErdosProblems.Erdos733.ST.TriangleBoundaryEvenIntersections

open Classical
noncomputable section

-- [TABLET NODE: CyclicPresentationClosedPathEvenIntersections]
lemma CyclicPresentationClosedPathEvenIntersections
    (J : SimpleClosedPolygonalCurve) (Γ : PolygonalPath)
    (K : FinitePolygonalSet)
    (hΓ : Γ.source = Γ.target)
    (hgp : PolygonalPathInGeneralPosition Γ K)
    (R : CyclicCurvePresentation J K) :
    Even (CyclicCurvePresentationIntersectionMultiplicity Γ R) := by
-- BODY
  let retained : Finset ℕ :=
    ((Finset.range Γ.vertices.length).filter fun i =>
      if hi : i + 1 < Γ.vertices.length then
        Γ.vertices[i] ≠ Γ.vertices[i + 1]
      else
        False)
  let start : retained → EuclideanSpace ℝ (Fin 2) := fun i =>
    Γ.vertices[i.1]'(by
      have h := i.2
      simp [retained] at h
      exact h.1)
  let stop : retained → EuclideanSpace ℝ (Fin 2) := fun i =>
    Γ.vertices[i.1 + 1]'(by
      have h := i.2
      simp [retained] at h
      exact h.2.choose)
  rw [CyclicPresentationRetainedSideSum Γ R]
  obtain ⟨σ, hσ, hsum⟩ := CyclicPresentationRetainedSideFanBridge Γ hΓ R
  rw [hsum]
  obtain ⟨z, _hzJ, hza, hbz, hside, hncol, htri⟩ :=
    CyclicPresentationRetainedApexBasicAvoidance Γ hgp R σ hσ
  exact CyclicPresentationTriangleFanMiddleSumEven R σ z start hza hside hbz hncol htri
