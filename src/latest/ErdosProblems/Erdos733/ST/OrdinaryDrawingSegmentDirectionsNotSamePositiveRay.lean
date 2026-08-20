import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing
import ErdosProblems.Erdos733.ST.SegmentSameRayInitialSubsegment

open Classical
noncomputable section

-- [TABLET NODE: OrdinaryDrawingSegmentDirectionsNotSamePositiveRay]
lemma OrdinaryDrawingSegmentDirectionsNotSamePositiveRay {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    {e f : G.edgeFinset} (hef : e ≠ f)
    {i j : ℕ}
    (hi : i + 1 < (D.edgeArc e).vertices.length)
    (hj : j + 1 < (D.edgeArc f).vertices.length)
    {x d v : EuclideanSpace ℝ (Fin 2)}
    (hd : d ≠ 0)
    (hseg_e :
      segment ℝ x (x + d) =
        segment ℝ (D.edgeArc e).vertices[i] (D.edgeArc e).vertices[i + 1])
    (hseg_f :
      segment ℝ x (x + v) =
        segment ℝ (D.edgeArc f).vertices[j] (D.edgeArc f).vertices[j + 1]) :
    ¬ ∃ a : ℝ, 0 < a ∧ v = a • d := by
-- BODY
  rintro ⟨a, ha, hv⟩
  obtain ⟨q, hxq, hsub⟩ := SegmentSameRayInitialSubsegment x d a hd ha
  have hbad := D.no_shared_nondegenerate_subarc (e₁ := e) (e₂ := f) hef
  apply hbad
  refine ⟨i, j, hi, hj, x, q, hxq, ?_⟩
  intro y hy
  have hy' := hsub hy
  constructor
  · simpa [hseg_e] using hy'.1
  · have hseg_f' :
        segment ℝ x (x + a • d) =
          segment ℝ (D.edgeArc f).vertices[j] (D.edgeArc f).vertices[j + 1] := by
      simpa [hv] using hseg_f
    simpa [hseg_f'] using hy'.2
