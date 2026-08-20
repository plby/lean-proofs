import ErdosProblems.Erdos733.ST.SumFaceDegrees
import ErdosProblems.Erdos733.ST.FaceDegreeLowerBound
import ErdosProblems.Erdos733.ST.ConnectedEulerFormula
import ErdosProblems.Erdos733.ST.PlaneFaceData
import ErdosProblems.Erdos733.ST.PlaneFaceDataExists

open Classical
noncomputable section

-- [TABLET NODE: ConnectedPlanarEdgeBound]
lemma ConnectedPlanarEdgeBound {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    G.Connected → 3 ≤ Fintype.card V →
      (∃ D : OrdinaryPolygonalDrawing G, D.crossingSet.card = 0) →
        G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
-- BODY
  classical
  intro hconn hn hdraw
  letI : DecidableRel G.Adj := Classical.decRel _
  rcases hdraw with ⟨D, hD⟩
  rcases (PlaneFaceDataExists.{_, 0} G D hD) with ⟨A⟩
  by_cases hedge_zero : G.edgeFinset.card = 0
  · omega
  have hedge_pos : 0 < G.edgeFinset.card := Nat.pos_of_ne_zero hedge_zero
  letI : Fintype A.Face := A.faceFintype
  have hface_lower : ∀ F : A.Face, 3 ≤ A.faceDegree F :=
    FaceDegreeLowerBound G D hD A hconn hn hedge_pos
  have hsum_lower :
      (∑ _F : A.Face, (3 : ℕ)) ≤ ∑ F : A.Face, A.faceDegree F := by
    exact Finset.sum_le_sum (fun F _hF => hface_lower F)
  have hface_sum_lower :
      Fintype.card A.Face * 3 ≤ ∑ F : A.Face, A.faceDegree F := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum_lower
  have hsum_degrees :
      (∑ F : A.Face, A.faceDegree F) = 2 * G.edgeFinset.card :=
    SumFaceDegrees G D hD A
  have hface_bound :
      Fintype.card A.Face * 3 ≤ 2 * G.edgeFinset.card := by
    simpa [hsum_degrees] using hface_sum_lower
  have hEuler :
      (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) +
        (Fintype.card A.Face : ℤ) = 2 :=
    ConnectedEulerFormula G D hD A hconn
  omega
