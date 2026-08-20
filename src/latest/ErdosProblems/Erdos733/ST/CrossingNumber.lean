import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing

open Classical
noncomputable section

-- [TABLET NODE: CrossingNumber]
noncomputable def CrossingNumber {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] : ℕ :=
-- BODY
  sInf (Set.range (fun D : OrdinaryPolygonalDrawing G => D.crossingSet.card))
