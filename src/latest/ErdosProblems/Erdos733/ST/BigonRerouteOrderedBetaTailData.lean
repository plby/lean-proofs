import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing

open Classical
noncomputable section

-- [TABLET NODE: BigonRerouteOrderedBetaTailData]
structure BigonRerouteOrderedBetaTailData {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (beta : G.edgeFinset) (u : V)
    (y : EuclideanSpace ℝ (Fin 2))
    (B Bplus Rbeta H : Set (EuclideanSpace ℝ (Fin 2))) where
-- BODY
  tailArc : PolygonalArc
  farEndpoint : V
  u_mem_beta : u ∈ beta.1
  farEndpoint_mem_beta : farEndpoint ∈ beta.1
  farEndpoint_ne_u : farEndpoint ≠ u
  source_eq : tailArc.source = y
  target_eq : tailArc.target = D.vertexPlacement farEndpoint
  carrier_eq : tailArc.carrier = Rbeta
  carrier_subset_old_beta : tailArc.carrier ⊆ (D.edgeArc beta).carrier
  relativeInterior_subset_old_beta :
    tailArc.relativeInterior ⊆ (D.edgeArc beta).relativeInterior
  meets_removed_subarc :
    tailArc.carrier ∩ (B ∪ Bplus) =
      ({y} : Set (EuclideanSpace ℝ (Fin 2)))
  carrier_subset_H : tailArc.carrier ⊆ H
  old_orientation_compatible :
    ((D.edgeArc beta).source = D.vertexPlacement u →
        tailArc.target = (D.edgeArc beta).target) ∧
      ((D.edgeArc beta).target = D.vertexPlacement u →
        tailArc.target = (D.edgeArc beta).source)
