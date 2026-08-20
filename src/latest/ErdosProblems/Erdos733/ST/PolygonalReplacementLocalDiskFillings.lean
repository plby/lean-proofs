import ErdosProblems.Erdos733.ST.PolygonalReplacementLocalDiskFillingData
import ErdosProblems.Erdos733.ST.EndpointFixedPolygonalDiskFillingClean
import ErdosProblems.Erdos733.ST.PolygonalReplacementIntersectionDiskChains
import ErdosProblems.Erdos733.ST.PolygonalReplacementVertexDiskSpokes

open Classical
noncomputable section

-- [TABLET NODE: PolygonalReplacementLocalDiskFillings]
lemma PolygonalReplacementLocalDiskFillings {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks) :
    Nonempty (PolygonalReplacementLocalDiskFillingData G D controlDisks tubeChains) := by
-- BODY
  classical
  rcases PolygonalReplacementVertexDiskSpokes G D controlDisks tubeChains with
    ⟨vertex_spoke, vertex_spoke_source, vertex_spoke_source_ne_target,
      vertex_spoke_target_boundary, vertex_spoke_attached_to_tube,
      vertex_boundary_covered, vertex_spoke_carrier_subset_closedBall,
      vertex_spoke_relativeInterior_subset_ball, vertex_spokes_same_vertex_disjoint⟩
  rcases PolygonalReplacementIntersectionDiskChains G D controlDisks tubeChains with
    ⟨intersection_chain, intersection_chain_source_ne_target,
      intersection_chain_source_boundary, intersection_chain_target_boundary,
      intersection_chain_source_attached_to_tube,
      intersection_chain_target_attached_to_tube, intersection_boundary_covered,
      intersection_chain_carrier_subset_closedBall,
      intersection_chain_relativeInterior_subset_ball,
      intersection_chains_no_shared_nondegenerate_subarc,
      intersection_chains_no_triple_intersections,
      intersection_chains_transverse_intersections,
      intersection_chains_pairwise_at_most_one⟩
  exact ⟨{
    vertex_spoke := vertex_spoke
    vertex_spoke_source := vertex_spoke_source
    vertex_spoke_source_ne_target := vertex_spoke_source_ne_target
    vertex_spoke_target_boundary := vertex_spoke_target_boundary
    vertex_spoke_attached_to_tube := vertex_spoke_attached_to_tube
    vertex_boundary_covered := vertex_boundary_covered
    vertex_spoke_carrier_subset_closedBall := vertex_spoke_carrier_subset_closedBall
    vertex_spoke_relativeInterior_subset_ball := vertex_spoke_relativeInterior_subset_ball
    vertex_spokes_same_vertex_disjoint := vertex_spokes_same_vertex_disjoint
    intersection_chain := intersection_chain
    intersection_chain_source_ne_target := intersection_chain_source_ne_target
    intersection_chain_source_boundary := intersection_chain_source_boundary
    intersection_chain_target_boundary := intersection_chain_target_boundary
    intersection_chain_source_attached_to_tube := intersection_chain_source_attached_to_tube
    intersection_chain_target_attached_to_tube := intersection_chain_target_attached_to_tube
    intersection_boundary_covered := intersection_boundary_covered
    intersection_chain_carrier_subset_closedBall := intersection_chain_carrier_subset_closedBall
    intersection_chain_relativeInterior_subset_ball := intersection_chain_relativeInterior_subset_ball
    intersection_chains_no_shared_nondegenerate_subarc :=
      intersection_chains_no_shared_nondegenerate_subarc
    intersection_chains_no_triple_intersections :=
      intersection_chains_no_triple_intersections
    intersection_chains_transverse_intersections :=
      intersection_chains_transverse_intersections
    intersection_chains_pairwise_at_most_one := intersection_chains_pairwise_at_most_one
  }⟩
