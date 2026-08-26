import ErdosProblems.Erdos73.TileEdgeRegions

/-! The prescribed tile centres and three-piece routes form an actual wall subdivision. -/

namespace Erdos73.BrickTileArray
noncomputable section
open scoped Classical
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {c r C R : ℕ} (A : BrickTileArray c r C R)

def gapPath (e : OrientedEdge (elementaryWall c r)) : GraphPath (elementaryWall C R) :=
  (A.exists_edge_gap_path e.adj).choose

theorem gapPath_source (e : OrientedEdge (elementaryWall c r)) :
    (A.gapPath e).source = (A.arm e.lo (brickWallPort e.lo.val e.hi.val)).target :=
  (A.exists_edge_gap_path e.adj).choose_spec.1

theorem gapPath_target (e : OrientedEdge (elementaryWall c r)) :
    (A.gapPath e).target = (A.arm e.hi (brickWallPort e.hi.val e.lo.val)).target :=
  (A.exists_edge_gap_path e.adj).choose_spec.2.1

theorem gapPath_subset (e : OrientedEdge (elementaryWall c r)) :
    (A.gapPath e).vertexSet ⊆ A.edgeGap e.lo e.hi :=
  (A.exists_edge_gap_path e.adj).choose_spec.2.2

def routedEdgePath (e : OrientedEdge (elementaryWall c r)) : GraphPath (elementaryWall C R) :=
  (A.arm e.lo (brickWallPort e.lo.val e.hi.val)).append3WithEqToPath (A.gapPath e)
    (A.arm e.hi (brickWallPort e.hi.val e.lo.val)).reverse (A.gapPath_source e).symm
    (by simpa only [GraphPath.reverse_source] using A.gapPath_target e)

theorem routedEdgePath_source (e : OrientedEdge (elementaryWall c r)) :
    (A.routedEdgePath e).source = A.center e.lo := by
  simp only [routedEdgePath, GraphPath.append3WithEqToPath_source, A.arm_source]

theorem routedEdgePath_target (e : OrientedEdge (elementaryWall c r)) :
    (A.routedEdgePath e).target = A.center e.hi := by
  simp only [routedEdgePath, GraphPath.append3WithEqToPath_target, GraphPath.reverse_target,
    A.arm_source]

theorem routedEdgePath_subset (e : OrientedEdge (elementaryWall c r)) :
    (A.routedEdgePath e).vertexSet ⊆ A.edgeRegion e := by
  intro x hx
  have hh := (A.arm e.lo (brickWallPort e.lo.val e.hi.val)).append3WithEqToPath_vertexSet_subset
    (A.gapPath e) (A.arm e.hi (brickWallPort e.hi.val e.lo.val)).reverse
    (A.gapPath_source e).symm
    (by simpa only [GraphPath.reverse_source] using A.gapPath_target e) hx
  simp only [GraphPath.reverse_vertexSet, mem_union] at hh
  simp only [edgeRegion, mem_union]
  rcases hh with (hh | hh) | hh
  · exact Or.inl (Or.inl hh)
  · exact Or.inl (Or.inr (A.gapPath_subset e hh))
  · exact Or.inr hh

def toSubdivisionModel : GraphSubdivisionModel (elementaryWall c r) (elementaryWall C R) where
  branchVertex := A.center
  injective := A.center_injective
  edgePath := A.routedEdgePath
  source_eq := A.routedEdgePath_source
  target_eq := A.routedEdgePath_target
  branch_on_path := by
    intro e w hw
    apply A.edgeRegion_branch
    apply A.routedEdgePath_subset e
    simpa only [GraphPath.vertexSet, List.mem_toFinset] using hw
  intersection := by
    intro e f hef x hx hx'
    apply A.edgeRegion_intersection hef
    · apply A.routedEdgePath_subset e
      simpa only [GraphPath.vertexSet, List.mem_toFinset] using hx
    · apply A.routedEdgePath_subset f
      simpa only [GraphPath.vertexSet, List.mem_toFinset] using hx'

theorem toSubdivisionModel_branchVertex (w : ElementaryWallVertex c r) :
    A.toSubdivisionModel.branchVertex w = A.point w.val := rfl

end
end Erdos73.BrickTileArray
