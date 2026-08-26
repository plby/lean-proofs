import ErdosProblems.Erdos73.IncidenceEdgeWitness

/-! Actual incidence subdivisions: even original corridors become two odd corridors. -/

namespace Erdos73.GraphSubdivisionModel
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {W V : Type*} [Fintype W] [LinearOrder W] [Fintype V]
variable {H : SimpleGraph W} {G : SimpleGraph V} [LinearOrder (W ⊕ OrientedEdge H)]
variable (S : GraphSubdivisionModel H G)

def incidenceVertex : W ⊕ OrientedEdge H → V
  | Sum.inl w => S.branchVertex w
  | Sum.inr e => S.firstInternal e

theorem incidenceVertex_injective (hlong : ∀ e, 2 ≤ (S.edgePath e).walk.length) :
    Function.Injective S.incidenceVertex := by
  intro x y he
  cases x with
  | inl w =>
    cases y with
    | inl z => exact congrArg Sum.inl (S.injective he)
    | inr e => exact (S.firstInternal_not_branch hlong e w he.symm).elim
  | inr e =>
    cases y with
    | inl w => exact (S.firstInternal_not_branch hlong e w he).elim
    | inr f => exact congrArg Sum.inr (S.firstInternal_injective hlong he)

def incidencePath (d : OrientedEdge (treeIncidenceGraph H)) : GraphPath G :=
  let D := incidenceEdgeWitness d
  if d.lo = Sum.inl (halfEndpoint D.original D.side) then S.halfPath D.original D.side
  else (S.halfPath D.original D.side).reverse

theorem incidencePath_source (d : OrientedEdge (treeIncidenceGraph H)) :
    (S.incidencePath d).source = S.incidenceVertex d.lo := by
  rcases (incidenceEdgeWitness d).endpoints with he | he
  · dsimp only [incidencePath]
    rw [if_pos he.1, S.halfPath_source, he.1]
    rfl
  · have hn : d.lo ≠ Sum.inl (halfEndpoint (incidenceEdgeWitness d).original
        (incidenceEdgeWitness d).side) := by rw [he.1]; simp
    dsimp only [incidencePath]
    rw [if_neg hn, GraphPath.reverse_source, S.halfPath_target, he.1]
    rfl

theorem incidencePath_target (d : OrientedEdge (treeIncidenceGraph H)) :
    (S.incidencePath d).target = S.incidenceVertex d.hi := by
  rcases (incidenceEdgeWitness d).endpoints with he | he
  · simp only [incidencePath, if_pos he.1, S.halfPath_target, he.2, incidenceVertex]
  · have hn : d.lo ≠ Sum.inl (halfEndpoint (incidenceEdgeWitness d).original
        (incidenceEdgeWitness d).side) := by rw [he.1]; simp
    simp only [incidencePath, if_neg hn, GraphPath.reverse_target, S.halfPath_source, he.2,
      incidenceVertex]

theorem incidencePath_vertexSet (d : OrientedEdge (treeIncidenceGraph H)) :
    (S.incidencePath d).vertexSet =
      (S.halfPath (incidenceEdgeWitness d).original (incidenceEdgeWitness d).side).vertexSet := by
  dsimp only [incidencePath]
  split_ifs <;> simp only [GraphPath.reverse_vertexSet]

theorem incidence_branch_on_path (hlong : ∀ e, 2 ≤ (S.edgePath e).walk.length)
    (d : OrientedEdge (treeIncidenceGraph H)) (w : W ⊕ OrientedEdge H)
    (hw : S.incidenceVertex w ∈ (S.incidencePath d).vertexSet) : w = d.lo ∨ w = d.hi := by
  rw [S.incidencePath_vertexSet] at hw
  cases w with
  | inl w =>
    have hh := S.branch_on_halfPath hlong _ _ w hw
    exact hh ▸ (incidenceEdgeWitness d).branch_incident
  | inr e =>
    have hh := S.firstInternal_on_halfPath hlong _ e _ hw
    exact hh ▸ (incidenceEdgeWitness d).midpoint_incident

theorem incidence_paths_intersection (hlong : ∀ e, 2 ≤ (S.edgePath e).walk.length)
    {d f : OrientedEdge (treeIncidenceGraph H)} (hdf : d ≠ f) {x : V}
    (hx : x ∈ (S.incidencePath d).vertexSet) (hx' : x ∈ (S.incidencePath f).vertexSet) :
    ∃ w, x = S.incidenceVertex w ∧ (w = d.lo ∨ w = d.hi) ∧ (w = f.lo ∨ w = f.hi) := by
  rw [S.incidencePath_vertexSet] at hx hx'
  let D := incidenceEdgeWitness d
  let F := incidenceEdgeWitness f
  by_cases he : D.original = F.original
  · have hs : D.side ≠ F.side := fun hs => hdf (D.edge_eq_of_code F he hs)
    have hx'' : x ∈ (S.halfPath D.original F.side).vertexSet := by simpa only [he] using hx'
    have hh := S.halfPaths_intersection D.original hs hx hx''
    refine ⟨Sum.inr D.original, hh, D.midpoint_incident, ?_⟩
    rw [he]
    exact F.midpoint_incident
  · obtain ⟨w, hw, _, _⟩ := S.intersection he x (S.halfPath_subset _ _ hx) (S.halfPath_subset _ _ hx')
    have hwD := S.branch_on_halfPath hlong D.original D.side w (hw ▸ hx)
    have hwF := S.branch_on_halfPath hlong F.original F.side w (hw ▸ hx')
    exact ⟨Sum.inl w, hw, hwD ▸ D.branch_incident, hwF ▸ F.branch_incident⟩

def incidenceSubdivisionModel (hlong : ∀ e, 2 ≤ (S.edgePath e).walk.length) :
    GraphSubdivisionModel (treeIncidenceGraph H) G where
  branchVertex := S.incidenceVertex
  injective := S.incidenceVertex_injective hlong
  edgePath := S.incidencePath
  source_eq := S.incidencePath_source
  target_eq := S.incidencePath_target
  branch_on_path := S.incidence_branch_on_path hlong
  intersection := fun _ _ hdf _ hx hx' => S.incidence_paths_intersection hlong hdf hx hx'

theorem incidencePath_odd (heven : ∀ e, Even (S.edgePath e).walk.length)
    (d : OrientedEdge (treeIncidenceGraph H)) : Odd (S.incidencePath d).walk.length := by
  have hh := S.halfPath_odd heven (incidenceEdgeWitness d).original (incidenceEdgeWitness d).side
  by_cases hdir : d.lo = Sum.inl (halfEndpoint (incidenceEdgeWitness d).original
      (incidenceEdgeWitness d).side)
  · have hp : S.incidencePath d =
        S.halfPath (incidenceEdgeWitness d).original (incidenceEdgeWitness d).side := by
      dsimp only [incidencePath]
      rw [if_pos hdir]
    exact (congrArg (fun P : GraphPath G => P.walk.length) hp).symm ▸ hh
  · have hp : S.incidencePath d =
        (S.halfPath (incidenceEdgeWitness d).original (incidenceEdgeWitness d).side).reverse := by
      dsimp only [incidencePath]
      rw [if_neg hdir]
    have hl := congrArg (fun P : GraphPath G => P.walk.length) hp
    have hrev : (S.halfPath (incidenceEdgeWitness d).original
        (incidenceEdgeWitness d).side).reverse.walk.length =
        (S.halfPath (incidenceEdgeWitness d).original (incidenceEdgeWitness d).side).walk.length :=
      _root_.SimpleGraph.Walk.length_reverse _
    exact (hl.trans hrev).symm ▸ hh

theorem incidenceSubdivisionModel_vertexSet_subset (hlong : ∀ e, 2 ≤ (S.edgePath e).walk.length) :
    (S.incidenceSubdivisionModel hlong).vertexSet ⊆ S.vertexSet := by
  intro x hx
  rcases ((S.incidenceSubdivisionModel hlong).mem_vertexSet x).mp hx with ⟨w, rfl⟩ | ⟨d, hx⟩
  · cases w with
    | inl w => exact (S.mem_vertexSet _).mpr (Or.inl ⟨w, rfl⟩)
    | inr e => exact (S.mem_vertexSet _).mpr (Or.inr ⟨e, S.firstInternal_mem e⟩)
  · have hx' : x ∈ (S.incidencePath d).vertexSet := hx
    rw [S.incidencePath_vertexSet] at hx'
    exact (S.mem_vertexSet x).mpr (Or.inr ⟨_, S.halfPath_subset _ _ hx'⟩)

end
end Erdos73.GraphSubdivisionModel
