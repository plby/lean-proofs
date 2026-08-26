import ErdosProblems.Erdos73.TreeExpansionEdges
import ErdosProblems.Erdos73.SubdivisionConnectivity

/-! Disjoint incidence-tree cells joined by clean paths give an actual subdivision. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {U V : Type*} [Fintype U] [LinearOrder U] [Fintype V] {W : U → Type*}
variable [∀ u, Fintype (W u)] [∀ u, LinearOrder (W u)]
variable {F : SimpleGraph U} {T : ∀ u, SimpleGraph (W u)}
variable [∀ u, LinearOrder (W u ⊕ OrientedEdge (T u))]
variable {port : ∀ u, U → W u} {G : SimpleGraph V}

structure TreeCellLinks (F : SimpleGraph U) (T : ∀ u, SimpleGraph (W u))
    [∀ u, LinearOrder (W u ⊕ OrientedEdge (T u))]
    (port : ∀ u, U → W u) (G : SimpleGraph V) where
  cell : ∀ u, GraphSubdivisionModel (treeIncidenceGraph (T u)) G
  disjoint : Pairwise (fun u v => Disjoint (cell u).vertexSet (cell v).vertexSet)
  link : OrientedEdge F → GraphPath G
  source_eq : ∀ e, (link e).source = (cell e.lo).branchVertex (Sum.inl (port e.lo e.hi))
  target_eq : ∀ e, (link e).target = (cell e.hi).branchVertex (Sum.inl (port e.hi e.lo))
  link_disjoint : Pairwise (fun e f => Disjoint (link e).vertexSet (link f).vertexSet)
  clean : ∀ e u x, x ∈ (link e).vertexSet → x ∈ (cell u).vertexSet →
    x = (link e).source ∨ x = (link e).target

namespace TreeCellLinks
variable (C : TreeCellLinks F T port G)

def branch (w : TreeExpansionVertex T) : V := (C.cell w.1).branchVertex w.2

theorem branch_mem (w : TreeExpansionVertex T) : C.branch w ∈ (C.cell w.1).vertexSet :=
  ((C.cell w.1).mem_vertexSet _).mpr (Or.inl ⟨w.2, rfl⟩)

theorem branch_injective : Function.Injective C.branch := by
  rintro ⟨u, x⟩ ⟨v, y⟩ he
  by_cases huv : u = v
  · subst v
    exact congrArg (Sigma.mk u) ((C.cell u).injective he)
  · exact (Finset.disjoint_left.mp (C.disjoint huv) (C.branch_mem ⟨u, x⟩)
      (he ▸ C.branch_mem ⟨v, y⟩)).elim

def path : TreeExpansionEdgeIndex F T → GraphPath G
  | Sum.inl ⟨u, e⟩ => (C.cell u).edgePath e
  | Sum.inr e => C.link e

theorem internal_subset (u : U) (e : OrientedEdge (treeIncidenceGraph (T u))) :
    ((C.cell u).edgePath e).vertexSet ⊆ (C.cell u).vertexSet := fun _ hx =>
  ((C.cell u).mem_vertexSet _).mpr (Or.inr ⟨e, hx⟩)

theorem branch_on_internal (u : U) (e : OrientedEdge (treeIncidenceGraph (T u)))
    (w : TreeExpansionVertex T) (hw : C.branch w ∈ ((C.cell u).edgePath e).vertexSet) :
    w = ⟨u, e.lo⟩ ∨ w = ⟨u, e.hi⟩ := by
  rcases w with ⟨v, x⟩
  by_cases huv : u = v
  · subst v
    exact ((C.cell u).branch_on_path e x hw).imp
      (congrArg (Sigma.mk u)) (congrArg (Sigma.mk u))
  · exact (Finset.disjoint_left.mp (C.disjoint huv) (C.internal_subset u e hw)
      (C.branch_mem ⟨v, x⟩)).elim

theorem link_inter_cell_branch (e : OrientedEdge F) (u : U) (x : V)
    (hx : x ∈ (C.link e).vertexSet) (hu : x ∈ (C.cell u).vertexSet) :
    ∃ w : TreeExpansionVertex T, x = C.branch w := by
  rcases C.clean e u x hx hu with hh | hh
  · exact ⟨⟨e.lo, Sum.inl (port e.lo e.hi)⟩, hh.trans (C.source_eq e)⟩
  · exact ⟨⟨e.hi, Sum.inl (port e.hi e.lo)⟩, hh.trans (C.target_eq e)⟩

theorem branch_on_link (e : OrientedEdge F) (w : TreeExpansionVertex T)
    (hw : C.branch w ∈ (C.link e).vertexSet) :
    w = ⟨e.lo, Sum.inl (port e.lo e.hi)⟩ ∨
      w = ⟨e.hi, Sum.inl (port e.hi e.lo)⟩ := by
  rcases C.clean e w.1 (C.branch w) hw (C.branch_mem w) with hh | hh
  · exact Or.inl (C.branch_injective (hh.trans (C.source_eq e)))
  · exact Or.inr (C.branch_injective (hh.trans (C.target_eq e)))

theorem paths_intersection {i j : TreeExpansionEdgeIndex F T} (hij : i ≠ j) (x : V)
    (hx : x ∈ (C.path i).vertexSet) (hy : x ∈ (C.path j).vertexSet) :
    ∃ w : TreeExpansionVertex T, x = C.branch w := by
  cases i with
  | inl a =>
    rcases a with ⟨u, e⟩
    cases j with
    | inl b =>
      rcases b with ⟨v, f⟩
      by_cases huv : u = v
      · subst v
        have hef : e ≠ f := fun hh => hij (hh ▸ rfl)
        obtain ⟨w, hw, _, _⟩ := (C.cell u).intersection hef x hx hy
        exact ⟨⟨u, w⟩, hw⟩
      · exact (Finset.disjoint_left.mp (C.disjoint huv)
          (C.internal_subset u e hx) (C.internal_subset v f hy)).elim
    | inr f => exact C.link_inter_cell_branch f u x hy (C.internal_subset u e hx)
  | inr e =>
    cases j with
    | inl b =>
      rcases b with ⟨u, f⟩
      exact C.link_inter_cell_branch e u x hx (C.internal_subset u f hy)
    | inr f =>
      have hef : e ≠ f := fun hh => hij (congrArg Sum.inr hh)
      exact (Finset.disjoint_left.mp (C.link_disjoint hef) hx hy).elim

def realization [LinearOrder (TreeExpansionVertex T)] :
    EdgePathRealization (treeExpansionGraph F T port) G (TreeExpansionEdgeIndex F T) where
  branch := C.branch
  injective := C.branch_injective
  left := treeExpansionEdgeLeft F T port
  right := treeExpansionEdgeRight F T port
  path := C.path
  source_eq := by
    rintro (⟨u, e⟩ | e)
    · exact (C.cell u).source_eq e
    · exact C.source_eq e
  target_eq := by
    rintro (⟨u, e⟩ | e)
    · exact (C.cell u).target_eq e
    · exact C.target_eq e
  covers := treeExpansionEdge_covers F T port
  branch_on_path := by
    rintro (⟨u, e⟩ | e) w hw
    · exact C.branch_on_internal u e w hw
    · exact C.branch_on_link e w hw
  intersection := fun _ _ hij x hx hy => C.paths_intersection hij x hx hy

def toSubdivisionModel [LinearOrder (TreeExpansionVertex T)] :
    GraphSubdivisionModel (treeExpansionGraph F T port) G := C.realization.toSubdivisionModel

theorem toSubdivisionModel_odd [LinearOrder (TreeExpansionVertex T)]
    (hc : ∀ u e, Odd ((C.cell u).edgePath e).walk.length)
    (hl : ∀ e, Odd (C.link e).walk.length) (e : OrientedEdge (treeExpansionGraph F T port)) :
    Odd (C.toSubdivisionModel.edgePath e).walk.length := by
  apply C.realization.toSubdivisionModel_odd
  rintro (⟨u, d⟩ | d)
  · exact hc u d
  · exact hl d

theorem hasIndependenceDefectAtLeast [LinearOrder (TreeExpansionVertex T)]
    (hc : ∀ u e, Odd ((C.cell u).edgePath e).walk.length)
    (hl : ∀ e, Odd (C.link e).walk.length) (hT : ∀ u, (T u).IsTree)
    (r : ℕ) (hF : 2 * F.indepNum + r ≤ Fintype.card U) :
    HasIndependenceDefectAtLeast r G :=
  C.toSubdivisionModel.hasIndependenceDefectAtLeast_of_odd
    (C.toSubdivisionModel_odd hc hl) r (treeExpansion_full_defect F T port hT r hF)

end TreeCellLinks
end
end Erdos73
