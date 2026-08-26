import ErdosProblems.Erdos73.TreeCellLinks
import ErdosProblems.Erdos73.SubdivisionIncidenceModel

/-! Even tree cells and odd external links preserve the base graph's defect. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {U V : Type*} [Fintype U] [LinearOrder U] [Fintype V] {W : U → Type*}
variable [∀ u, Fintype (W u)] [∀ u, LinearOrder (W u)]
variable {F : SimpleGraph U} {T : ∀ u, SimpleGraph (W u)}
variable [∀ u, LinearOrder (W u ⊕ OrientedEdge (T u))]
variable {port : ∀ u, U → W u} {G : SimpleGraph V}

structure EvenTreeCellLinks (F : SimpleGraph U) (T : ∀ u, SimpleGraph (W u))
    (port : ∀ u, U → W u) (G : SimpleGraph V) where
  cell : ∀ u, GraphSubdivisionModel (T u) G
  even : ∀ u e, Even ((cell u).edgePath e).walk.length
  disjoint : Pairwise (fun u v => Disjoint (cell u).vertexSet (cell v).vertexSet)
  link : OrientedEdge F → GraphPath G
  odd : ∀ e, Odd (link e).walk.length
  source_eq : ∀ e, (link e).source = (cell e.lo).branchVertex (port e.lo e.hi)
  target_eq : ∀ e, (link e).target = (cell e.hi).branchVertex (port e.hi e.lo)
  link_disjoint : Pairwise (fun e f => Disjoint (link e).vertexSet (link f).vertexSet)
  clean : ∀ e u x, x ∈ (link e).vertexSet → x ∈ (cell u).vertexSet →
    x = (link e).source ∨ x = (link e).target

namespace EvenTreeCellLinks
variable (C : EvenTreeCellLinks F T port G)

def toTreeCellLinks : TreeCellLinks F T port G where
  cell := fun u => (C.cell u).incidenceSubdivisionModel
    ((C.cell u).edgePath_length_two_le_of_even (C.even u))
  disjoint := by
    intro u v huv
    exact (C.disjoint huv).mono
      ((C.cell u).incidenceSubdivisionModel_vertexSet_subset _)
      ((C.cell v).incidenceSubdivisionModel_vertexSet_subset _)
  link := C.link
  source_eq := C.source_eq
  target_eq := C.target_eq
  link_disjoint := C.link_disjoint
  clean := fun e u x hx hu => C.clean e u x hx
    ((C.cell u).incidenceSubdivisionModel_vertexSet_subset _ hu)

theorem toTreeCellLinks_odd (u : U) (e : OrientedEdge (treeIncidenceGraph (T u))) :
    Odd ((C.toTreeCellLinks.cell u).edgePath e).walk.length :=
  (C.cell u).incidencePath_odd (C.even u) e

include C in
theorem hasIndependenceDefectAtLeast [LinearOrder (TreeExpansionVertex T)]
    (hT : ∀ u, (T u).IsTree) (r : ℕ) (hF : 2 * F.indepNum + r ≤ Fintype.card U) :
    HasIndependenceDefectAtLeast r G :=
  TreeCellLinks.hasIndependenceDefectAtLeast C.toTreeCellLinks
    C.toTreeCellLinks_odd C.odd hT r hF

end EvenTreeCellLinks
end
end Erdos73
