import ErdosProblems.Erdos73.EvenTreeCellLinks
import ErdosProblems.Erdos73.SubdivisionTreeRegions

/-! Connected pattern regions and clean odd links transfer full independence defect. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {U W V : Type*} [Fintype U] [LinearOrder U]
variable [Fintype W] [LinearOrder W] [Fintype V]
variable {F : SimpleGraph U} {H : SimpleGraph W} {G : SimpleGraph V}

theorem hasIndependenceDefectAtLeast_of_regions_and_links
    (S : GraphSubdivisionModel H G) (col : BipartiteColoringOn G S.vertexSet)
    (b : Bool) (hb : ∀ w, col.color (S.branchVertex w) = b)
    (R : U → Finset W) (hR : Pairwise (fun u v => Disjoint (R u) (R v)))
    (hconn : ∀ u, (H.induce (R u : Set W)).Connected)
    (port : U → U → W) (hport : ∀ u v, port u v ∈ R u)
    (P : OrientedEdge F → GraphPath G)
    (hs : ∀ e, (P e).source = S.branchVertex (port e.lo e.hi))
    (ht : ∀ e, (P e).target = S.branchVertex (port e.hi e.lo))
    (hodd : ∀ e, Odd (P e).walk.length)
    (hdis : Pairwise (fun e f => Disjoint (P e).vertexSet (P f).vertexSet))
    (hclean : ∀ e x, x ∈ (P e).vertexSet → x ∈ S.vertexSet →
      x = (P e).source ∨ x = (P e).target)
    (r : ℕ) (hF : 2 * F.indepNum + r ≤ Fintype.card U) :
    HasIndependenceDefectAtLeast r G := by
  have hex (u : U) := S.exists_even_tree_region col b hb (R u) (hconn u)
  choose T hT cells hbranch hsub heven using hex
  let localPort (u v : U) : (R u : Set W) := ⟨port u v, hport u v⟩
  let (u : U) : LinearOrder ((R u : Set W) ⊕ OrientedEdge (T u)) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  let : LinearOrder (TreeExpansionVertex T) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  let C : EvenTreeCellLinks F T localPort G := {
    cell := cells
    even := heven
    disjoint := fun u v huv => (S.supportOver_disjoint (hR huv)).mono (hsub u) (hsub v)
    link := P
    odd := hodd
    source_eq := fun e => (hs e).trans (hbranch e.lo (localPort e.lo e.hi)).symm
    target_eq := fun e => (ht e).trans (hbranch e.hi (localPort e.hi e.lo)).symm
    link_disjoint := hdis
    clean := fun e u x hx hu => hclean e x hx
      (S.supportOver_mono (subset_univ _) (hsub u hu)) }
  exact EvenTreeCellLinks.hasIndependenceDefectAtLeast C hT r hF

end
end Erdos73
