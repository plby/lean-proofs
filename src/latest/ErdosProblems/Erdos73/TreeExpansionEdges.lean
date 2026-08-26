import ErdosProblems.Erdos73.TreeExpansion
import ErdosProblems.Erdos73.EdgePathRealization

/-! The internal and external edge indices of a tree expansion. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset

variable {U : Type*} [Fintype U] [LinearOrder U] {W : U → Type*}
variable [∀ u, Fintype (W u)] [∀ u, LinearOrder (W u)]
variable (F : SimpleGraph U) (T : ∀ u, SimpleGraph (W u))
variable [∀ u, LinearOrder (W u ⊕ OrientedEdge (T u))]

abbrev TreeExpansionEdgeIndex :=
  (Σ u, OrientedEdge (treeIncidenceGraph (T u))) ⊕ OrientedEdge F

def treeExpansionEdgeLeft (port : ∀ u, U → W u) :
    TreeExpansionEdgeIndex F T → TreeExpansionVertex T
  | Sum.inl ⟨u, e⟩ => ⟨u, e.lo⟩
  | Sum.inr e => ⟨e.lo, Sum.inl (port e.lo e.hi)⟩

def treeExpansionEdgeRight (port : ∀ u, U → W u) :
    TreeExpansionEdgeIndex F T → TreeExpansionVertex T
  | Sum.inl ⟨u, e⟩ => ⟨u, e.hi⟩
  | Sum.inr e => ⟨e.hi, Sum.inl (port e.hi e.lo)⟩

theorem treeExpansionEdge_covers [LinearOrder (TreeExpansionVertex T)]
    (port : ∀ u, U → W u) (e : OrientedEdge (treeExpansionGraph F T port)) :
    ∃ i, s(treeExpansionEdgeLeft F T port i, treeExpansionEdgeRight F T port i) =
      s(e.lo, e.hi) := by
  rcases e.adj with h | h
  · obtain ⟨u, h⟩ := SimpleGraph.iSup_adj.mp h
    obtain ⟨a, b, hab, ha, hb⟩ := h.2
    let d := OrientedEdge.ofAdj hab
    refine ⟨Sum.inl ⟨u, d⟩, ?_⟩
    change s(Sigma.mk u d.lo, Sigma.mk u d.hi) = s(e.lo, e.hi)
    rcases OrientedEdge.ofAdj_endpoints hab with hd | hd
    · rw [hd.1, hd.2, ha, hb]
    · rw [hd.1, hd.2, ha, hb, Sym2.eq_swap]
  · obtain ⟨u, v, huv, ha, hb⟩ := h
    let d := OrientedEdge.ofAdj huv
    refine ⟨Sum.inr d, ?_⟩
    change s(⟨d.lo, Sum.inl (port d.lo d.hi)⟩, ⟨d.hi, Sum.inl (port d.hi d.lo)⟩) =
      s(e.lo, e.hi)
    rcases OrientedEdge.ofAdj_endpoints huv with hd | hd
    · rw [hd.1, hd.2, ← ha, ← hb]
    · rw [hd.1, hd.2, ← ha, ← hb, Sym2.eq_swap]

end
end Erdos73
