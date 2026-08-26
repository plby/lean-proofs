import ErdosProblems.Erdos73.RegionLinkDefect

/-! Convert endpoint ports on oriented edges to a consistent vertex-pair port function. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset

variable {U W : Type*} [Fintype U] [LinearOrder U] {F : SimpleGraph U}

theorem OrientedEdge.ofAdj_adj (e : OrientedEdge F) : OrientedEdge.ofAdj e.adj = e :=
  OrientedEdge.eq_of_sym2_eq (OrientedEdge.ofAdj_sym2 e.adj)

theorem OrientedEdge.ofAdj_symm {u v : U} (h : F.Adj u v) :
    OrientedEdge.ofAdj h.symm = OrientedEdge.ofAdj h := by
  apply OrientedEdge.eq_of_sym2_eq
  rw [OrientedEdge.ofAdj_sym2, OrientedEdge.ofAdj_sym2, Sym2.eq_swap]

def edgePortAssignment (s t : OrientedEdge F → W) (defaultPort : U → W) (u v : U) : W :=
  if h : F.Adj u v then
    if u = (OrientedEdge.ofAdj h).lo then s (OrientedEdge.ofAdj h) else t (OrientedEdge.ofAdj h)
  else defaultPort u

theorem edgePortAssignment_lo (s t : OrientedEdge F → W) (defaultPort : U → W)
    (e : OrientedEdge F) : edgePortAssignment s t defaultPort e.lo e.hi = s e := by
  simp only [edgePortAssignment, dif_pos e.adj, OrientedEdge.ofAdj_adj, ite_true]

theorem edgePortAssignment_hi (s t : OrientedEdge F → W) (defaultPort : U → W)
    (e : OrientedEdge F) : edgePortAssignment s t defaultPort e.hi e.lo = t e := by
  rw [edgePortAssignment, dif_pos e.adj.symm]
  have he : OrientedEdge.ofAdj e.adj.symm = e :=
    (OrientedEdge.ofAdj_symm e.adj).trans (OrientedEdge.ofAdj_adj e)
  rw [he, if_neg e.adj.ne.symm]

theorem edgePortAssignment_mem [DecidableEq W]
    (R : U → Finset W) (s t : OrientedEdge F → W) (defaultPort : U → W)
    (hs : ∀ e, s e ∈ R e.lo) (ht : ∀ e, t e ∈ R e.hi)
    (hd : ∀ u, defaultPort u ∈ R u) (u v : U) :
    edgePortAssignment s t defaultPort u v ∈ R u := by
  by_cases huv : F.Adj u v
  · rw [edgePortAssignment, dif_pos huv]
    rcases OrientedEdge.ofAdj_endpoints huv with he | he
    · rw [if_pos he.1.symm]
      simpa only [he.1] using hs (OrientedEdge.ofAdj huv)
    · have hn : u ≠ (OrientedEdge.ofAdj huv).lo := by rw [he.1]; exact huv.ne
      rw [if_neg hn]
      simpa only [he.2] using ht (OrientedEdge.ofAdj huv)
  · rw [edgePortAssignment, dif_neg huv]
    exact hd u

end
end Erdos73
