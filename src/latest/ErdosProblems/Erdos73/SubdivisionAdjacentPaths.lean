import ErdosProblems.Erdos73.SubdivisionConnectivity

/-! Orient a subdivision corridor along either orientation of its pattern edge. -/

namespace Erdos73.GraphSubdivisionModel
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {W V : Type*} [Fintype W] [LinearOrder W]
variable {H : SimpleGraph W} {G : SimpleGraph V}

def pathAlongAdj (S : GraphSubdivisionModel H G) {u v : W} (h : H.Adj u v) : GraphPath G :=
  let e := OrientedEdge.ofAdj h
  if e.lo = u then S.edgePath e else (S.edgePath e).reverse

theorem pathAlongAdj_source (S : GraphSubdivisionModel H G) {u v : W} (h : H.Adj u v) :
    (S.pathAlongAdj h).source = S.branchVertex u := by
  rcases OrientedEdge.ofAdj_endpoints h with he | he
  · simp only [pathAlongAdj, he.1, ↓reduceIte, S.source_eq]
  · have hvu : v ≠ u := h.ne.symm
    simp only [pathAlongAdj, he.1, if_neg hvu, GraphPath.reverse_source, S.target_eq, he.2]

theorem pathAlongAdj_target (S : GraphSubdivisionModel H G) {u v : W} (h : H.Adj u v) :
    (S.pathAlongAdj h).target = S.branchVertex v := by
  rcases OrientedEdge.ofAdj_endpoints h with he | he
  · simp only [pathAlongAdj, he.1, ↓reduceIte, S.target_eq, he.2]
  · have hvu : v ≠ u := h.ne.symm
    simp only [pathAlongAdj, he.1, if_neg hvu, GraphPath.reverse_target, S.source_eq]

theorem pathAlongAdj_vertexSet (S : GraphSubdivisionModel H G) {u v : W} (h : H.Adj u v) :
    (S.pathAlongAdj h).vertexSet = (S.edgePath (OrientedEdge.ofAdj h)).vertexSet := by
  dsimp only [pathAlongAdj]
  split_ifs <;> simp only [GraphPath.reverse_vertexSet]

theorem pathAlongAdj_inter_supportOver (S : GraphSubdivisionModel H G)
    {u v : W} (h : H.Adj u v) (T : Finset W) (hu : u ∉ T)
    {x : V} (hx : x ∈ (S.pathAlongAdj h).vertexSet) (hxT : x ∈ S.supportOver T) :
    x = S.branchVertex v := by
  rw [S.pathAlongAdj_vertexSet] at hx
  let e := OrientedEdge.ofAdj h
  have he := OrientedEdge.ofAdj_endpoints h
  have huf : u = e.lo ∨ u = e.hi := he.elim
    (fun he => Or.inl he.1.symm) (fun he => Or.inr he.2.symm)
  have hend : ∀ w, (w = e.lo ∨ w = e.hi) → w = u ∨ w = v := by
    intro w hw
    rcases he with he | he <;> rcases hw with hw | hw
    · exact Or.inl (hw.trans he.1)
    · exact Or.inr (hw.trans he.2)
    · exact Or.inr (hw.trans he.1)
    · exact Or.inl (hw.trans he.2)
  rcases (S.mem_supportOver T x).mp hxT with ⟨w, hwT, hwx⟩ | ⟨f, hflo, hfhi, hxf⟩
  · have hw := S.branch_on_path e w (hwx ▸ hx)
    rcases hend w hw with rfl | rfl
    · exact (hu hwT).elim
    · exact hwx.symm
  · have hef : e ≠ f := by
      intro hef
      have hue : u ∈ T := huf.elim (fun hh => hh ▸ (hef ▸ hflo))
        (fun hh => hh ▸ (hef ▸ hfhi))
      exact hu hue
    obtain ⟨w, hxw, hwe, hwf⟩ := S.intersection hef x hx hxf
    have hwT : w ∈ T := hwf.elim (fun hh => hh ▸ hflo) (fun hh => hh ▸ hfhi)
    rcases hend w hwe with rfl | rfl
    · exact (hu hwT).elim
    · exact hxw

end
end Erdos73.GraphSubdivisionModel
