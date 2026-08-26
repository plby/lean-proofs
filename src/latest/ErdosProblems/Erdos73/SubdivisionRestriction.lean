import ErdosProblems.Erdos73.OrientedEdgeMaps

/-! Restrict actual subdivision models along ordinary graph copies, preserving all supports. -/

namespace Erdos73.GraphSubdivisionModel
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Erdos73Infrastructure.SimpleGraph

variable {U W V : Type*} [Fintype U] [LinearOrder U] [Fintype W] [LinearOrder W]
variable {F : SimpleGraph U} {H : SimpleGraph W} {G : SimpleGraph V}

def pathAlongCopy (S : GraphSubdivisionModel H G) (f : F.Copy H) (e : OrientedEdge F) :
    GraphPath G :=
  if f e.lo < f e.hi then S.edgePath (OrientedEdge.mapCopy f e)
  else (S.edgePath (OrientedEdge.mapCopy f e)).reverse

theorem pathAlongCopy_source (S : GraphSubdivisionModel H G) (f : F.Copy H) (e : OrientedEdge F) :
    (S.pathAlongCopy f e).source = S.branchVertex (f e.lo) := by
  unfold pathAlongCopy
  split_ifs with hh
  · rw [S.source_eq]
    exact congrArg S.branchVertex (min_eq_left hh.le)
  · rw [GraphPath.reverse_source, S.target_eq]
    exact congrArg S.branchVertex (max_eq_left (le_of_not_gt hh))

theorem pathAlongCopy_target (S : GraphSubdivisionModel H G) (f : F.Copy H) (e : OrientedEdge F) :
    (S.pathAlongCopy f e).target = S.branchVertex (f e.hi) := by
  unfold pathAlongCopy
  split_ifs with hh
  · rw [S.target_eq]
    exact congrArg S.branchVertex (max_eq_right hh.le)
  · rw [GraphPath.reverse_target, S.source_eq]
    exact congrArg S.branchVertex (min_eq_right (le_of_not_gt hh))

theorem pathAlongCopy_vertexSet (S : GraphSubdivisionModel H G) (f : F.Copy H) (e : OrientedEdge F) :
    (S.pathAlongCopy f e).vertexSet = (S.edgePath (OrientedEdge.mapCopy f e)).vertexSet := by
  unfold pathAlongCopy
  split_ifs <;> simp only [GraphPath.reverse_vertexSet]

def restrictCopy (S : GraphSubdivisionModel H G) (f : F.Copy H) : GraphSubdivisionModel F G where
  branchVertex := S.branchVertex ∘ f
  injective := S.injective.comp f.injective
  edgePath := S.pathAlongCopy f
  source_eq := S.pathAlongCopy_source f
  target_eq := S.pathAlongCopy_target f
  branch_on_path := by
    intro e u hu
    rw [S.pathAlongCopy_vertexSet] at hu
    have hh := S.branch_on_path (OrientedEdge.mapCopy f e) (f u) hu
    rw [OrientedEdge.mapCopy_endpoint_iff] at hh
    exact hh.imp (fun he => f.injective he) (fun he => f.injective he)
  intersection := by
    intro e d hed v hve hvd
    rw [S.pathAlongCopy_vertexSet] at hve hvd
    obtain ⟨w, hv, hwe, hwd⟩ := S.intersection ((OrientedEdge.mapCopy_injective f).ne hed) v hve hvd
    rw [OrientedEdge.mapCopy_endpoint_iff] at hwe hwd
    rcases hwe with hwe | hwe
    · refine ⟨e.lo, ?_, Or.inl rfl, ?_⟩
      · simpa only [Function.comp_apply, hwe] using hv
      · rw [hwe] at hwd
        exact hwd.imp (fun he => f.injective he) (fun he => f.injective he)
    · refine ⟨e.hi, ?_, Or.inr rfl, ?_⟩
      · simpa only [Function.comp_apply, hwe] using hv
      · rw [hwe] at hwd
        exact hwd.imp (fun he => f.injective he) (fun he => f.injective he)

@[simp] theorem restrictCopy_branchVertex (S : GraphSubdivisionModel H G) (f : F.Copy H) (u : U) :
    (S.restrictCopy f).branchVertex u = S.branchVertex (f u) := rfl

theorem restrictCopy_edgePath_vertexSet (S : GraphSubdivisionModel H G) (f : F.Copy H)
    (e : OrientedEdge F) : ((S.restrictCopy f).edgePath e).vertexSet =
      (S.edgePath (OrientedEdge.mapCopy f e)).vertexSet := S.pathAlongCopy_vertexSet f e

end
end Erdos73.GraphSubdivisionModel
