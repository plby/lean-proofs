import ErdosProblems.Erdos73.SubdivisionRestriction

/-! Supports of subdivision regions and their preservation under restriction. -/

namespace Erdos73.GraphSubdivisionModel
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {W V : Type*} [Fintype W] [LinearOrder W]
variable {H : SimpleGraph W} {G : SimpleGraph V}

def supportOver (S : GraphSubdivisionModel H G) (T : Finset W) : Finset V :=
  T.image S.branchVertex ∪ (Finset.univ.filter (fun e : OrientedEdge H =>
    e.lo ∈ T ∧ e.hi ∈ T)).biUnion (fun e => (S.edgePath e).vertexSet)

theorem mem_supportOver (S : GraphSubdivisionModel H G) (T : Finset W) (v : V) :
    v ∈ S.supportOver T ↔ (∃ w ∈ T, S.branchVertex w = v) ∨
      ∃ e : OrientedEdge H, e.lo ∈ T ∧ e.hi ∈ T ∧ v ∈ (S.edgePath e).vertexSet := by
  simp only [supportOver, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_univ, true_and]
  aesop

def vertexSet (S : GraphSubdivisionModel H G) : Finset V := S.supportOver Finset.univ

theorem mem_vertexSet (S : GraphSubdivisionModel H G) (v : V) :
    v ∈ S.vertexSet ↔ (∃ w, S.branchVertex w = v) ∨
      ∃ e : OrientedEdge H, v ∈ (S.edgePath e).vertexSet := by
  simp only [vertexSet, mem_supportOver, Finset.mem_univ, true_and]

theorem supportOver_disjoint (S : GraphSubdivisionModel H G) {T R : Finset W}
    (hTR : Disjoint T R) : Disjoint (S.supportOver T) (S.supportOver R) := by
  apply Finset.disjoint_left.mpr
  intro v hvT hvR
  rcases (S.mem_supportOver T v).mp hvT with ⟨u, huT, hu⟩ | ⟨e, heT, heT', hve⟩
  · rcases (S.mem_supportOver R v).mp hvR with ⟨w, hwR, hw⟩ | ⟨d, hdR, hdR', hvd⟩
    · exact Finset.disjoint_left.mp hTR huT ((S.injective (hu.trans hw.symm)) ▸ hwR)
    · rw [← hu] at hvd
      rcases S.branch_on_path d u hvd with h | h
      · exact Finset.disjoint_left.mp hTR huT (h ▸ hdR)
      · exact Finset.disjoint_left.mp hTR huT (h ▸ hdR')
  · rcases (S.mem_supportOver R v).mp hvR with ⟨w, hwR, hw⟩ | ⟨d, hdR, hdR', hvd⟩
    · rw [← hw] at hve
      rcases S.branch_on_path e w hve with h | h
      · exact Finset.disjoint_left.mp hTR (h ▸ heT) hwR
      · exact Finset.disjoint_left.mp hTR (h ▸ heT') hwR
    · by_cases hed : e = d
      · exact Finset.disjoint_left.mp hTR heT (hed ▸ hdR)
      · obtain ⟨w, _, hwe, hwd⟩ := S.intersection hed v hve hvd
        have hwT : w ∈ T := hwe.elim (fun h => h ▸ heT) (fun h => h ▸ heT')
        have hwR : w ∈ R := hwd.elim (fun h => h ▸ hdR) (fun h => h ▸ hdR')
        exact Finset.disjoint_left.mp hTR hwT hwR

variable {U : Type*} [Fintype U] [LinearOrder U] {F : SimpleGraph U}

theorem restrictCopy_vertexSet_subset (S : GraphSubdivisionModel H G) (f : F.Copy H) :
    (S.restrictCopy f).vertexSet ⊆ S.supportOver (Finset.univ.image f) := by
  intro v hv
  rcases ((S.restrictCopy f).mem_vertexSet v).mp hv with ⟨u, hu⟩ | ⟨e, he⟩
  · exact (S.mem_supportOver _ v).mpr (Or.inl
      ⟨f u, Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩, hu⟩)
  · rw [S.restrictCopy_edgePath_vertexSet] at he
    apply (S.mem_supportOver _ v).mpr
    refine Or.inr ⟨OrientedEdge.mapCopy f e, ?_, ?_, he⟩
    · rcases OrientedEdge.mapCopy_endpoints f e with h | h
      · exact Finset.mem_image.mpr ⟨e.lo, Finset.mem_univ _, h.1.symm⟩
      · exact Finset.mem_image.mpr ⟨e.hi, Finset.mem_univ _, h.1.symm⟩
    · rcases OrientedEdge.mapCopy_endpoints f e with h | h
      · exact Finset.mem_image.mpr ⟨e.hi, Finset.mem_univ _, h.2.symm⟩
      · exact Finset.mem_image.mpr ⟨e.lo, Finset.mem_univ _, h.2.symm⟩

theorem restrictCopy_vertexSet_disjoint {U' : Type*} [Fintype U'] [LinearOrder U']
    {F' : SimpleGraph U'} (S : GraphSubdivisionModel H G) (f : F.Copy H) (g : F'.Copy H)
    (h : Disjoint (Finset.univ.image f) (Finset.univ.image g)) :
    Disjoint (S.restrictCopy f).vertexSet (S.restrictCopy g).vertexSet :=
  (S.supportOver_disjoint h).mono (S.restrictCopy_vertexSet_subset f)
    (S.restrictCopy_vertexSet_subset g)

end
end Erdos73.GraphSubdivisionModel
