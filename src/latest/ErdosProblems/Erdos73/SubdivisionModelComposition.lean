import ErdosProblems.Erdos73.SubdivisionSupportIntersection
import ErdosProblems.Erdos73.SubdivisionPaths

/-! Compose actual simple-path subdivision models, preserving branch intersections. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

theorem OrientedEdge.common_endpoint_unique {U : Type*} [Fintype U] [LinearOrder U]
    {F : SimpleGraph U} {e f : OrientedEdge F} (hef : e ≠ f) {u v : U}
    (hue : u = e.lo ∨ u = e.hi) (huf : u = f.lo ∨ u = f.hi)
    (hve : v = e.lo ∨ v = e.hi) (hvf : v = f.lo ∨ v = f.hi) : u = v := by
  by_contra huv
  apply hef
  apply OrientedEdge.eq_of_sym2_eq
  apply Sym2.eq_iff.mpr
  rcases hue with hue | hue <;> rcases huf with huf | huf <;>
    rcases hve with hve | hve <;> rcases hvf with hvf | hvf <;> aesop

namespace GraphSubdivisionModel

variable {U W V : Type*} [Fintype U] [LinearOrder U] [Fintype W] [LinearOrder W]
variable {F : SimpleGraph U} {H : SimpleGraph W} {G : SimpleGraph V}

def expandPath (S : GraphSubdivisionModel H G) (P : GraphPath H) : GraphPath G :=
  (S.exists_path_with_walkSupport P.walk P.isPath).choose

theorem expandPath_source (S : GraphSubdivisionModel H G) (P : GraphPath H) :
    (S.expandPath P).source = S.branchVertex P.source :=
  (S.exists_path_with_walkSupport P.walk P.isPath).choose_spec.1

theorem expandPath_target (S : GraphSubdivisionModel H G) (P : GraphPath H) :
    (S.expandPath P).target = S.branchVertex P.target :=
  (S.exists_path_with_walkSupport P.walk P.isPath).choose_spec.2.1

theorem expandPath_vertexSet (S : GraphSubdivisionModel H G) (P : GraphPath H) :
    (S.expandPath P).vertexSet = S.walkSupport P.walk :=
  (S.exists_path_with_walkSupport P.walk P.isPath).choose_spec.2.2

theorem expandPath_subset_supportOver (S : GraphSubdivisionModel H G) (P : GraphPath H) :
    (S.expandPath P).vertexSet ⊆ S.supportOver P.vertexSet := by
  rw [S.expandPath_vertexSet]
  have he : P.walk.support.toFinset = P.vertexSet := by
    ext w
    simp only [GraphPath.vertexSet, List.mem_toFinset]
  exact he ▸ S.walkSupport_subset_supportOver P.walk

def compose (S : GraphSubdivisionModel H G) (T : GraphSubdivisionModel F H) :
    GraphSubdivisionModel F G where
  branchVertex := S.branchVertex ∘ T.branchVertex
  injective := S.injective.comp T.injective
  edgePath := fun e => S.expandPath (T.edgePath e)
  source_eq := fun e => (S.expandPath_source _).trans (congrArg S.branchVertex (T.source_eq e))
  target_eq := fun e => (S.expandPath_target _).trans (congrArg S.branchVertex (T.target_eq e))
  branch_on_path := by
    intro e u hu
    have hh := S.expandPath_subset_supportOver (T.edgePath e) hu
    exact T.branch_on_path e u ((S.branch_mem_supportOver_iff _ _).mp hh)
  intersection := by
    intro e f hef x hxe hxf
    have hxE := S.expandPath_subset_supportOver (T.edgePath e) hxe
    have hxF := S.expandPath_subset_supportOver (T.edgePath f) hxf
    have hxS : x ∈ S.vertexSet := S.supportOver_mono (subset_univ _) hxE
    obtain ⟨z, _, hz⟩ := S.exists_support_anchor x hxS
    obtain ⟨u, hzu, hue, huf⟩ := T.intersection hef z (hz _ hxE) (hz _ hxF)
    have hinter : (T.edgePath e).vertexSet ∩ (T.edgePath f).vertexSet ⊆ {T.branchVertex u} := by
      intro y hy
      obtain ⟨v, hyv, hve, hvf⟩ := T.intersection hef y (mem_inter.mp hy).1 (mem_inter.mp hy).2
      have huv := OrientedEdge.common_endpoint_unique hef hue huf hve hvf
      exact mem_singleton.mpr (hyv.trans (congrArg T.branchVertex huv.symm))
    have hh := S.supportOver_inter_subset_singleton hinter (mem_inter.mpr ⟨hxE, hxF⟩)
    exact ⟨u, mem_singleton.mp hh, hue, huf⟩

theorem compose_branchVertex (S : GraphSubdivisionModel H G) (T : GraphSubdivisionModel F H)
    (u : U) : (S.compose T).branchVertex u = S.branchVertex (T.branchVertex u) := rfl

theorem compose_vertexSet_subset (S : GraphSubdivisionModel H G) (T : GraphSubdivisionModel F H) :
    (S.compose T).vertexSet ⊆ S.vertexSet := by
  intro x hx
  rcases ((S.compose T).mem_vertexSet x).mp hx with ⟨u, rfl⟩ | ⟨e, hx⟩
  · exact (S.mem_vertexSet _).mpr (Or.inl ⟨T.branchVertex u, rfl⟩)
  · exact S.supportOver_mono (subset_univ _) (S.expandPath_subset_supportOver (T.edgePath e) hx)

end GraphSubdivisionModel
end
end Erdos73
