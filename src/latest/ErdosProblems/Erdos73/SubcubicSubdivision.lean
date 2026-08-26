/- Constructing an actual subdivision of every subcubic minor pattern. -/
import ErdosProblems.Erdos73.SubcubicBranchArms

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph
variable {W V : Type*} [Fintype W] [LinearOrder W]
variable {H : SimpleGraph W} {G : SimpleGraph V}

/-- A subdivision with actual simple edge paths. Distinct edge paths
meet only at branch vertices corresponding to common pattern endpoints. -/
structure GraphSubdivisionModel (H : SimpleGraph W) (G : SimpleGraph V) where
  branchVertex : W → V
  injective : Function.Injective branchVertex
  edgePath : OrientedEdge H → GraphPath G
  source_eq : ∀ e, (edgePath e).source = branchVertex e.lo
  target_eq : ∀ e, (edgePath e).target = branchVertex e.hi
  branch_on_path : ∀ e w, branchVertex w ∈ (edgePath e).vertexSet → w = e.lo ∨ w = e.hi
  intersection : ∀ ⦃e f⦄, e ≠ f → ∀ v,
    v ∈ (edgePath e).vertexSet → v ∈ (edgePath f).vertexSet →
    ∃ w, v = branchVertex w ∧ (w = e.lo ∨ w = e.hi) ∧ (w = f.lo ∨ w = f.hi)

def SubcubicBranchArms.toSubdivisionModel {M : MinorModel H G} (A : SubcubicBranchArms M) :
    GraphSubdivisionModel H G where
  branchVertex := A.center
  injective := A.center_injective
  edgePath := A.edgePath
  source_eq := A.edgePath_source
  target_eq := A.edgePath_target
  branch_on_path := fun _ _ => A.branchVertex_on_edgePath
  intersection := fun _ _ hef _ => A.edgePaths_intersection hef

/-- The branch vertices and edge paths remain in their original minor
branches, providing the support data needed for later orientation transport. -/
theorem exists_subdivisionModel_of_subcubic_minor (M : MinorModel H G)
    (hdeg : ∀ w, H.degree w ≤ 3) :
    ∃ S : GraphSubdivisionModel H G,
      (∀ w, S.branchVertex w ∈ M.branchSet w) ∧
      ∀ e, (S.edgePath e).vertexSet ⊆ M.branchSet e.lo ∪ M.branchSet e.hi := by
  obtain ⟨A⟩ := exists_subcubicBranchArms M hdeg
  exact ⟨A.toSubdivisionModel, A.center_mem, A.edgePath_subset_branches⟩

end
end Erdos73
