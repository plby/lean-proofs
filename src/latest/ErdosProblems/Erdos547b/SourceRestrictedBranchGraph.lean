/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceRestrictedCutCoordinates

/-!
# Exact graph transport for a retained branch family
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceRestrictedCutCoordinates

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59Part2Full Erdos547b.ZhaoClaim616SourceBridge

variable {r b : ℕ} (F : OrderedBranchForest r b) (keep : Finset (Fin b))

theorem coordinateInclusion_adj_iff (x y : (OrderedBranchForest.restrict F keep).Vertex) :
    F.graph.Adj (coordinateInclusion F keep x) (coordinateInclusion F keep y) ↔
      (OrderedBranchForest.restrict F keep).graph.Adj x y := by
  rcases x with i | ⟨i, a⟩ <;> rcases y with j | ⟨j, d⟩
  · rfl
  · rfl
  · rfl
  · constructor
    · rintro ⟨h, hadj⟩
      have hij : i = j := (OrderedBranchForest.selectedEquiv keep).injective (Subtype.ext h)
      subst j
      exact ⟨rfl, hadj⟩
    · rintro ⟨h, hadj⟩
      change i = j at h
      subst j
      exact ⟨rfl, hadj⟩

def restrictedGraphIso : (OrderedBranchForest.restrict F keep).graph ≃g
    F.graph.induce {x | retained F keep x} where
  toEquiv := coordinateEquiv F keep
  map_rel_iff' := coordinateInclusion_adj_iff F keep _ _

end Erdos547b.ZhaoSourceRestrictedCutCoordinates

#print axioms Erdos547b.ZhaoSourceRestrictedCutCoordinates.coordinateInclusion_adj_iff
#print axioms Erdos547b.ZhaoSourceRestrictedCutCoordinates.restrictedGraphIso
