/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceRestrictedBranchGraph
import ErdosProblems.Erdos547b.SourceReconnectedGraph

/-!
# Restriction commutes with restoring the surviving cut edges
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceRestrictedCutCoordinates

open Finset SimpleGraph Erdos547b.RegularPair Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoClaim616SourceBridge Erdos547b.ZhaoSourceReconnectedGraph
open Erdos547b.ZhaoSourceGlobalPrefixState

variable {r b k : ℕ} (F : OrderedBranchForest r b) (keep : Finset (Fin b))
variable (rootSide : Fin r → Fin 2) (locate : Fin b → Fin 2 × Fin k)
variable (L : CutSource F.branches F.owner rootSide locate)
variable (hparent : ∀ i hi, retained F keep (L.parent i hi))

theorem reconnected_adj_inclusion_iff (x y : (OrderedBranchForest.restrict F keep).Vertex) :
    (reconnectedGraph F L).Adj (coordinateInclusion F keep x) (coordinateInclusion F keep y) ↔
      (reconnectedGraph (OrderedBranchForest.restrict F keep)
        (restrictCutSource F keep rootSide locate L hparent)).Adj x y := by
  constructor
  · intro h
    rcases h with h | ⟨i, hi, h | h⟩
    · exact Or.inl ((coordinateInclusion_adj_iff F keep x y).mp h)
    · exact Or.inr ⟨i, hi, Or.inl ⟨coordinateInclusion_injective F keep
        (h.1.trans (coordinateInclusion_lower F keep _ (hparent i hi)).symm),
        coordinateInclusion_injective F keep h.2⟩⟩
    · exact Or.inr ⟨i, hi, Or.inr ⟨coordinateInclusion_injective F keep
        (h.1.trans (coordinateInclusion_lower F keep _ (hparent i hi)).symm),
        coordinateInclusion_injective F keep h.2⟩⟩
  · intro h
    rcases h with h | ⟨i, hi, h | h⟩
    · exact Or.inl ((coordinateInclusion_adj_iff F keep x y).mpr h)
    · rcases h with ⟨rfl, rfl⟩
      exact Or.inr ⟨i, hi, Or.inl ⟨coordinateInclusion_lower F keep _ (hparent i hi), rfl⟩⟩
    · rcases h with ⟨rfl, rfl⟩
      exact Or.inr ⟨i, hi, Or.inr ⟨coordinateInclusion_lower F keep _ (hparent i hi), rfl⟩⟩

def restrictedReconnectedGraphIso :
    reconnectedGraph (OrderedBranchForest.restrict F keep) (restrictCutSource F keep rootSide locate L hparent) ≃g
      (reconnectedGraph F L).induce {x | retained F keep x} where
  toEquiv := coordinateEquiv F keep
  map_rel_iff' := reconnected_adj_inclusion_iff F keep rootSide locate L hparent _ _

end Erdos547b.ZhaoSourceRestrictedCutCoordinates

#print axioms Erdos547b.ZhaoSourceRestrictedCutCoordinates.restrictedReconnectedGraphIso
