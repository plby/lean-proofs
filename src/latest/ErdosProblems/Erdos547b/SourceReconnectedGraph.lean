/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceRestrictedCutCoordinates

/-!
# The branch forest with its actual recorded cut edges restored
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceReconnectedGraph

open Finset SimpleGraph Erdos547b.RegularPair Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoSourceGlobalPrefixState

variable {r b k : ℕ} (F : OrderedBranchForest r b)
variable {rootSide : Fin r → Fin 2} {locate : Fin b → Fin 2 × Fin k}
variable (L : CutSource F.branches F.owner rootSide locate)

theorem parent_ne_childRoot (i : Fin r) (hi : i.val ≠ 0) : L.parent i hi ≠ Sum.inl i := by
  intro h
  have hb := L.before i hi
  rw [h] at hb
  exact Nat.lt_irrefl i.val hb

def reconnectedGraph : SimpleGraph F.Vertex where
  Adj x y := F.graph.Adj x y ∨ ∃ i hi,
    (x = L.parent i hi ∧ y = Sum.inl i) ∨ (y = L.parent i hi ∧ x = Sum.inl i)
  symm := ⟨by
    intro x y h
    rcases h with h | ⟨i, hi, h | h⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨i, hi, Or.inr h⟩
    · exact Or.inr ⟨i, hi, Or.inl h⟩⟩
  loopless := ⟨by
    intro x h
    rcases h with h | ⟨i, hi, h | h⟩
    · exact F.graph.loopless.irrefl x h
    · exact parent_ne_childRoot F L i hi (h.1.symm.trans h.2)
    · exact parent_ne_childRoot F L i hi (h.1.symm.trans h.2)⟩

def copyOfForestCopy {V : Type*} (H : SimpleGraph V) (f : F.graph.Copy H)
    (hcut : ∀ i hi, H.Adj (f (L.parent i hi)) (f (Sum.inl i))) :
    (reconnectedGraph F L).Copy H where
  toHom := {
    toFun := f
    map_rel' := by
      intro x y h
      rcases h with h | ⟨i, hi, h | h⟩
      · exact f.toHom.map_rel h
      · rcases h with ⟨rfl, rfl⟩
        exact hcut i hi
      · rcases h with ⟨rfl, rfl⟩
        exact (hcut i hi).symm }
  injective' := f.injective

end Erdos547b.ZhaoSourceReconnectedGraph

#print axioms Erdos547b.ZhaoSourceReconnectedGraph.reconnectedGraph
#print axioms Erdos547b.ZhaoSourceReconnectedGraph.copyOfForestCopy
