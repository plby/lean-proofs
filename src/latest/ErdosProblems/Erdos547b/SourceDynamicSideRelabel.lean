/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceDynamicUsedCard

/-!
# Relabeling physical sides without changing actual graph copies

Appendix A.2 orders the current live cardinalities locally. Composing
orientations with that side permutation restores the original endpoints,
and the exact used sets are transported by the same permutation.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoLemma58GroupedSmallForest

open Finset SimpleGraph Erdos547b.RegularPair

variable {b : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
variable {F : OrderedRootedForest b} {H : SimpleGraph V}
variable {parent : Fin b → V} {orient : Fin b → Fin 2 ≃ Fin 2}
variable {available : Fin 2 → Finset V}

def DynamicAttachedForestEmbedding.relabelSides (side : Fin 2 ≃ Fin 2)
    (E : DynamicAttachedForestEmbedding F H parent orient (fun c => available (side c))) :
    DynamicAttachedForestEmbedding F H parent (fun i => (orient i).trans side) available where
  embedding := E.embedding
  attach := E.attach
  map_side := E.map_side

theorem DynamicAttachedForestEmbedding.used_relabelSides (side : Fin 2 ≃ Fin 2)
    (E : DynamicAttachedForestEmbedding F H parent orient (fun c => available (side c))) (c : Fin 2) :
    ((E.relabelSides side).used (side c)) = E.used c := by
  unfold DynamicAttachedForestEmbedding.used DynamicAttachedForestEmbedding.relabelSides
  apply Finset.biUnion_congr rfl
  intro i _
  unfold orientedCopyImage
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.trans_apply, side.injective.eq_iff]

end Erdos547b.ZhaoLemma58GroupedSmallForest

#print axioms Erdos547b.ZhaoLemma58GroupedSmallForest.DynamicAttachedForestEmbedding.relabelSides
#print axioms Erdos547b.ZhaoLemma58GroupedSmallForest.DynamicAttachedForestEmbedding.used_relabelSides
