/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58GroupedSmallForest

/-!
# Exact endpoint counts of a dynamically embedded forest

Global injectivity makes the oriented component images disjoint. Thus the
actual used cardinality equals its source side load, which is essential
when propagating the Part-3 residual trichotomy.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoLemma58GroupedSmallForest

open Finset SimpleGraph Erdos547b.RegularPair

variable {b : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
variable {F : OrderedRootedForest b} {H : SimpleGraph V}
variable {parent : Fin b → V} {orient : Fin b → Fin 2 ≃ Fin 2}
variable {available : Fin 2 → Finset V}

def DynamicAttachedForestEmbedding.used (E : DynamicAttachedForestEmbedding F H parent orient available)
    (c : Fin 2) : Finset V :=
  Finset.univ.biUnion fun i => orientedCopyImage (F.tree i) (F.isTree i) (F.root i)
    (orient i) H (E.embedding.copy i) c

theorem DynamicAttachedForestEmbedding.used_subset
    (E : DynamicAttachedForestEmbedding F H parent orient available) (c : Fin 2) :
    E.used c ⊆ available c := by
  intro v hv
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
  exact orientedCopyImage_subset (F.tree i) (F.isTree i) (F.root i) (orient i) H
    (E.embedding.copy i) available (E.map_side i) c hi

/-- Actual image cardinality, not just an upper bound by source mass. -/
theorem DynamicAttachedForestEmbedding.card_used
    (E : DynamicAttachedForestEmbedding F H parent orient available) (c : Fin 2) :
    (E.used c).card = sideLoad F orient c := by
  unfold DynamicAttachedForestEmbedding.used
  rw [Finset.card_biUnion]
  · exact Finset.sum_congr rfl (fun i _ => card_orientedCopyImage
      (F.tree i) (F.isTree i) (F.root i) (orient i) H (E.embedding.copy i) c)
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hv
    obtain ⟨d, _, hd⟩ := Finset.mem_image.mp hw
    have heq : (⟨i, a⟩ : Σ k, Fin (F.size k)) = ⟨j, d⟩ :=
      E.embedding.injective (ha.trans hd.symm)
    exact hij (congrArg Sigma.fst heq)

theorem DynamicAttachedForestEmbedding.card_residual
    (E : DynamicAttachedForestEmbedding F H parent orient available) (c : Fin 2) :
    (available c \ E.used c).card = (available c).card - sideLoad F orient c := by
  rw [Finset.card_sdiff_of_subset (E.used_subset c), E.card_used c]

end Erdos547b.ZhaoLemma58GroupedSmallForest

#print axioms Erdos547b.ZhaoLemma58GroupedSmallForest.DynamicAttachedForestEmbedding.used_subset
#print axioms Erdos547b.ZhaoLemma58GroupedSmallForest.DynamicAttachedForestEmbedding.card_used
#print axioms Erdos547b.ZhaoLemma58GroupedSmallForest.DynamicAttachedForestEmbedding.card_residual
