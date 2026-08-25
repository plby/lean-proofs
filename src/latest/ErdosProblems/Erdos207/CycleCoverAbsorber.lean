/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CycleDecompositionGrouping

/-!
# The path-cover/full-cycle-cover absorber

The graph in this file is fixed once the root type is fixed.  For every
triangle-divisible root graph, the cycle-decomposition and grouping theorems
select the in-sides of exactly the necessary bounded absorbers and give a
triangle decomposition of the fixed graph together with that root graph.
-/

namespace Erdos207

open Finset

noncomputable section

abbrev CycleCoverPathVertex (V : Type*) [Fintype V] :=
  PathCoverVertex V (6 * (Fintype.card V) ^ 2)

abbrev CycleCoverAbsorberVertex (V : Type*) [Fintype V] :=
  FullCycleCoverVertex (CycleCoverPathVertex V)

def cycleCoverRootEmbedding
    (V : Type*) [Fintype V] [DecidableEq V] :
    V ↪ CycleCoverAbsorberVertex V :=
  (pathCoverRootEmbedding
    (X := V) (k := 6 * (Fintype.card V) ^ 2)).trans
      (fullCycleCoverBaseEmbedding (CycleCoverPathVertex V))

def fullCycleCoverOutGraph
    (V : Type*) [Fintype V] [DecidableEq V] :
    SimpleGraph (CycleCoverAbsorberVertex V) :=
  graphSup univ (fun i : FullCycleCoverCopy (CycleCoverPathVertex V) =>
    coveredGraph (fullCycleCoverOut i))

def embeddedPathCoverGraph
    (V : Type*) [Fintype V] [DecidableEq V] :
    SimpleGraph (CycleCoverAbsorberVertex V) :=
  (pathCoverGraph V (6 * (Fintype.card V) ^ 2)).map
    (fullCycleCoverBaseEmbedding (CycleCoverPathVertex V))

/-- The fixed graph before the high-girth sphere transform. -/
def cycleCoverAbsorberGraph
    (V : Type*) [Fintype V] [DecidableEq V] :
    SimpleGraph (CycleCoverAbsorberVertex V) :=
  fullCycleCoverOutGraph V ⊔ embeddedPathCoverGraph V

lemma completedAugmentedGraph_map_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (D : CycleDecomposition G)
    (hD : D.cycleCount < (Fintype.card V) ^ 2) :
    (D.completedAugmentedGraph (Fintype.card V) hD).map
        (fullCycleCoverBaseEmbedding (CycleCoverPathVertex V)) =
      G.map (cycleCoverRootEmbedding V) ⊔ embeddedPathCoverGraph V := by
  rw [CycleDecomposition.completedAugmentedGraph_eq,
    SimpleGraph.map_sup_function, SimpleGraph.map_map]
  rfl

/-- Exact absorption before the girth transform: every triangle-divisible
root graph switches into the fixed path/full-cycle-cover graph. -/
theorem cycleCoverAbsorber_absorbs
    {V : Type*} [Fintype V] [DecidableEq V]
    (hV : 2 ≤ Fintype.card V)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : TriangleDivisible G) :
    ∃ C : TripleSystemOn (CycleCoverAbsorberVertex V),
      IsTriangleDecomposition
        (cycleCoverAbsorberGraph V ⊔
          G.map (cycleCoverRootEmbedding V)) C := by
  obtain ⟨D⟩ := exists_cycleDecomposition_of_even_degree G hG.1
  let hD := D.cycleCount_lt_card_sq hV
  have hgroup := D.hasFullCycleCoverGrouping_completed hV hG
  obtain ⟨C, hC⟩ := fullCycleCover_absorbs_grouped hgroup
  refine ⟨C, ?_⟩
  rw [completedAugmentedGraph_map_eq D hD] at hC
  change IsTriangleDecomposition
    ((fullCycleCoverOutGraph V ⊔ embeddedPathCoverGraph V) ⊔
      G.map (cycleCoverRootEmbedding V)) C
  change IsTriangleDecomposition
    (fullCycleCoverOutGraph V ⊔
      (G.map (cycleCoverRootEmbedding V) ⊔ embeddedPathCoverGraph V)) C at hC
  rw [show
      (fullCycleCoverOutGraph V ⊔ embeddedPathCoverGraph V) ⊔
          G.map (cycleCoverRootEmbedding V) =
        fullCycleCoverOutGraph V ⊔
          (G.map (cycleCoverRootEmbedding V) ⊔
            embeddedPathCoverGraph V) by ac_rfl]
  exact hC

end

end Erdos207
