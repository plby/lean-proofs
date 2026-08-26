/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma54AppendixA
import ErdosProblems.Erdos547b.Lemma54AppendixA1

/-!
# Zhao Lemma 5.4(3): one dynamically realized Appendix group

This file is the acyclic composition layer between the finite source
orientation of Lemma A.2 and the adaptive regular-pair realization of
Corollary A.1.  The source theorem chooses an orientation satisfying the
four exact side/root capacities and records Zhao's three possible residual
outcomes.  The graph theorem then embeds the trees sequentially, deleting
their actual images from the live endpoint and prescribed-root pools.

The conclusion contains the resulting simultaneous forest embedding.  No
copy, continuation, live-state invariant, or static per-endpoint load is an
input.
-/

open scoped BigOperators SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58PartThreeEmbedding

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ForestMatching
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma54AppendixA
open Erdos547b.ZhaoLemma54AppendixA1

universe v

/-- The actual output of one owner-coherent Part-3 matching-edge group: the
source orientation, Zhao's residual trichotomy, and the concrete dynamically
constructed embedding attached to the one already embedded parent. -/
structure PartThreeDynamicGroupEmbedding
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (parent : B)
    (available rootPool : Fin 2 → Finset B)
    (small rootMargin : ℕ) where
  orient : Fin b → Fin 2 ≃ Fin 2
  embedding : DynamicAttachedForestEmbedding
    F G (fun _ ↦ parent) orient available
  trichotomy : AppendixA2Trichotomy F orient
    #(available 0) #(available 1) #(rootPool 0) #(rootPool 1)
    rootMargin small

/-- Compose Zhao Lemma A.2 with Corollary A.1 on one regular matching pair.

`D` is purely finite source/cardinality data.  All remaining hypotheses are
ordinary regular-pair and set-containment facts for the actual current
endpoint and root-reservoir sets.  The single `parent` argument is essential:
Zhao applies Appendix A separately to the forest below one already embedded
outer root, with `rootPool 0` and `rootPool 1` contained in that root's two
neighbourhoods.  In particular, no pre-existing embedding or conclusion is
assumed. -/
theorem exists_partThreeDynamicGroupEmbedding
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b)
    (small rootMargin sideMargin : ℕ)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (parent : B)
    (whole available rootPool : Fin 2 → Finset B)
    (rho density gamma epsilon N : ℝ)
    (D : AppendixA2NumericData F small rootMargin sideMargin
      #(available 0) #(available 1) #(rootPool 0) #(rootPool 1)
      gamma epsilon N)
    (hunif : G.IsUniform rho (whole 0) (whole 1))
    (havailable : ∀ c, available c ⊆ whole c)
    (hrootPool : ∀ c, rootPool c ⊆ available c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : density ≤ G.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ density - rho)
    (hepsilonN : 0 ≤ epsilon * N)
    (hregularRoot : ∀ c,
      rho * (#(whole c) : ℝ) < 3 * epsilon * N)
    (hregularInterior : ∀ c,
      rho * (#(whole c) : ℝ) ≤ gamma * N)
    (hcomponentMargin : ∀ i c,
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) ≤
        (density - rho) * (gamma * N))
    (hattach : ∀ c w, w ∈ rootPool c → G.Adj parent w) :
    Nonempty (PartThreeDynamicGroupEmbedding
      F G parent available rootPool small rootMargin) := by
  obtain ⟨O⟩ := exists_appendixA2Orientation F small rootMargin sideMargin
    #(available 0) #(available 1) #(rootPool 0) #(rootPool 1)
    gamma epsilon N D
  have hcapacity : AppendixOneCapacity
      (sideLoad F O.orient 0) (sideLoad F O.orient 1)
      (rootSideLoad F O.orient 0) (rootSideLoad F O.orient 1)
      #(available 0) #(available 1) #(rootPool 0) #(rootPool 1)
      gamma epsilon N := by
    simpa only [rootLoad, rootSideLoad] using O.capacity
  obtain ⟨E⟩ :=
    exists_dynamicAttachedForestEmbedding_of_appendixOneCapacity
      F G (fun _ ↦ parent) O.orient whole available rootPool rho density gamma
      epsilon N hunif havailable hrootPool hwholeDisjoint hdensity hfactor
      hepsilonN hregularRoot hregularInterior hcomponentMargin
      (fun i w hw ↦ hattach (branchRootSide F O.orient i) w hw)
      hcapacity
  exact ⟨{
    orient := O.orient
    embedding := E
    trichotomy := O.trichotomy
  }⟩

end Erdos547b.ZhaoLemma58PartThreeEmbedding

#print axioms Erdos547b.ZhaoLemma58PartThreeEmbedding.exists_partThreeDynamicGroupEmbedding
