/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim617CorrectedPaths
import ErdosProblems.Erdos547b.HierarchicalRegularEmbedding
import ErdosProblems.Erdos547b.HierarchicalTargetCleaning
import ErdosProblems.Erdos547b.Lemma614HierarchicalFullTree
import ErdosProblems.Erdos547b.Lemma614HierarchicalUnifiedFullTree
import ErdosProblems.Erdos547b.SpecialSegmentation

/-!
# The no-oracle regular-system endpoint used by Claim 6.17

This file is the boundary between the corrected, component-rooted source
decomposition for Claim 6.17 and the online form of Lemma 5.9(2).  In
particular, the theorem below does not accept a copy, a prescribed root map,
or any pointwise degree hypothesis.  It consumes the concrete cleaned
regular-pair system and constructs a copy of the original ordered branch
forest, including every edge from an original root and every hierarchical
attachment edge.

The Section 6 specialization has one remaining upstream responsibility:
constructing `CleanedRegularSystem` from the canonical Claim-6.16 cluster and
matching allocation.  Keeping that construction visible in the type avoids
silently replacing Zhao's online allocation argument by a copy oracle.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim617SwitchAdapter

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoLemma59Part2Full
open Erdos547b.ZhaoLemma59SpecialSegmentation
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalOnline
open Erdos547b.ZhaoLemma59HierarchicalRegular
open Erdos547b.ZhaoLemma59HierarchicalTargetCleaning
open Erdos547b.ZhaoLemma59HierarchicalUnified
open Erdos547b.ZhaoLemma614HierarchicalFullTree
open Erdos547b.ZhaoLemma614HierarchicalUnifiedFullTree

universe u

variable {r b c k : ℕ} {B : Type u}

/-- A concrete cleaned regular system realizes the whole original ordered
branch forest.  The intermediate hierarchical copy is constructed online;
`copyOfHierarchicalCopy` then transports it across the explicit segmentation
equivalence. -/
theorem exists_orderedBranchForestCopy_of_cleanedRegularSystem
    [Fintype B] [DecidableEq B]
    (F : OrderedBranchForest r b)
    (special : Finset (BranchVertex F))
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (originalImage : Fin r → B)
    (rootGroup : Fin #(marks F special) → Fin c)
    (group : Fin #(marks F special) → Fin k)
    (rootCandidate : Fin #(marks F special) → Finset B)
    (interiorCandidate :
      (i : Fin #(marks F special)) →
        Fin ((toHierarchicalSegmentForest F special).segments.size i) →
          Finset B)
    (S :
      ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.CleanedRegularSystem
        (toHierarchicalSegmentForest F special) G rho originalImage
        rootGroup group rootCandidate interiorCandidate) :
    Nonempty (F.graph.Copy G) := by
  obtain ⟨E⟩ :=
    ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.exists_hierarchicalRegularEmbedding
      (toHierarchicalSegmentForest F special) G rho originalImage
      rootGroup group rootCandidate interiorCandidate S
  exact ⟨copyOfHierarchicalCopy F special G E.fullCopy⟩

/-- Full-tree specialization used by the switch contradiction.  The literal
tree, rather than a caller-supplied core copy, is reindexed and realized by
the hierarchical online constructor, so all Zhao cut edges and all reserved
two-path edges occur in the returned copy. -/
theorem exists_fullTreeRegularEmbedding_of_switchCleanedRegularSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    [Fintype B] [DecidableEq B]
    (hT : T.IsTree) (globalRoot : V)
    (special : Finset (WholeBranchVertex T hT globalRoot))
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (globalRootImage : Fin 1 → B)
    (rootGroup :
      Fin #(marks (wholeBranchForest T hT globalRoot) special) → Fin c)
    (group :
      Fin #(marks (wholeBranchForest T hT globalRoot) special) → Fin k)
    (rootCandidate :
      Fin #(marks (wholeBranchForest T hT globalRoot) special) → Finset B)
    (interiorCandidate :
      (i : Fin #(marks (wholeBranchForest T hT globalRoot) special)) →
        Fin ((wholeHierarchy T hT globalRoot special).segments.size i) →
          Finset B)
    (S :
      ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.CleanedRegularSystem
        (wholeHierarchy T hT globalRoot special) G rho globalRootImage
        rootGroup group rootCandidate interiorCandidate) :
    Nonempty (FullTreeRegularEmbedding T hT globalRoot special G
      globalRootImage rootCandidate interiorCandidate) :=
  ZhaoLemma614HierarchicalFullTree.
    exists_fullTreeRegularEmbedding_of_cleanedRegularSystem
      T hT globalRoot special G rho globalRootImage rootGroup group
        rootCandidate interiorCandidate S

theorem exists_fullTreeCopy_of_switchCleanedRegularSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    [Fintype B] [DecidableEq B]
    (hT : T.IsTree) (globalRoot : V)
    (special : Finset (WholeBranchVertex T hT globalRoot))
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (globalRootImage : Fin 1 → B)
    (rootGroup :
      Fin #(marks (wholeBranchForest T hT globalRoot) special) → Fin c)
    (group :
      Fin #(marks (wholeBranchForest T hT globalRoot) special) → Fin k)
    (rootCandidate :
      Fin #(marks (wholeBranchForest T hT globalRoot) special) → Finset B)
    (interiorCandidate :
      (i : Fin #(marks (wholeBranchForest T hT globalRoot) special)) →
        Fin ((wholeHierarchy T hT globalRoot special).segments.size i) →
          Finset B)
    (S :
      ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.CleanedRegularSystem
        (wholeHierarchy T hT globalRoot special) G rho globalRootImage
        rootGroup group rootCandidate interiorCandidate) :
    Nonempty (T.Copy G) :=
  (exists_fullTreeRegularEmbedding_of_switchCleanedRegularSystem hT globalRoot
    special G rho globalRootImage rootGroup group rootCandidate
      interiorCandidate S).map FullTreeRegularEmbedding.fullCopy

/-- Raw target-reservoir form of the switch adapter.  Target-relative
cleaning and unified-pool realization are both constructed inside this
theorem; callers supply only aggregate capacities and physical-pool
separation. -/
theorem exists_fullTreeRegularEmbedding_of_switchTargetUnifiedSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    [Fintype B] [DecidableEq B]
    {c k : ℕ}
    (hT : T.IsTree) (globalRoot : V)
    (special : Finset (WholeBranchVertex T hT globalRoot))
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (globalRootImage : Fin 1 → B)
    (rootGroup :
      Fin #(marks (wholeBranchForest T hT globalRoot) special) → Fin c)
    (rootPool interiorPool :
      Fin #(marks (wholeBranchForest T hT globalRoot) special) → Fin k)
    (rootWhole rootRaw : Fin c → Finset B)
    (interiorWhole interiorRaw :
      (i : Fin #(marks (wholeBranchForest T hT globalRoot) special)) →
        Fin ((wholeHierarchy T hT globalRoot special).segments.size i) →
          Finset B)
    (reserved : Finset B)
    (hreserved : Finset.univ.image globalRootImage ⊆ reserved)
    (hattachOriginalCapacity : ∀ i q,
      (wholeHierarchy T hT globalRoot special).parent i = Sum.inl q →
      (HierarchicalSegmentForest.poolLoad
          (wholeHierarchy T hT globalRoot special)
          rootPool interiorPool (rootPool i) + 1 : ℝ) +
          #(HierarchicalSegmentForest.targetCoordinateRemoved
            (wholeHierarchy T hT globalRoot special) G rho rootGroup
              rootWhole rootRaw interiorWhole interiorRaw i
                ((wholeHierarchy T hT globalRoot special).segments.root i) ∪
            reserved) ≤
        (#((rootRaw (rootGroup i)).filter
          (G.Adj (globalRootImage q))) : ℝ))
    (hattachCapacity : ∀ i j a,
      (wholeHierarchy T hT globalRoot special).parent i = Sum.inr ⟨j, a⟩ →
      (HierarchicalSegmentForest.poolLoad
          (wholeHierarchy T hT globalRoot special)
          rootPool interiorPool (rootPool i) + 1 : ℝ) +
          #(HierarchicalSegmentForest.targetCoordinateRemoved
            (wholeHierarchy T hT globalRoot special) G rho rootGroup
              rootWhole rootRaw interiorWhole interiorRaw i
                ((wholeHierarchy T hT globalRoot special).segments.root i) ∪
            reserved) ≤
        (G.edgeDensity
          (HierarchicalSegmentForest.rawCandidate
            (wholeHierarchy T hT globalRoot special)
              rootGroup rootWhole interiorWhole j a)
          (rootWhole (rootGroup i)) - rho) * #(rootRaw (rootGroup i)))
    (hinternalCapacity : ∀ i a b,
      ((wholeHierarchy T hT globalRoot special).segments.tree i).Adj a b →
      b ≠ (wholeHierarchy T hT globalRoot special).segments.root i →
      (HierarchicalSegmentForest.poolLoad
          (wholeHierarchy T hT globalRoot special)
          rootPool interiorPool (interiorPool i) + 1 : ℝ) +
          #(HierarchicalSegmentForest.targetInteriorRemoved
            (wholeHierarchy T hT globalRoot special) G rho rootGroup
              rootWhole rootRaw interiorWhole interiorRaw reserved i b) ≤
        (G.edgeDensity
          (HierarchicalSegmentForest.rawCandidate
            (wholeHierarchy T hT globalRoot special)
              rootGroup rootWhole interiorWhole i a)
          (interiorWhole i b) - rho) * #(interiorRaw i b))
    (horiginalInjective : Function.Injective globalRootImage)
    (hrootRawDisjoint : ∀ i j, rootPool i ≠ rootPool j →
      Disjoint (rootRaw (rootGroup i)) (rootRaw (rootGroup j)))
    (hinteriorRawDisjoint : ∀ i a j b,
      interiorPool i ≠ interiorPool j →
      Disjoint (interiorRaw i a) (interiorRaw j b))
    (hrootInteriorRawDisjoint : ∀ i j a,
      rootPool i ≠ interiorPool j →
      Disjoint (rootRaw (rootGroup i)) (interiorRaw j a)) :
    let rootCandidate := HierarchicalSegmentForest.targetRootCandidate
      (wholeHierarchy T hT globalRoot special) G rho rootGroup rootWhole
        rootRaw interiorWhole interiorRaw reserved
    let interiorCandidate := HierarchicalSegmentForest.targetInteriorCandidate
      (wholeHierarchy T hT globalRoot special) G rho rootGroup rootWhole
        rootRaw interiorWhole interiorRaw reserved
    Nonempty (FullTreeRegularEmbedding T hT globalRoot special G
      globalRootImage rootCandidate interiorCandidate) := by
  dsimp only
  let rootCandidate := HierarchicalSegmentForest.targetRootCandidate
    (wholeHierarchy T hT globalRoot special) G rho rootGroup rootWhole rootRaw
      interiorWhole interiorRaw reserved
  let interiorCandidate := HierarchicalSegmentForest.targetInteriorCandidate
    (wholeHierarchy T hT globalRoot special) G rho rootGroup rootWhole rootRaw
      interiorWhole interiorRaw reserved
  let S := HierarchicalSegmentForest.targetUnifiedCleanedRegularSystem
    (wholeHierarchy T hT globalRoot special) G rho globalRootImage rootGroup
      rootPool interiorPool rootWhole rootRaw interiorWhole interiorRaw reserved
      hreserved hattachOriginalCapacity hattachCapacity hinternalCapacity
      horiginalInjective hrootRawDisjoint hinteriorRawDisjoint
      hrootInteriorRawDisjoint
  exact exists_fullTreeRegularEmbedding_of_unifiedCleanedRegularSystem
    T hT globalRoot special G globalRootImage rootPool interiorPool
      rootCandidate interiorCandidate S

/-- Copy-valued spelling of the raw target-reservoir switch endpoint. -/
theorem exists_fullTreeCopy_of_switchTargetUnifiedSystem
    {V : Type u} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} [DecidableRel T.Adj]
    [Fintype B] [DecidableEq B]
    {c k : ℕ}
    (hT : T.IsTree) (globalRoot : V)
    (special : Finset (WholeBranchVertex T hT globalRoot))
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (globalRootImage : Fin 1 → B)
    (rootGroup :
      Fin #(marks (wholeBranchForest T hT globalRoot) special) → Fin c)
    (rootPool interiorPool :
      Fin #(marks (wholeBranchForest T hT globalRoot) special) → Fin k)
    (rootWhole rootRaw : Fin c → Finset B)
    (interiorWhole interiorRaw :
      (i : Fin #(marks (wholeBranchForest T hT globalRoot) special)) →
        Fin ((wholeHierarchy T hT globalRoot special).segments.size i) →
          Finset B)
    (reserved : Finset B)
    (hreserved : Finset.univ.image globalRootImage ⊆ reserved)
    (hattachOriginalCapacity : ∀ i q,
      (wholeHierarchy T hT globalRoot special).parent i = Sum.inl q →
      (HierarchicalSegmentForest.poolLoad
          (wholeHierarchy T hT globalRoot special)
          rootPool interiorPool (rootPool i) + 1 : ℝ) +
          #(HierarchicalSegmentForest.targetCoordinateRemoved
            (wholeHierarchy T hT globalRoot special) G rho rootGroup
              rootWhole rootRaw interiorWhole interiorRaw i
                ((wholeHierarchy T hT globalRoot special).segments.root i) ∪
            reserved) ≤
        (#((rootRaw (rootGroup i)).filter
          (G.Adj (globalRootImage q))) : ℝ))
    (hattachCapacity : ∀ i j a,
      (wholeHierarchy T hT globalRoot special).parent i = Sum.inr ⟨j, a⟩ →
      (HierarchicalSegmentForest.poolLoad
          (wholeHierarchy T hT globalRoot special)
          rootPool interiorPool (rootPool i) + 1 : ℝ) +
          #(HierarchicalSegmentForest.targetCoordinateRemoved
            (wholeHierarchy T hT globalRoot special) G rho rootGroup
              rootWhole rootRaw interiorWhole interiorRaw i
                ((wholeHierarchy T hT globalRoot special).segments.root i) ∪
            reserved) ≤
        (G.edgeDensity
          (HierarchicalSegmentForest.rawCandidate
            (wholeHierarchy T hT globalRoot special)
              rootGroup rootWhole interiorWhole j a)
          (rootWhole (rootGroup i)) - rho) * #(rootRaw (rootGroup i)))
    (hinternalCapacity : ∀ i a b,
      ((wholeHierarchy T hT globalRoot special).segments.tree i).Adj a b →
      b ≠ (wholeHierarchy T hT globalRoot special).segments.root i →
      (HierarchicalSegmentForest.poolLoad
          (wholeHierarchy T hT globalRoot special)
          rootPool interiorPool (interiorPool i) + 1 : ℝ) +
          #(HierarchicalSegmentForest.targetInteriorRemoved
            (wholeHierarchy T hT globalRoot special) G rho rootGroup
              rootWhole rootRaw interiorWhole interiorRaw reserved i b) ≤
        (G.edgeDensity
          (HierarchicalSegmentForest.rawCandidate
            (wholeHierarchy T hT globalRoot special)
              rootGroup rootWhole interiorWhole i a)
          (interiorWhole i b) - rho) * #(interiorRaw i b))
    (horiginalInjective : Function.Injective globalRootImage)
    (hrootRawDisjoint : ∀ i j, rootPool i ≠ rootPool j →
      Disjoint (rootRaw (rootGroup i)) (rootRaw (rootGroup j)))
    (hinteriorRawDisjoint : ∀ i a j b,
      interiorPool i ≠ interiorPool j →
      Disjoint (interiorRaw i a) (interiorRaw j b))
    (hrootInteriorRawDisjoint : ∀ i j a,
      rootPool i ≠ interiorPool j →
      Disjoint (rootRaw (rootGroup i)) (interiorRaw j a)) :
    Nonempty (T.Copy G) := by
  let rootCandidate := HierarchicalSegmentForest.targetRootCandidate
    (wholeHierarchy T hT globalRoot special) G rho rootGroup rootWhole rootRaw
      interiorWhole interiorRaw reserved
  let interiorCandidate := HierarchicalSegmentForest.targetInteriorCandidate
    (wholeHierarchy T hT globalRoot special) G rho rootGroup rootWhole rootRaw
      interiorWhole interiorRaw reserved
  obtain ⟨E⟩ := exists_fullTreeRegularEmbedding_of_switchTargetUnifiedSystem
    hT globalRoot special G rho globalRootImage rootGroup rootPool interiorPool
      rootWhole rootRaw interiorWhole interiorRaw reserved hreserved
      hattachOriginalCapacity hattachCapacity hinternalCapacity
      horiginalInjective hrootRawDisjoint hinteriorRawDisjoint
      hrootInteriorRawDisjoint
  exact ⟨E.fullCopy⟩

end Erdos547b.ZhaoClaim617SwitchAdapter

#print axioms Erdos547b.ZhaoClaim617SwitchAdapter.exists_orderedBranchForestCopy_of_cleanedRegularSystem
