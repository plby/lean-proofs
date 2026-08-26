/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceAppendixCapacityBounds
import ErdosProblems.Erdos547b.SourceMixedRootRequirements
import ErdosProblems.Erdos547b.SourceActiveChunk

/-!
# Capacity-aware immutable chunk data and concrete graph prefixes

Threshold prefixes retain their actual fixed plan. Appendix prefixes
retain their chosen orientations, exact partial copies, and the residual
trichotomy. Both expose literal original-index placements and concrete
mixed-root requirements. No future embedding operation is a field.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceGeneralizedChunk

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceActualChunkEmbedding Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoSourceFamilyCapacity Erdos547b.ZhaoSourceAppendixCapacityBounds
open Erdos547b.ZhaoSourceActualPendingPlan Erdos547b.ZhaoSourceActualPartTwoPlan
open Erdos547b.ZhaoSourceMixedRootRequirements Erdos547b.ZhaoSourcePartThreeResidualNumerics
open Erdos547b.ZhaoSourcePendingPlacement Erdos547b.ZhaoSourceSortedBranchOrder
open Erdos547b.ZhaoSourcePendingOwnerInterval Erdos547b.ZhaoSourcePendingInterval
open Erdos547b.ZhaoSourceResidualRootPacking Erdos547b.ZhaoSourceSaturatedPacking
open Erdos547b.ZhaoSourceOriginalBranchPlacement Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58ChosenOwnerBatches Erdos547b.ZhaoLemma58ThresholdResidualCapacity

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)
variable (S : CleanSourceWitness W Q) (C : Index W)
variable {b r : ℕ} (F : OrderedRootedForest b) (owner : Fin b → Fin r) (kind : FamilyKind)

/-- Fixed source classification and allocation of one reserved chunk. -/
structure ChunkSource where
  edge : MatchingEdge Q.claim67.M
  edge_away : edge ∈ edgesAwayFromDistinguished Q.claim67.M (padFinset (large W))
    (Sum.inl Q.A) (Sum.inl Q.B)
  edge_valid : edgeValid W Q S C kind edge
  items : List (Fin b)
  nodup : items.Nodup
  owner_mono : Monotone (listOwner owner items)
  fits : mass (fun i => (F.size i : ℝ)) items ≤ capacity W Q S C kind edge
  branch_valid : ∀ i ∈ items, kind.BranchValid F i
  small : ∀ i ∈ items, F.size i ≤ freshBranchBound α W.clusterSize

variable (D : ChunkSource W Q S C F owner kind)

def ChunkSource.Backend : Type :=
  match kind with
  | .threshold _ => ActualPendingPlan W Q S C D.edge (listForest F D.items)
  | .appendix _ => PUnit

abbrev ChunkSource.ChosenPrefix (rootImage : Fin r → Fin hostN) (n : ℕ) :=
  ChosenPartialDynamicEmbedding (listForest F D.items) (embeddingHost W)
    (fun i => rootImage (listOwner owner D.items i))
    (residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge))
    (branchPrefix (ownerCutoff (listOwner owner D.items) n))

def ChunkSource.LiveInvariant {rootImage : Fin r → Fin hostN} {n : ℕ}
    (E : D.ChosenPrefix W Q S C F owner kind rootImage n) : Prop :=
  ResidualInvariant
    (rootDensity W S (Sum.inl C) (edgeVertex W Q D.edge 0))
    (rootDensity W S (Sum.inl C) (edgeVertex W Q D.edge 1))
    W.clusterSize ((epsilon α : ℝ) * W.clusterSize)
    ((W.clusterSize : ℝ) - (residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge) 0 \ E.used 0).card)
    ((W.clusterSize : ℝ) - (residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge) 1 \ E.used 1).card)

def ChunkSource.Prefix (backend : D.Backend W Q S C F owner kind)
    (rootImage : Fin r → Fin hostN) (n : ℕ) : Type := by
  cases kind with
  | threshold ratio =>
      exact PartialDynamicAttachedForestEmbedding (listForest F D.items) (embeddingHost W)
        (fun i => rootImage (listOwner owner D.items i)) backend.orient
        (residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge))
        (branchPrefix (ownerCutoff (listOwner owner D.items) n))
  | appendix lambda =>
      exact {E : D.ChosenPrefix W Q S C F owner (.appendix lambda) rootImage n //
        D.LiveInvariant W Q S C F owner (.appendix lambda) E}

/-- The source capacity constructs the threshold plan; the Appendix
backend needs no fixed future orientation. -/
theorem ChunkSource.exists_backend
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hC : C = Q.A ∨ C = Q.B) (hkind : kind.Valid α) :
    Nonempty (D.Backend W Q S C F owner kind) := by
  cases kind with
  | threshold ratio =>
      apply exists_actual_partTwo_plan W Q hα hα1 hhost horder S C hC D.edge (listForest F D.items)
        ratio hkind.1 hkind.2
      · intro i
        exact (D.branch_valid _ (List.get_mem D.items i)).1
      · intro i
        exact (D.branch_valid _ (List.get_mem D.items i)).2
      · intro i
        exact D.small _ (List.get_mem D.items i)
      · rw [listForest_order]
        exact D.fits
  | appendix _ => exact ⟨PUnit.unit⟩

def ChunkSource.chosen {backend : D.Backend W Q S C F owner kind}
    {rootImage : Fin r → Fin hostN} {n : ℕ}
    (E : D.Prefix W Q S C F owner kind backend rootImage n) :
    D.ChosenPrefix W Q S C F owner kind rootImage n := by
  cases kind with
  | threshold _ => exact ⟨backend.orient, E⟩
  | appendix _ => exact E.val

def ChunkSource.placement {backend : D.Backend W Q S C F owner kind}
    {rootImage : Fin r → Fin hostN} {n : ℕ}
    (E : D.Prefix W Q S C F owner kind backend rootImage n) :
    BranchPlacement F (embeddingHost W)
      (prefixSelected D.items (ownerCutoff (listOwner owner D.items) n))
      (fun i => rootImage (owner i)) (fun e => residualSide (edgeWhole W Q e) (deleted W Q e)) :=
  toPlacement F (embeddingHost W) D.items (fun i => rootImage (owner i))
    (D.chosen W Q S C F owner kind E).orient
    (fun e => residualSide (edgeWhole W Q e) (deleted W Q e)) D.edge
    (D.chosen W Q S C F owner kind E).state

def ChunkSource.requirement {backend : D.Backend W Q S C F owner kind}
    {rootImage : Fin r → Fin hostN} {n : ℕ}
    (E : D.Prefix W Q S C F owner kind backend rootImage n) : Requirement W Q :=
  match kind with
  | .threshold _ => some (.threshold D.edge)
  | .appendix lambda => some (.appendix D.edge (fun c =>
      residualSide (edgeWhole W Q D.edge) (deleted W Q D.edge) c \
        (D.chosen W Q S C F owner (.appendix lambda) E).used c))

/-- The actual stored Appendix prefix supplies its live-size requirement
from the chunk capacity, without assuming a current-root degree. -/
theorem ChunkSource.requirement_valid
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hkind : kind.Valid α)
    {backend : D.Backend W Q S C F owner kind} {rootImage : Fin r → Fin hostN} {n : ℕ}
    (E : D.Prefix W Q S C F owner kind backend rootImage n) :
    requirementValid W Q S C (D.requirement W Q S C F owner kind E) := by
  cases kind with
  | threshold _ => exact D.edge_away
  | appendix lambda =>
      have hfits : ((listForest F D.items).order : ℝ) ≤ capacity W Q S C (.appendix lambda) D.edge := by
        rw [listForest_order]
        exact D.fits
      have hlarge := live_large_before_root W Q hα hα1 hhost horder S C D.edge lambda hkind
        D.edge_valid (listForest F D.items) hfits (fun i => rootImage (listOwner owner D.items i))
        E.val.orient (branchPrefix (ownerCutoff (listOwner owner D.items) n)) E.val.state E.property
      refine ⟨D.edge_away, ?_⟩
      intro c
      have hd : (0 : ℝ) < densityCutoff α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.1
      exact ⟨(hd.trans_le hkind.1).trans_le (D.edge_valid c).1,
        Finset.sdiff_subset.trans Finset.sdiff_subset, hlarge c⟩

end Erdos547b.ZhaoSourceGeneralizedChunk

#print axioms Erdos547b.ZhaoSourceGeneralizedChunk.ChunkSource.exists_backend
#print axioms Erdos547b.ZhaoSourceGeneralizedChunk.ChunkSource.requirement_valid
