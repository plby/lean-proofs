/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58CutForestReconstruction
import ErdosProblems.Erdos547b.Lemma58CutEdgeLocal
import ErdosProblems.Erdos547b.Lemma58RootSkeleton
import ErdosProblems.Erdos547b.Lemma58RootCandidateCleaning

/-!
# Full cut-aware tree output of the dynamic Zhao Lemma 5.8 backend

This module composes the three checked layers:

* concrete threshold/Appendix realization of every owner batch in the exact
  residual matching endpoints;
* certified owner-specific target cleaning and matching-fiber assembly; and
* literal reconstruction of all edges deleted by the Zhao forest partition.

The public theorem has no embedding, copy, containment, or continuation
premise.  Its large local callback is `OwnerLocalStepData`, a source/live-host
record realized by the already checked graph constructors.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58FullCutTree

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58ChosenOwnerBatches
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58OwnerLocalStep
open Erdos547b.ZhaoLemma58OwnerForbidden
open Erdos547b.ZhaoLemma58OwnerForbiddenCertificate
open Erdos547b.ZhaoLemma58CertifiedMatchingAssembly
open Erdos547b.ZhaoLemma58CutForestReconstruction
open Erdos547b.ZhaoLemma58CutEdgeLocal
open Erdos547b.ZhaoLemma58RootSkeleton
open Erdos547b.ZhaoLemma58RootCandidateCleaning

universe u v x

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- Literal branch forest assigned to one matching edge. -/
abbrev cutFiberForest
    (P : ZhaoForestPartition T globalRoot small)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (e : Fin k) : OrderedRootedForest (matchingFiber assign e).card :=
  (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.restrict
    (branchForest P) (matchingFiber assign e)).branches

/-- Original component owner of a branch in one matching fiber. -/
abbrev cutFiberOwner
    (P : ZhaoForestPartition T globalRoot small)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (e : Fin k) : Fin (matchingFiber assign e).card → Fin P.numParts :=
  fun i ↦ (branchForest P).owner
    (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i)

/-- The complete cut-aware constructor with the correct edge-local
alternatives: Parts 1/2 pay for and orient a matching edge once, while Part
3 may process its owner batches adaptively.  Every premise is source or
live-host data; the certified embeddings are constructed internally. -/
theorem exists_treeCopy_of_cutEdgeLocalData
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (Gpair Gtarget : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gtarget.Adj]
    (hGle : Gpair ≤ Gtarget)
    {k : ℕ} (rootImage : Fin P.numParts → B)
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (hendpoint : ∀ e c, endpoint e c ⊆ whole e c)
    (hpairDisjoint : ∀ e, Disjoint (whole e 0) (whole e 1))
    (hsupportDisjoint : ∀ e e', e ≠ e' →
      Disjoint (endpoint e 0 ∪ endpoint e 1)
        (endpoint e' 0 ∪ endpoint e' 1))
    (hdata : ∀ e, Nonempty (CutEdgeLocalData P
      (cutFiberForest P assign e) Gpair Gtarget
      (fun i ↦ rootImage (cutFiberOwner P assign e i))
      (whole e) (endpoint e) (cutFiberOwner P assign e)
      (cutParentBad P Gtarget rootImage endpoint e)
      (globalCutParentBad P Gtarget rootImage endpoint e)
      (rho e) (density e)))
    (hrootInjective : Function.Injective rootImage)
    (hrootOutside : ∀ q e c, rootImage q ∉ endpoint e c)
    (hrootCut : ∀ j (hj : j.val ≠ 0),
      P.parent j hj = P.roots (P.parentPart j hj) →
      Gtarget.Adj (rootImage j) (rootImage (P.parentPart j hj))) :
    Nonempty (T.Copy Gtarget) := by
  classical
  have hlocal (e : Fin k) : Nonempty (CertifiedOwnerDynamicEmbedding
      (cutFiberForest P assign e) Gpair
      (fun i ↦ rootImage (cutFiberOwner P assign e i))
      (endpoint e) (cutFiberOwner P assign e)
      (cutParentBad P Gtarget rootImage endpoint e)) := by
    obtain ⟨D⟩ := hdata e
    exact D.realize P (cutFiberForest P assign e) Gpair Gtarget
      (fun i ↦ rootImage (cutFiberOwner P assign e i))
      (whole e) (endpoint e) (cutFiberOwner P assign e)
      (cutParentBad P Gtarget rootImage endpoint e)
      (globalCutParentBad P Gtarget rootImage endpoint e)
      (rho e) (density e) (hendpoint e) (hpairDisjoint e)
      (fun q c ↦ cutParentBad_subset_global P Gtarget rootImage endpoint e q c)
  obtain ⟨E⟩ :=
    exists_certifiedRootAttachedBranchEmbedding_of_matchingFibers
      (branchForest P) Gpair rootImage assign endpoint
      (cutParentBad P Gtarget rootImage endpoint) hlocal hsupportDisjoint
  exact ⟨treeCopyOfCertifiedMatchingFibersOfLE P Gpair Gtarget hGle
    rootImage assign endpoint E hrootInjective hrootOutside hrootCut⟩

/-- Edge-local source/live-host data after the root images have been fixed. -/
abbrev CutEdgeData
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (Gpair Gtarget : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gtarget.Adj]
    {k : ℕ} (rootImage : Fin P.numParts → B)
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ) :=
  ∀ e, Nonempty (CutEdgeLocalData P
    (cutFiberForest P assign e) Gpair Gtarget
    (fun i ↦ rootImage (cutFiberOwner P assign e i))
    (whole e) (endpoint e) (cutFiberOwner P assign e)
    (cutParentBad P Gtarget rootImage endpoint e)
    (globalCutParentBad P Gtarget rootImage endpoint e)
    (rho e) (density e))

/-- Root-selection form of the edge-local constructor. -/
theorem exists_treeCopy_of_rootCandidates_and_cutEdgeData
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (Gpair Gtarget : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gtarget.Adj]
    (hGle : Gpair ≤ Gtarget)
    {k : ℕ}
    (candidate : Fin P.numParts → Finset B)
    (hcandidate : ∀ i, P.numParts ≤ #(candidate i))
    (hlink : ∀ j (hj : j.val ≠ 0)
      (hroot : P.parent j hj = P.roots (P.parentPart j hj))
      z, z ∈ candidate (P.parentPart j hj) →
      P.numParts ≤ #((candidate j).filter (Gtarget.Adj z)))
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (hendpoint : ∀ e c, endpoint e c ⊆ whole e c)
    (hpairDisjoint : ∀ e, Disjoint (whole e 0) (whole e 1))
    (hsupportDisjoint : ∀ e e', e ≠ e' →
      Disjoint (endpoint e 0 ∪ endpoint e 1)
        (endpoint e' 0 ∪ endpoint e' 1))
    (hrootOutside : ∀ q z, z ∈ candidate q →
      ∀ e c, z ∉ endpoint e c)
    (hdata : ∀ rootImage : Fin P.numParts → B,
      (∀ q, rootImage q ∈ candidate q) →
      CutEdgeData P Gpair Gtarget rootImage assign whole endpoint rho density) :
    Nonempty (T.Copy Gtarget) := by
  obtain ⟨R⟩ := exists_rootSkeletonEmbedding P Gtarget candidate
    hcandidate hlink
  apply exists_treeCopy_of_cutEdgeLocalData P Gpair Gtarget hGle R.rootImage
    assign whole endpoint rho density hendpoint hpairDisjoint hsupportDisjoint
  · exact hdata R.rootImage R.mem_candidate
  · exact R.injective
  · intro q e c
    exact hrootOutside q (R.rootImage q) (R.mem_candidate q) e c
  · exact R.cut_root_adj

/-- Fully target-cleaned root form of the edge-local constructor. -/
theorem exists_treeCopy_of_targetCleanedRoots_and_cutEdgeData
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (Gpair Gtarget : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gtarget.Adj]
    (hGle : Gpair ≤ Gtarget)
    {Target : Type x} [Fintype Target] [DecidableEq Target]
    (rootRho : ℝ)
    (rootWhole rootRaw : Fin P.numParts → Finset B)
    (targets : Fin P.numParts → Finset Target)
    (targetWhole targetRaw : Target → Finset B)
    (rootLoss : Fin P.numParts → ℕ)
    (hrootBad : ∀ q, #(rootTargetBad Gtarget rootRho rootWhole rootRaw
      targets targetWhole targetRaw q) ≤ rootLoss q)
    (hrootBudget : ∀ q, P.numParts + rootLoss q ≤ #(rootRaw q))
    (hrootTarget : ∀ j (hj : j.val ≠ 0)
      (hroot : P.parent j hj = P.roots (P.parentPart j hj)),
      ∃ t ∈ targets (P.parentPart j hj), targetRaw t = rootRaw j)
    (hrootDegree : ∀ j (hj : j.val ≠ 0)
      (hroot : P.parent j hj = P.roots (P.parentPart j hj))
      (t : Target) (ht : t ∈ targets (P.parentPart j hj))
      (htarget : targetRaw t = rootRaw j),
      (P.numParts : ℝ) + rootLoss j ≤
        (Gtarget.edgeDensity (rootWhole (P.parentPart j hj))
          (targetWhole t) - rootRho) * #(targetRaw t))
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (hendpoint : ∀ e c, endpoint e c ⊆ whole e c)
    (hpairDisjoint : ∀ e, Disjoint (whole e 0) (whole e 1))
    (hsupportDisjoint : ∀ e e', e ≠ e' →
      Disjoint (endpoint e 0 ∪ endpoint e 1)
        (endpoint e' 0 ∪ endpoint e' 1))
    (hrootRawOutside : ∀ q e c, Disjoint (rootRaw q) (endpoint e c))
    (hdata : ∀ rootImage : Fin P.numParts → B,
      (∀ q, rootImage q ∈ rootCandidate Gtarget rootRho rootWhole
        rootRaw targets targetWhole targetRaw q) →
      CutEdgeData P Gpair Gtarget rootImage assign whole endpoint rho density) :
    Nonempty (T.Copy Gtarget) := by
  obtain ⟨R⟩ := exists_rootSkeletonEmbedding_of_targetCleaning P Gtarget
    rootRho rootWhole rootRaw targets targetWhole targetRaw rootLoss hrootBad
    hrootBudget hrootTarget hrootDegree
  apply exists_treeCopy_of_cutEdgeLocalData P Gpair Gtarget hGle R.rootImage
    assign whole endpoint rho density hendpoint hpairDisjoint hsupportDisjoint
  · exact hdata R.rootImage R.mem_candidate
  · exact R.injective
  · intro q e c
    exact Finset.disjoint_left.mp (hrootRawOutside q e c)
      (rootCandidate_subset_raw Gtarget rootRho rootWhole rootRaw targets
        targetWhole targetRaw q (R.mem_candidate q))
  · exact R.cut_root_adj

/-- Target-cleaned root form with each root/root target and its density
estimate packaged together. -/
theorem exists_treeCopy_of_targetCleanedRoots_and_cutEdgeDataWithLinks
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (Gpair Gtarget : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gtarget.Adj]
    (hGle : Gpair ≤ Gtarget)
    {Target : Type x} [Fintype Target] [DecidableEq Target]
    (rootRho : ℝ)
    (rootWhole rootRaw : Fin P.numParts → Finset B)
    (targets : Fin P.numParts → Finset Target)
    (targetWhole targetRaw : Target → Finset B)
    (rootLoss : Fin P.numParts → ℕ)
    (hrootBad : ∀ q, #(rootTargetBad Gtarget rootRho rootWhole rootRaw
      targets targetWhole targetRaw q) ≤ rootLoss q)
    (hrootBudget : ∀ q, P.numParts + rootLoss q ≤ #(rootRaw q))
    (hrootLink : ∀ j (hj : j.val ≠ 0)
      (hroot : P.parent j hj = P.roots (P.parentPart j hj)),
      ∃ t ∈ targets (P.parentPart j hj),
        targetRaw t = rootRaw j ∧
        (P.numParts : ℝ) + rootLoss j ≤
          (Gtarget.edgeDensity (rootWhole (P.parentPart j hj))
            (targetWhole t) - rootRho) * #(targetRaw t))
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (hendpoint : ∀ e c, endpoint e c ⊆ whole e c)
    (hpairDisjoint : ∀ e, Disjoint (whole e 0) (whole e 1))
    (hsupportDisjoint : ∀ e e', e ≠ e' →
      Disjoint (endpoint e 0 ∪ endpoint e 1)
        (endpoint e' 0 ∪ endpoint e' 1))
    (hrootRawOutside : ∀ q e c, Disjoint (rootRaw q) (endpoint e c))
    (hdata : ∀ rootImage : Fin P.numParts → B,
      (∀ q, rootImage q ∈ rootCandidate Gtarget rootRho rootWhole
        rootRaw targets targetWhole targetRaw q) →
      CutEdgeData P Gpair Gtarget rootImage assign whole endpoint rho density) :
    Nonempty (T.Copy Gtarget) := by
  obtain ⟨R⟩ := exists_rootSkeletonEmbedding_of_targetCleaningWithLinks P
    Gtarget rootRho rootWhole rootRaw targets targetWhole targetRaw rootLoss
    hrootBad hrootBudget hrootLink
  apply exists_treeCopy_of_cutEdgeLocalData P Gpair Gtarget hGle R.rootImage
    assign whole endpoint rho density hendpoint hpairDisjoint hsupportDisjoint
  · exact hdata R.rootImage R.mem_candidate
  · exact R.injective
  · intro q e c
    exact Finset.disjoint_left.mp (hrootRawOutside q e c)
      (rootCandidate_subset_raw Gtarget rootRho rootWhole rootRaw targets
        targetWhole targetRaw q (R.mem_candidate q))
  · exact R.cut_root_adj

/-- The complete cut-aware dynamic Lemma-5.8 constructor. -/
theorem exists_treeCopy_of_ownerLocalSteps
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (Gpair Gtarget : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gtarget.Adj]
    (hGle : Gpair ≤ Gtarget)
    {k : ℕ} (rootImage : Fin P.numParts → B)
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (hendpoint : ∀ e c, endpoint e c ⊆ whole e c)
    (hpairDisjoint : ∀ e, Disjoint (whole e 0) (whole e 1))
    (hsupportDisjoint : ∀ e e', e ≠ e' →
      Disjoint (endpoint e 0 ∪ endpoint e 1)
        (endpoint e' 0 ∪ endpoint e' 1))
    (hdata : ∀ e n (hn : n < P.numParts)
      (Eprefix : ChosenPartialDynamicEmbedding
        (cutFiberForest P assign e) Gpair
        (fun i ↦ rootImage (cutFiberOwner P assign e i))
        (endpoint e)
        (ownerPrefix Finset.univ (cutFiberOwner P assign e) n)),
      Nonempty (OwnerLocalStepData
        (selectedForest (cutFiberForest P assign e)
          (ownerBatch Finset.univ (cutFiberOwner P assign e) ⟨n, hn⟩)) Gpair
        (fun i ↦ rootImage (cutFiberOwner P assign e
          (OrderedBranchForest.selectedEquiv
            (ownerBatch Finset.univ (cutFiberOwner P assign e) ⟨n, hn⟩) i)))
        (whole e)
        (ownerCleanedLive
          (fun c ↦ endpoint e c \ Eprefix.used c)
          (cutParentBad P Gtarget rootImage endpoint e ⟨n, hn⟩))
        (rho e) (density e)))
    (hrootInjective : Function.Injective rootImage)
    (hrootOutside : ∀ q e c, rootImage q ∉ endpoint e c)
    (hrootCut : ∀ j (hj : j.val ≠ 0),
      P.parent j hj = P.roots (P.parentPart j hj) →
      Gtarget.Adj (rootImage j) (rootImage (P.parentPart j hj))) :
    Nonempty (T.Copy Gtarget) := by
  classical
  have hlocal (e : Fin k) : Nonempty (CertifiedOwnerDynamicEmbedding
      (cutFiberForest P assign e) Gpair
      (fun i ↦ rootImage (cutFiberOwner P assign e i))
      (endpoint e) (cutFiberOwner P assign e)
      (cutParentBad P Gtarget rootImage endpoint e)) := by
    apply exists_certifiedDynamicEmbedding_of_ownerLocalStepsWithForbidden
      (cutFiberForest P assign e) Gpair
      (fun i ↦ rootImage (cutFiberOwner P assign e i))
      (whole e) (endpoint e) (hendpoint e) (hpairDisjoint e)
      (cutFiberOwner P assign e) (rho e) (density e)
      (cutParentBad P Gtarget rootImage endpoint e)
    intro n hn Eprefix
    exact hdata e n hn Eprefix
  obtain ⟨E⟩ :=
    exists_certifiedRootAttachedBranchEmbedding_of_matchingFibers
      (branchForest P) Gpair rootImage assign endpoint
      (cutParentBad P Gtarget rootImage endpoint) hlocal hsupportDisjoint
  exact ⟨treeCopyOfCertifiedMatchingFibersOfLE P Gpair Gtarget hGle
    rootImage assign endpoint E hrootInjective hrootOutside hrootCut⟩

/-- The exact source/live-host callback required after a root image has been
chosen.  Naming it keeps the root-selection wrapper readable. -/
abbrev CutOwnerLocalData
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (Gpair Gtarget : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gtarget.Adj]
    {k : ℕ} (rootImage : Fin P.numParts → B)
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ) :=
  ∀ e n (hn : n < P.numParts)
    (Eprefix : ChosenPartialDynamicEmbedding
      (cutFiberForest P assign e) Gpair
      (fun i ↦ rootImage (cutFiberOwner P assign e i))
      (endpoint e)
      (ownerPrefix Finset.univ (cutFiberOwner P assign e) n)),
    Nonempty (OwnerLocalStepData
      (selectedForest (cutFiberForest P assign e)
        (ownerBatch Finset.univ (cutFiberOwner P assign e) ⟨n, hn⟩)) Gpair
      (fun i ↦ rootImage (cutFiberOwner P assign e
        (OrderedBranchForest.selectedEquiv
          (ownerBatch Finset.univ (cutFiberOwner P assign e) ⟨n, hn⟩) i)))
      (whole e)
      (ownerCleanedLive
        (fun c ↦ endpoint e c \ Eprefix.used c)
        (cutParentBad P Gtarget rootImage endpoint e ⟨n, hn⟩))
      (rho e) (density e))

/-- Root-selection form of the complete cut-aware constructor.  The roots
are chosen online from genuine candidate reservoirs, root/root cut links are
enforced during that choice, and the dynamic owner recursion handles all
internal cut parents. -/
theorem exists_treeCopy_of_rootCandidates_and_ownerLocalSteps
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (Gpair Gtarget : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gtarget.Adj]
    (hGle : Gpair ≤ Gtarget)
    {k : ℕ}
    (candidate : Fin P.numParts → Finset B)
    (hcandidate : ∀ i, P.numParts ≤ #(candidate i))
    (hlink : ∀ j (hj : j.val ≠ 0)
      (hroot : P.parent j hj = P.roots (P.parentPart j hj))
      z, z ∈ candidate (P.parentPart j hj) →
      P.numParts ≤ #((candidate j).filter (Gtarget.Adj z)))
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (hendpoint : ∀ e c, endpoint e c ⊆ whole e c)
    (hpairDisjoint : ∀ e, Disjoint (whole e 0) (whole e 1))
    (hsupportDisjoint : ∀ e e', e ≠ e' →
      Disjoint (endpoint e 0 ∪ endpoint e 1)
        (endpoint e' 0 ∪ endpoint e' 1))
    (hrootOutside : ∀ q z, z ∈ candidate q →
      ∀ e c, z ∉ endpoint e c)
    (hdata : ∀ rootImage : Fin P.numParts → B,
      (∀ q, rootImage q ∈ candidate q) →
      CutOwnerLocalData P Gpair Gtarget rootImage assign whole endpoint
        rho density) :
    Nonempty (T.Copy Gtarget) := by
  obtain ⟨R⟩ := exists_rootSkeletonEmbedding P Gtarget candidate
    hcandidate hlink
  apply exists_treeCopy_of_ownerLocalSteps P Gpair Gtarget hGle R.rootImage
    assign whole
    endpoint rho density hendpoint hpairDisjoint hsupportDisjoint
  · exact hdata R.rootImage R.mem_candidate
  · exact R.injective
  · intro q e c
    exact hrootOutside q (R.rootImage q) (R.mem_candidate q) e c
  · exact R.cut_root_adj

/-- Fully target-cleaned root form.  Regularity controls a finite union of
low-degree root exceptions, the resulting reservoirs produce the online root
skeleton, and the dynamic owner constructor embeds every branch while
retaining the internal cut-parent constraints. -/
theorem exists_treeCopy_of_targetCleanedRoots_and_ownerLocalSteps
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (Gpair Gtarget : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gtarget.Adj]
    (hGle : Gpair ≤ Gtarget)
    {Target : Type u} [Fintype Target] [DecidableEq Target]
    (rootRho : ℝ)
    (rootWhole rootRaw : Fin P.numParts → Finset B)
    (targets : Fin P.numParts → Finset Target)
    (targetWhole targetRaw : Target → Finset B)
    (rootLoss : Fin P.numParts → ℕ)
    (hrootBad : ∀ q, #(rootTargetBad Gtarget rootRho rootWhole rootRaw
      targets targetWhole targetRaw q) ≤ rootLoss q)
    (hrootBudget : ∀ q, P.numParts + rootLoss q ≤ #(rootRaw q))
    (hrootTarget : ∀ j (hj : j.val ≠ 0)
      (hroot : P.parent j hj = P.roots (P.parentPart j hj)),
      ∃ t ∈ targets (P.parentPart j hj), targetRaw t = rootRaw j)
    (hrootDegree : ∀ j (hj : j.val ≠ 0)
      (hroot : P.parent j hj = P.roots (P.parentPart j hj))
      (t : Target) (ht : t ∈ targets (P.parentPart j hj))
      (htarget : targetRaw t = rootRaw j),
      (P.numParts : ℝ) + rootLoss j ≤
        (Gtarget.edgeDensity (rootWhole (P.parentPart j hj))
          (targetWhole t) - rootRho) * #(targetRaw t))
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (whole endpoint : Fin k → Fin 2 → Finset B)
    (rho density : Fin k → ℝ)
    (hendpoint : ∀ e c, endpoint e c ⊆ whole e c)
    (hpairDisjoint : ∀ e, Disjoint (whole e 0) (whole e 1))
    (hsupportDisjoint : ∀ e e', e ≠ e' →
      Disjoint (endpoint e 0 ∪ endpoint e 1)
        (endpoint e' 0 ∪ endpoint e' 1))
    (hrootRawOutside : ∀ q e c, Disjoint (rootRaw q) (endpoint e c))
    (hdata : ∀ rootImage : Fin P.numParts → B,
      (∀ q, rootImage q ∈ rootCandidate Gtarget rootRho rootWhole
        rootRaw targets targetWhole targetRaw q) →
      CutOwnerLocalData P Gpair Gtarget rootImage assign whole endpoint
        rho density) :
    Nonempty (T.Copy Gtarget) := by
  obtain ⟨R⟩ := exists_rootSkeletonEmbedding_of_targetCleaning P Gtarget
    rootRho rootWhole rootRaw targets targetWhole targetRaw rootLoss hrootBad
    hrootBudget hrootTarget hrootDegree
  apply exists_treeCopy_of_ownerLocalSteps P Gpair Gtarget hGle R.rootImage
    assign whole endpoint rho density hendpoint hpairDisjoint hsupportDisjoint
  · exact hdata R.rootImage R.mem_candidate
  · exact R.injective
  · intro q e c
    exact Finset.disjoint_left.mp (hrootRawOutside q e c)
      (rootCandidate_subset_raw Gtarget rootRho rootWhole rootRaw targets
        targetWhole targetRaw q (R.mem_candidate q))
  · exact R.cut_root_adj

end Erdos547b.ZhaoLemma58FullCutTree

#print axioms Erdos547b.ZhaoLemma58FullCutTree.exists_treeCopy_of_ownerLocalSteps
#print axioms Erdos547b.ZhaoLemma58FullCutTree.exists_treeCopy_of_cutEdgeLocalData
#print axioms Erdos547b.ZhaoLemma58FullCutTree.exists_treeCopy_of_targetCleanedRoots_and_cutEdgeData
#print axioms Erdos547b.ZhaoLemma58FullCutTree.exists_treeCopy_of_targetCleanedRoots_and_cutEdgeDataWithLinks
#print axioms Erdos547b.ZhaoLemma58FullCutTree.exists_treeCopy_of_rootCandidates_and_ownerLocalSteps
#print axioms Erdos547b.ZhaoLemma58FullCutTree.exists_treeCopy_of_targetCleanedRoots_and_ownerLocalSteps
