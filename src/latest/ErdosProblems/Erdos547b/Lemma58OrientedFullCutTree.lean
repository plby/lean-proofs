/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58OrientedCertifiedAssembly
import ErdosProblems.Erdos547b.Lemma58RootCandidateCleaning

/-!
# Full cut-tree reconstruction with a fixed source orientation

This is the orientation-sensitive counterpart of `Lemma58FullCutTree` for
Parts 1/2.  Root targets and local edge fibers share one literal branch
orientation, and cut-parent cleaning is charged only on the physical target
of the deleted parent.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58OrientedFullCutTree

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.RegularPair
open Erdos547b.ZhaoClaim68BranchAdapter
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58OwnerForbiddenCertificate
open Erdos547b.ZhaoLemma58CertifiedMatchingAssembly
open Erdos547b.ZhaoLemma58OrientedCutForestReconstruction
open Erdos547b.ZhaoLemma58OrientedCutEdgeLocal
open Erdos547b.ZhaoLemma58OrientedCertifiedAssembly
open Erdos547b.ZhaoLemma58RootSkeleton
open Erdos547b.ZhaoLemma58RootCandidateCleaning

universe u v x

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- Literal branch forest in one assignment fiber. -/
abbrev orientedCutFiberForest
    (P : ZhaoForestPartition T globalRoot small)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (e : Fin k) : OrderedRootedForest (matchingFiber assign e).card :=
  (OrderedBranchForest.restrict (branchForest P)
    (matchingFiber assign e)).branches

/-- Component owner of one branch in an assignment fiber. -/
abbrev orientedCutFiberOwner
    (P : ZhaoForestPartition T globalRoot small)
    {k : ℕ}
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (e : Fin k) : Fin (matchingFiber assign e).card → Fin P.numParts :=
  fun i ↦ (branchForest P).owner
    (OrderedBranchForest.selectedEquiv (matchingFiber assign e) i)

/-- Exact fixed-orientation edge-local result constructed from source/live
host data.  It is an internal result type, not a public hypothesis of the
rich application; concrete canonical threshold constructors build it. -/
abbrev FixedOrientedCutEdgeData
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (Gpair Gtarget : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gtarget.Adj]
    {k : ℕ} (rootImage : Fin P.numParts → B)
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (orient : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin 2 ≃ Fin 2) :=
  ∀ e, Nonempty {E : CertifiedOwnerDynamicEmbedding
      (orientedCutFiberForest P assign e) Gpair
      (fun i ↦ rootImage (orientedCutFiberOwner P assign e i))
      (endpoint e) (orientedCutFiberOwner P assign e)
      (orientedCutParentBad P Gtarget rootImage assign endpoint orient e) //
    E.orient = restrictedOrient assign orient e}

/-- Assemble the fixed fibers and reconstruct every original tree edge. -/
theorem exists_treeCopy_of_fixedOrientedCutEdgeData
    {B : Type v} [Fintype B] [DecidableEq B]
    (P : ZhaoForestPartition T globalRoot small)
    (Gpair Gtarget : SimpleGraph B)
    [DecidableRel Gpair.Adj] [DecidableRel Gtarget.Adj]
    (hGle : Gpair ≤ Gtarget)
    {k : ℕ} (rootImage : Fin P.numParts → B)
    (assign : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin k)
    (endpoint : Fin k → Fin 2 → Finset B)
    (orient : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin 2 ≃ Fin 2)
    (hdata : FixedOrientedCutEdgeData P Gpair Gtarget rootImage assign
      endpoint orient)
    (hsupportDisjoint : ∀ e e', e ≠ e' →
      Disjoint (endpoint e 0 ∪ endpoint e 1)
        (endpoint e' 0 ∪ endpoint e' 1))
    (hrootInjective : Function.Injective rootImage)
    (hrootOutside : ∀ q e c, rootImage q ∉ endpoint e c)
    (hrootCut : ∀ j (hj : j.val ≠ 0),
      P.parent j hj = P.roots (P.parentPart j hj) →
      Gtarget.Adj (rootImage j) (rootImage (P.parentPart j hj))) :
    Nonempty (T.Copy Gtarget) := by
  obtain ⟨E, hEorient⟩ :=
    exists_certifiedRootAttachedBranchEmbedding_of_fixedMatchingFibers
      (branchForest P) Gpair rootImage assign endpoint orient
      (fun e q c ↦ orientedCutParentBad P Gtarget rootImage assign endpoint
        orient e q c) hdata hsupportDisjoint
  exact ⟨treeCopyOfOrientedCertifiedMatchingFibersOfLE P Gpair Gtarget
    hGle rootImage assign endpoint orient E hEorient hrootInjective
    hrootOutside hrootCut⟩

/-- Target-cleaned root wrapper for the fixed-orientation cut-tree
constructor. -/
theorem exists_treeCopy_of_targetCleanedRoots_and_fixedOrientedDataWithLinks
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
    (endpoint : Fin k → Fin 2 → Finset B)
    (orient : Fin (Fintype.card (ChildKey P.orderedForest)) → Fin 2 ≃ Fin 2)
    (hsupportDisjoint : ∀ e e', e ≠ e' →
      Disjoint (endpoint e 0 ∪ endpoint e 1)
        (endpoint e' 0 ∪ endpoint e' 1))
    (hrootRawOutside : ∀ q e c, Disjoint (rootRaw q) (endpoint e c))
    (hdata : ∀ rootImage : Fin P.numParts → B,
      (∀ q, rootImage q ∈ rootCandidate Gtarget rootRho rootWhole
        rootRaw targets targetWhole targetRaw q) →
      FixedOrientedCutEdgeData P Gpair Gtarget rootImage assign endpoint
        orient) :
    Nonempty (T.Copy Gtarget) := by
  obtain ⟨R⟩ := exists_rootSkeletonEmbedding_of_targetCleaningWithLinks P
    Gtarget rootRho rootWhole rootRaw targets targetWhole targetRaw rootLoss
    hrootBad hrootBudget hrootLink
  apply exists_treeCopy_of_fixedOrientedCutEdgeData P Gpair Gtarget hGle
    R.rootImage assign endpoint orient (hdata R.rootImage R.mem_candidate)
    hsupportDisjoint R.injective
  · intro q e c
    exact Finset.disjoint_left.mp (hrootRawOutside q e c)
      (rootCandidate_subset_raw Gtarget rootRho rootWhole rootRaw targets
        targetWhole targetRaw q (R.mem_candidate q))
  · exact R.cut_root_adj

end Erdos547b.ZhaoLemma58OrientedFullCutTree

#print axioms Erdos547b.ZhaoLemma58OrientedFullCutTree.exists_treeCopy_of_fixedOrientedCutEdgeData
#print axioms Erdos547b.ZhaoLemma58OrientedFullCutTree.exists_treeCopy_of_targetCleanedRoots_and_fixedOrientedDataWithLinks
