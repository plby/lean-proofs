/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichGlobalFixedPlan

/-!
# Rich host facts for the fixed synchronized Lemma 5.8 recursion

This layer derives regular-pair facts and the complete permanent deletion
bound from the rich physical host.  The remaining recursive datum contains
only the source-oriented capacity, eligibility, and component inequalities.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichGlobalFixedHostFacts

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615RichDynamicHostLayout
open Erdos547b.ZhaoClaim615RichDynamicApplication
open Erdos547b.ZhaoClaim615RichDynamicRootLayout
open Erdos547b.ZhaoClaim615RichDynamicRootTargets
open Erdos547b.ZhaoClaim615RichDynamicRootCleaning
open Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan
open Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning
open Erdos547b.ZhaoClaim615RichGlobalOnlineSideApplication
open Erdos547b.ZhaoClaim615RichGlobalOnlinePlannedApplication
open Erdos547b.ZhaoClaim615RichGlobalFixedPlan
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma54ThresholdSourceNumerics
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58GlobalCutOnline
open Erdos547b.ZhaoLemma58GlobalPlannedOnlineState
open Erdos547b.ZhaoLemma58GlobalPlannedOwnerSuccessor
open Erdos547b.ZhaoLemma58GlobalFixedOrientationPlan
open Erdos547b.ZhaoLemma58GlobalFixedOnlineSuccessor
open Erdos547b.ZhaoLemma58OnlineParentCleaning
open Erdos547b.ZhaoLemma58OnlineParentSideCleaning
open Erdos547b.ZhaoLemma58RootCandidateCleaning

universe u v w

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

variable {Bv : Type v} {I : Type w}
variable [Fintype Bv] [DecidableEq Bv] [Fintype I] [DecidableEq I]
variable (Pcluster : ClusterAssignment Bv I)
variable (Gdegree : SimpleGraph Bv) [DecidableRel Gdegree.Adj]
variable (threshold quota : ℕ)
variable (R : SimpleGraph I) [DecidableRel R.Adj]
variable (miss : ℕ)
variable
  (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R
    (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)
variable (sourceDensity : EvenPadding I → EvenPadding I → ℝ)

variable {L : Finset (EvenPadding I)} {eta N targetB cap : ℝ}
variable {which : ExceptionalCase} {count cardBound : ℕ}
variable
  (E0 : SelectedExceptionalEdges Q sourceDensity L eta which count)
variable
  (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)

variable (P : ZhaoForestPartition T globalRoot small)
variable {available : Finset
  (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
variable {target slack : ℕ}
variable (S : SelectedF0 P available target slack)
variable {cap0 : K0 Q sourceDensity E0 → ℕ}
variable {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
variable {capb : Kb Q sourceDensity Mb → ℕ}
variable
  (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
    cap0 cap1 capb)

/-- Root candidates for the singleton fixed-orientation target plan. -/
abbrev richFixedCandidate
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho : ℝ)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2) :=
  plannedRootCandidate Pcluster Gdegree threshold quota R miss Q sourceDensity
    E0 Mb P S A G rootRho
    (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A orient)

/-- Rich physical endpoints after fixed-plan future-parent cleaning. -/
abbrev richFixedCleanEndpoint
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho : ℝ)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2) :=
  richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A G rootRho
    (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A orient)

/-- Planned root cleaning gives the density-gap degree into the literal side
chosen for the root of every globally oriented branch. -/
theorem richFixedCandidate_branchRoot_degree
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A orient))
    (j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
    (z : Bv)
    (hz : z ∈ richFixedCandidate Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho orient ((branchForest P).owner j)) :
    let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A)
    let c := globalFixedCoordinateSide (branchForest P) assign orient
      ⟨j, (branchForest P).branches.root j⟩
    (rootDensity - rootRho) *
        #(richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb (assign j) c) ≤
      #((richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb (assign j) c).filter (G.Adj z)) := by
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  let c := globalFixedCoordinateSide (branchForest P) assign orient
    ⟨j, (branchForest P).branches.root j⟩
  let target : RichRootTarget Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb := Sum.inr (assign j, c)
  have hc : c ∈
      (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A orient).branchRootSides j := by
    simp only [richFixedRootTargetPlan, globalFixedRootAllowed,
      Finset.mem_singleton, c, globalFixedCoordinateSide]
  have ht := plannedBranchRootTarget_mem Pcluster Gdegree threshold quota R miss
    Q sourceDensity E0 Mb P S A
    (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A orient) j c hc
  have hdegree := F.target_degree Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A G rootRho rootDensity H _
    ((branchForest P).owner j) z hz target
    (by simpa only [target, assign] using ht)
  simpa only [target, richTargetRaw, assign, c] using hdegree

/-- Regularity bounds the future-parent deletion on a side which is actually
used by the fixed plan.  The two scalar premises are exactly the missing
effects of cleaning the child's root reservoir: enough of that reservoir
survives to be regularity-large, and its online degree threshold fits below
the density gap. -/
theorem card_richFixedParentLowDegree_le_thresholdReserve
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A orient))
    (e : PhysicalIndex Q sourceDensity E0 Mb) (c : Fin 2)
    (q : Fin P.numParts) (hq : q.val ≠ 0)
    (hnotroot : P.parent q hq ≠ P.roots (P.parentPart q hq))
    (he : let coord := cutParentBranchCoordinate P q hq hnotroot
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) coord.1 = e)
    (hc : let coord := cutParentBranchCoordinate P q hq hnotroot
      c ∈ globalFixedCoordinateAllowed (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) orient coord)
    (hrootBudget :
      thresholdReserve rootRho
          #(rootWhole Pcluster Gdegree threshold quota R miss Q P q) +
        richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A rootRho
            (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb P S A orient) q ≤ quota)
    (hthreshold : (P.numParts : ℝ) ≤
      (rootDensity - rootRho) *
        #(richFixedCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho orient q)) :
    #(parentLowDegree P G
        (richFixedCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho orient)
        (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c) q) ≤
      thresholdReserve rootRho
        #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
          e c) := by
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  let coord := cutParentBranchCoordinate P q hq hnotroot
  let target : RichRootTarget Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb := Sum.inr (e, c)
  have hparentNonroot : P.parent q hq ∉ partitionRoots P :=
    (Finset.mem_sdiff.mp
      (cutParent_mem_partitionNonroots P q hq hnotroot)).2
  have hcoord : literalBranchCoordinate P (P.parent q hq) hparentNonroot =
      coord := by
    apply (partitionBranchEquivNonroots P).injective
    apply Subtype.ext
    simpa only [partitionBranchEquivNonroots_literalBranchCoordinate, coord,
      cutParentBranchCoordinate_value]
  have hc' : c ∈
      (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A orient).coordinateSides
        (literalBranchCoordinate P (P.parent q hq) hparentNonroot) := by
    change c ∈ globalFixedCoordinateAllowed (branchForest P) assign orient
      (literalBranchCoordinate P (P.parent q hq) hparentNonroot)
    simpa only [hcoord, assign, coord] using hc
  have ht0 := plannedCoordinateTarget_mem_of_nonrootCutParent Pcluster Gdegree
    threshold quota R miss Q sourceDensity E0 Mb P S A
    (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A orient) q hq hparentNonroot c hc'
  have he' : assign
      (literalBranchCoordinate P (P.parent q hq) hparentNonroot).1 = e := by
    simpa only [hcoord, assign, coord] using he
  have ht : target ∈
      richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A
          (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A orient) q := by
    simpa only [target, assign, he'] using ht0
  have hp := H.pair_of_adj
    (richRootCluster Pcluster Gdegree threshold quota R miss Q P q)
    (richTargetCluster Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb target) (F.pair_adj q target ht)
  have hp' :
      G.IsUniform rootRho
          (rootWhole Pcluster Gdegree threshold quota R miss Q P q)
          (richTargetWhole Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb target) ∧
        rootDensity ≤ G.edgeDensity
          (rootWhole Pcluster Gdegree threshold quota R miss Q P q)
          (richTargetWhole Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb target) := by
    simpa only [rootWhole_eq_padCluster, richTargetWhole_eq_padCluster] using hp
  have hcandidate :
      thresholdReserve rootRho
          #(rootWhole Pcluster Gdegree threshold quota R miss Q P q) ≤
        #(richFixedCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho orient q) := by
    apply root_count_le_card_rootCandidate G rootRho
      (rootWhole Pcluster Gdegree threshold quota R miss Q P)
      (rootRaw Pcluster Gdegree threshold quota R miss Q P)
      (richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A
          (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A orient))
      (richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb)
      (richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb) q _ _
    · exact F.rootTargetBad_le Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho rootDensity H _ q
    · simpa only [card_rootRaw] using hrootBudget
  have hrootLarge : rootRho *
        #(rootWhole Pcluster Gdegree threshold quota R miss Q P q) ≤
      #(richFixedCandidate Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho orient q) := by
    calc
      rootRho * #(rootWhole Pcluster Gdegree threshold quota R miss Q P q) ≤
          thresholdReserve rootRho
            #(rootWhole Pcluster Gdegree threshold quota R miss Q P q) :=
        thresholdReserve_covers _ _
      _ ≤ #(richFixedCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho orient q) := by
        exact_mod_cast hcandidate
  have hrootSub :
      richFixedCandidate Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb P S A G rootRho orient q ⊆
        rootWhole Pcluster Gdegree threshold quota R miss Q P q :=
    (rootCandidate_subset_raw G rootRho
      (rootWhole Pcluster Gdegree threshold quota R miss Q P)
      (rootRaw Pcluster Gdegree threshold quota R miss Q P)
      (richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A
          (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A orient))
      (richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb)
      (richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb) q).trans
      (rootRaw_subset Pcluster Gdegree threshold quota R miss Q P q)
  have hendpointLarge : rootRho *
        #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
          e c) ≤
      #(richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0
        Mb e c) := by
    simpa only [target, richTargetWhole, richTargetRaw] using
      F.target_large q target ht
  have hdensity : rootDensity ≤ G.edgeDensity
      (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
        e c)
      (rootWhole Pcluster Gdegree threshold quota R miss Q P q) := by
    simpa only [target, richTargetWhole, G.edgeDensity_comm] using hp'.2
  have hthreshold' : (P.numParts : ℝ) ≤
      (G.edgeDensity
          (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0
            Mb e c)
          (rootWhole Pcluster Gdegree threshold quota R miss Q P q) - rootRho) *
        #(richFixedCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho orient q) := by
    exact hthreshold.trans (mul_le_mul_of_nonneg_right
      (sub_le_sub_right hdensity rootRho) (Nat.cast_nonneg _))
  have hreal := card_parentLowDegree_le_of_uniform P G
    (richFixedCandidate Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb P S A G rootRho orient) q
    (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb e c)
    (rootWhole Pcluster Gdegree threshold quota R miss Q P q)
    (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
      e c) rootRho
    (by simpa only [target, richTargetWhole] using hp'.1.symm)
    (endpoint_subset_whole Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb e c) hrootSub hendpointLarge hrootLarge hthreshold'
  have hreserve := thresholdReserve_covers rootRho
    #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb e c)
  exact_mod_cast hreal.trans hreserve

/-- Honest per-edge inequalities left after the rich host supplies uniformity,
density, and both stages of permanent cleaning. -/
structure RichFixedFullFiberEdgeFacts
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A orient))
    (e : PhysicalIndex Q sourceDensity E0 Mb) : Type (max u v w) where
  factor_nonneg : 0 ≤ rootDensity - rootRho
  root_candidate_budget : ∀ q,
    thresholdReserve rootRho
        #(rootWhole Pcluster Gdegree threshold quota R miss Q P q) +
      richPlannedRootLoss Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A rootRho
          (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A orient) q ≤ quota
  parent_threshold : ∀ c q (hq : q.val ≠ 0)
    (hnotroot : P.parent q hq ≠ P.roots (P.parentPart q hq)),
    let coord := cutParentBranchCoordinate P q hq hnotroot
    (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A)) coord.1 = e →
    c ∈ globalFixedCoordinateAllowed (branchForest P)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) orient coord →
      (P.numParts : ℝ) ≤ (rootDensity - rootRho) *
        #(richFixedCandidate Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootRho orient q)
  total : ∀ c,
    (2 * quota + P.numParts *
        thresholdReserve rootRho
          #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb e c)) +
        sideLoad (onlineFiberForest (branchForest P)
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A)) e)
          (globalFixedFiberOrientation (branchForest P)
            (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
              (threshold := threshold) (quota := quota) (R := R)
              (miss := miss) (Q := Q) (sourceDensity := sourceDensity)
              (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)) orient e) c +
        thresholdReserve rootRho
          #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb e c) ≤
      #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
        e c)
  eligible_margin : ∀ c,
    let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A)
    (((2 * quota + P.numParts *
        thresholdReserve rootRho
          #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb e c)) +
        sideLoad (onlineFiberForest (branchForest P) assign e)
          (globalFixedFiberOrientation (branchForest P) assign orient e) c +
        (1 + thresholdReserve rootRho
            #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
              E0 Mb e c)) : ℕ) : ℝ) ≤
      (rootDensity - rootRho) *
        #(richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c)
  component_margin : ∀ c,
    let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A)
    (small : ℝ) +
        rootRho *
          (#(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb e c) : ℝ) + 1 ≤
      (rootDensity - rootRho) *
        ((#(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c) : ℝ) - (2 * quota + P.numParts *
            thresholdReserve rootRho
              #(richWhole Pcluster Gdegree threshold quota R miss Q
                sourceDensity E0 Mb e c) : ℕ) -
          sideLoad (onlineFiberForest (branchForest P) assign e)
            (globalFixedFiberOrientation (branchForest P) assign orient e) c)

namespace RichFixedFullFiberEdgeFacts

/-- Add the rich regular-pair and exact two-stage cleaning facts. -/
def toFixedFullFiberOnlineOwnerEdgeFacts
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A orient))
    (n : ℕ) (hn : n < P.numParts)
    (state : OnlineOwnerPrefixState (branchForest P) G
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A))
      (richFixedCleanEndpoint Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho orient)
      (richFixedCandidate Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho orient) n)
    (z : Bv) (e : PhysicalIndex Q sourceDensity E0 Mb)
    (hz : z ∈ richFixedCandidate Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho orient ⟨n, hn⟩)
    (D : RichFixedFullFiberEdgeFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho rootDensity H orient F e) :
    FixedFullFiberOnlineOwnerEdgeFacts (branchForest P) G
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) orient
      (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
      (richFixedCleanEndpoint Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho orient)
      (fun _ ↦ rootRho) (fun _ ↦ rootDensity)
      (richFixedCandidate Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho orient) n hn state z e where
  reserve := fun c ↦ thresholdReserve rootRho
    #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
      e c)
  permanentBound := fun c ↦ 2 * quota + P.numParts *
    thresholdReserve rootRho
      #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
        e c)
  uniform := (whole_pair Pcluster Gdegree threshold quota R miss Q sourceDensity
    E0 Mb G rootRho rootDensity H e).1
  density_lower := (whole_pair Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb G rootRho rootDensity H e).2
  factor_nonneg := D.factor_nonneg
  reserve_regular := fun c ↦ thresholdReserve_covers rootRho
    #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
      e c)
  permanent := by
    intro c
    apply card_whole_sdiff_onlineSideCleanEndpoint_le P G
      (richFixedCandidate Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho orient)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A))
      (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
      (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0
        Mb)
      (globalFixedCoordinateAllowed (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) orient)
      e c (2 * quota)
        (thresholdReserve rootRho
          #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb e c))
      (card_whole_sdiff_endpoint_le_two_mul_quota Pcluster Gdegree threshold
        quota R miss Q sourceDensity E0 Mb e c)
      (by
        intro q hq hnotroot
        dsimp only
        intro he hc
        exact card_richFixedParentLowDegree_le_thresholdReserve Pcluster
          Gdegree threshold quota R miss Q sourceDensity E0 Mb P S A G rootRho
          rootDensity H orient F e c q hq hnotroot he hc
          (D.root_candidate_budget q)
          (D.parent_threshold c q hq hnotroot he hc))
  total := D.total
  eligible := by
    intro i
    let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A)
    let j := onlineOwnerBatchBranch (branchForest P) assign e n hn i
    let c := branchRootSide
      (onlineOwnerBatchForest (branchForest P) assign e n hn)
      (onlineOwnerBatchFixedOrientation (branchForest P) assign orient e n hn) i
    have hjOwner : (branchForest P).owner j = ⟨n, hn⟩ := by
      exact onlineOwnerBatchBranch_owner (branchForest P) assign e n hn i
    have hzj : z ∈ richFixedCandidate Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho orient
          ((branchForest P).owner j) := by
      simpa only [hjOwner] using hz
    have hdegree0 := richFixedCandidate_branchRoot_degree Pcluster Gdegree
      threshold quota R miss Q sourceDensity E0 Mb P S A G rootRho rootDensity
      H orient F j z hzj
    have hjAssign : assign j = e := by
      exact onlineOwnerBatchBranch_assign (branchForest P) assign e n hn i
    have hc : c = globalFixedCoordinateSide (branchForest P) assign orient
        ⟨j, (branchForest P).branches.root j⟩ := by
      exact Finset.mem_singleton.mp
        (onlineOwnerBatchFixedOrientation_root_mem (branchForest P) assign orient
          e n hn i)
    have hdegree : (rootDensity - rootRho) *
          #(richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb e c) ≤
        #((richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c).filter (G.Adj z)) := by
      simpa only [assign, j, c, hjAssign, hc] using hdegree0
    have hneighborSub :
        (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0
            Mb e c).filter (G.Adj z) ⊆
          (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0
            Mb e c).filter (G.Adj z) := by
      intro x hx
      have hx' := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr
        ⟨endpoint_subset_whole Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb e c hx'.1, hx'.2⟩
    have hneighborCard :
        (#((richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb e c).filter (G.Adj z)) : ℝ) ≤
          #((richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0
            Mb e c).filter (G.Adj z)) := by
      exact_mod_cast Finset.card_le_card hneighborSub
    have hprefix := globalFixedPrefixLoad_add_sideLoadBefore_le_sideLoad
      (branchForest P) assign orient e n hn i c
    have hloadNat :
        (2 * quota + P.numParts *
            thresholdReserve rootRho
              #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
                E0 Mb e c)) +
          globalFixedPrefixLoad (branchForest P) assign orient e n c +
          (1 + thresholdReserve rootRho
              #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
                E0 Mb e c) +
            sideLoadBefore
              (onlineOwnerBatchForest (branchForest P) assign e n hn)
              (onlineOwnerBatchFixedOrientation (branchForest P) assign orient e
                n hn) i c) ≤
        (2 * quota + P.numParts *
            thresholdReserve rootRho
              #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
                E0 Mb e c)) +
          sideLoad (onlineFiberForest (branchForest P) assign e)
            (globalFixedFiberOrientation (branchForest P) assign orient e) c +
          (1 + thresholdReserve rootRho
            #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
              E0 Mb e c)) := by
      omega
    have hloadReal :
        (((2 * quota + P.numParts *
              thresholdReserve rootRho
                #(richWhole Pcluster Gdegree threshold quota R miss Q
                  sourceDensity E0 Mb e c)) +
            globalFixedPrefixLoad (branchForest P) assign orient e n c +
            (1 + thresholdReserve rootRho
                #(richWhole Pcluster Gdegree threshold quota R miss Q
                  sourceDensity E0 Mb e c) +
              sideLoadBefore
                (onlineOwnerBatchForest (branchForest P) assign e n hn)
                (onlineOwnerBatchFixedOrientation (branchForest P) assign orient
                  e n hn) i c) : ℕ) : ℝ) ≤
          ((2 * quota + P.numParts *
              thresholdReserve rootRho
                #(richWhole Pcluster Gdegree threshold quota R miss Q
                  sourceDensity E0 Mb e c)) +
            sideLoad (onlineFiberForest (branchForest P) assign e)
              (globalFixedFiberOrientation (branchForest P) assign orient e) c +
            (1 + thresholdReserve rootRho
              #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
                E0 Mb e c)) : ℕ) := by
      exact_mod_cast hloadNat
    have hreal := hloadReal.trans
      ((D.eligible_margin c).trans (hdegree.trans hneighborCard))
    have hnat :
        (2 * quota + P.numParts *
            thresholdReserve rootRho
              #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
                E0 Mb e c)) +
          globalFixedPrefixLoad (branchForest P) assign orient e n c +
          (1 + thresholdReserve rootRho
              #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
                E0 Mb e c) +
            sideLoadBefore
              (onlineOwnerBatchForest (branchForest P) assign e n hn)
              (onlineOwnerBatchFixedOrientation (branchForest P) assign orient e
                n hn) i c) ≤
        #((richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
          e c).filter (G.Adj z)) := by
      exact_mod_cast hreal
    have hrootImage :
        extendedRootImage state.rootImage n hn z
            (onlineFiberOwner (branchForest P) assign e
              (selectedEquiv
                (onlineOwnerBatch (branchForest P) assign e n hn) i)) = z := by
      have hownerLocal :
          onlineFiberOwner (branchForest P) assign e
              (selectedEquiv
                (onlineOwnerBatch (branchForest P) assign e n hn) i) =
            ⟨n, hn⟩ := by
        change (branchForest P).owner j = ⟨n, hn⟩
        exact hjOwner
      rw [hownerLocal, extendedRootImage_current]
    simpa only [assign, c, hrootImage] using hnat
  component := by
    intro i c
    have hsize :
        (onlineOwnerBatchForest (branchForest P)
            (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
              (threshold := threshold) (quota := quota) (R := R) (miss := miss)
              (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
              (P := P) (S := S) (A := A)) e n hn).size i ≤ small := by
      change (branchForest P).branches.size
        (onlineOwnerBatchBranch (branchForest P)
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A)) e n hn i) ≤ small
      exact canonical_branch_size_le_small P _
    have hsizeReal :
        ((onlineOwnerBatchForest (branchForest P)
            (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
              (threshold := threshold) (quota := quota) (R := R) (miss := miss)
              (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
              (P := P) (S := S) (A := A)) e n hn).size i : ℝ) ≤ small := by
      exact_mod_cast hsize
    have hbase := D.component_margin c
    linarith

end RichFixedFullFiberEdgeFacts

/-- Rich fixed-plan realization with uniformity, density, and permanent
side-cleaning loss derived internally from the reduced-pair host. -/
theorem exists_treeCopy_of_richFixedHostScalarOnline
    (hT : T.IsTree)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (rootRho rootDensity : ℝ)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (F : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        (richFixedRootTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A orient))
    (initialRootImage : Fin P.numParts → Bv)
    (facts : ∀ e, RichFixedFullFiberEdgeFacts Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H orient F e) :
    Nonempty (T.Copy G) := by
  apply exists_treeCopy_of_richFixedScalarOnline Pcluster Gdegree threshold
    quota R miss Q sourceDensity E0 Mb P S A hT G hdisjoint rootRho
    rootDensity H orient F initialRootImage (fun _ ↦ rootRho)
    (fun _ ↦ rootDensity)
  intro n hn state z hz hzf e
  exact (facts e).toFixedFullFiberOnlineOwnerEdgeFacts
    Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb P S A G
    rootRho rootDensity H orient F n hn state.state.state z e
    (onlineRootEligible_subset P G
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A))
      (richFixedCleanEndpoint Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho orient)
      (richFixedCandidate Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb P S A G rootRho orient) n hn state.state hz)

end Erdos547b.ZhaoClaim615RichGlobalFixedHostFacts

#print axioms Erdos547b.ZhaoClaim615RichGlobalFixedHostFacts.card_richFixedParentLowDegree_le_thresholdReserve
#print axioms Erdos547b.ZhaoClaim615RichGlobalFixedHostFacts.richFixedCandidate_branchRoot_degree
#print axioms Erdos547b.ZhaoClaim615RichGlobalFixedHostFacts.RichFixedFullFiberEdgeFacts.toFixedFullFiberOnlineOwnerEdgeFacts
#print axioms Erdos547b.ZhaoClaim615RichGlobalFixedHostFacts.exists_treeCopy_of_richFixedHostScalarOnline
