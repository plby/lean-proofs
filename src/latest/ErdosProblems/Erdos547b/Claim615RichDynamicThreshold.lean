/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichDynamicApplication
import ErdosProblems.Erdos547b.Claim615RichPhysicalPartTwo

/-!
# Dynamic threshold fibers for rich Claim 6.15

This is the source-faithful replacement for the static endpoint-load cap.
A Part-1/2 source orientation is realized in the dynamically remaining
regular-pair endpoints, while permanent reserve deletion and every internal
cut-parent exception are charged exactly once.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichDynamicThreshold

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615RichDynamicHostLayout
open Erdos547b.ZhaoClaim615RichDynamicApplication
open Erdos547b.ZhaoClaim615RichPhysicalFiberPlan
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58CutForestReconstruction
open Erdos547b.ZhaoLemma58CutEdgeLocal
open Erdos547b.ZhaoLemma58FullCutTree
open Erdos547b.ZhaoLemma54ThresholdOrientation
open Erdos547b.ZhaoLemma54ThresholdNumerics
open Erdos547b.ZhaoLemma54ThresholdSourceNumerics

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
variable (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
  cap0 cap1 capb)

/-- Package the checked canonical-threshold dynamic constructor for one
literal rich physical edge.  The remaining premises are only scalar loss,
root-neighbour, and small-component inequalities on that edge. -/
theorem richThresholdCutEdgeDatum
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (Hpair : ReducedPairRealization Pcluster R G rho density)
    (rootImage : Fin P.numParts → Bv)
    (e : PhysicalIndex Q sourceDensity E0 Mb)
    (ratio dx dy gamma epsilon N0 : ℝ)
    (lowSide highSide : Fin 2)
    (Dsource : ClassifiedThresholdOwnerNumerics
      (cutFiberForest P
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e)
      ratio dx dy gamma epsilon N0 small)
    (hsides : highSide ≠ lowSide)
    (hfactor : 0 ≤ density - rho)
    (permanentBound rootLoss : Fin 2 → ℕ)
    (hpermanent : ∀ c,
      #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c \
        richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb e c) ≤ permanentBound c)
    (htypical : ∀ c (j : CutIndex P),
      #(cutRootNonneighbors P G rootImage
          (richEndpoint Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb) e c j) ≤ rootLoss c)
    (htotal : ∀ c,
      globalCutLossBound P permanentBound rootLoss c +
          thresholdHighBudget dy gamma N0 +
          thresholdReserve rho
            #(richWhole Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb e c) ≤
        #(richWhole Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb e c))
    (heligible : ∀
      (base : Fin (matchingFiber
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e).card → Fin 2 ≃ Fin 2)
      (hbase : ∀ t c,
        2 * sideLoadPrefix
            (cutFiberForest P
              (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
                (threshold := threshold) (quota := quota) (R := R)
                (miss := miss) (Q := Q) (sourceDensity := sourceDensity)
                (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)) e)
            base t c ≤
          prefixOrder
            (cutFiberForest P
              (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
                (threshold := threshold) (quota := quota) (R := R)
                (miss := miss) (Q := Q) (sourceDensity := sourceDensity)
                (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)) e) t +
            small),
      let F := cutFiberForest P
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e
      let O := actualThresholdSwitchOrientation F small
        (thresholdLowBudget dx gamma N0)
        (thresholdHighBudget dy gamma N0) lowSide highSide Dsource.small
        hsides (Dsource.suffix_display highSide) base hbase
      ∀ i,
        let c := branchRootSide F O.orient i
        globalCutLossBound P permanentBound rootLoss c +
            (1 + thresholdReserve rho
                #(richWhole Pcluster Gdegree threshold quota R miss Q
                  sourceDensity E0 Mb e c) +
              sideLoadBefore F O.orient i c) ≤
          #((richWhole Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb e c).filter
            (G.Adj (rootImage (cutFiberOwner P
              (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
                (threshold := threshold) (quota := quota) (R := R)
                (miss := miss) (Q := Q) (sourceDensity := sourceDensity)
                (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)) e i)))))
    (hcomponent : ∀ i c,
      ((cutFiberForest P
          (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R) (miss := miss)
            (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
            (P := P) (S := S) (A := A)) e).size i : ℝ) +
          rho * (#(richWhole Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb e c) : ℝ) + 1 ≤
        (density - rho) *
          ((#(richWhole Pcluster Gdegree threshold quota R miss Q
              sourceDensity E0 Mb e c) : ℝ) -
            globalCutLossBound P permanentBound rootLoss c -
            thresholdHighBudget dy gamma N0)) :
    RichCutEdgeDatum Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb P S A G rootImage (fun _ ↦ rho) (fun _ ↦ density) e := by
  let whole := richWhole Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb e
  let endpoint := richEndpoint Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb e
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  let F := cutFiberForest P assign e
  let owner := cutFiberOwner P assign e
  let bad := cutParentBad P G rootImage
    (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
    e
  let globalBad := globalCutParentBad P G rootImage
    (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
    e
  have hendpoint : ∀ c, endpoint c ⊆ whole c := by
    exact endpoint_subset_whole
      (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
      (quota := quota) (R := R) (miss := miss) (Q := Q)
      (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) e
  have hglobalSub : ∀ c, globalBad c ⊆ endpoint c := by
    intro c
    exact Finset.filter_subset _ _
  have hpair := whole_pair
    (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
    (quota := quota) (R := R) (miss := miss) (Q := Q)
    (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    G rho density Hpair e
  have hwholeDisjoint : Disjoint (whole 0) (whole 1) :=
    whole_disjoint
      (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
      (quota := quota) (R := R) (miss := miss) (Q := Q)
      (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      hdisjoint e
  have hloss : ∀ c,
      #(Erdos547b.ZhaoLemma58CombinedResidual.combinedDeleted whole endpoint
        (fun _ ↦ ∅) globalBad c) ≤
        globalCutLossBound P permanentBound rootLoss c := by
    intro c
    exact card_combinedDeleted_global_le P G rootImage
      (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
      (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb) e permanentBound rootLoss hpermanent htypical c
  exact ⟨CutEdgeLocalData.thresholdOfCanonicalCombinedBounds P F G G
    (fun i ↦ rootImage (owner i)) whole endpoint owner bad globalBad
    rho density ratio dx dy gamma epsilon N0 small lowSide highSide Dsource
    hsides hendpoint hglobalSub hpair.1 hwholeDisjoint hpair.2 hfactor
    (globalCutLossBound P permanentBound rootLoss) hloss htotal heligible
    hcomponent⟩

end Erdos547b.ZhaoClaim615RichDynamicThreshold

#print axioms Erdos547b.ZhaoClaim615RichDynamicThreshold.richThresholdCutEdgeDatum
