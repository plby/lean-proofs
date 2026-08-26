/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichDynamicThreshold
import ErdosProblems.Erdos547b.Claim615RichDynamicPlannedApplication

/-!
# The three rich threshold families

This module packages the source and live-host facts needed by one canonical
threshold fiber, then assembles the exceptional, remaining, and reserved
families into the concrete `CutEdgeData` consumed by the full cut-tree
backend.  The package contains no embedding or copy result.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichDynamicThresholdFamilies

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
open Erdos547b.ZhaoClaim615RichDynamicThreshold
open Erdos547b.ZhaoClaim615RichDynamicRootLayout
open Erdos547b.ZhaoClaim615RichDynamicRootTargets
open Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan
open Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning
open Erdos547b.ZhaoClaim615RichDynamicPlannedApplication
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58CutForestReconstruction
open Erdos547b.ZhaoLemma58CutEdgeLocal
open Erdos547b.ZhaoLemma58FullCutTree
open Erdos547b.ZhaoLemma58RootCandidateCleaning
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
variable
  (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
    cap0 cap1 capb)

/-- The literal forest assigned to one rich physical edge. -/
abbrev richThresholdFiberForest
    (e : PhysicalIndex Q sourceDensity E0 Mb) :=
  cutFiberForest P
    (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A)) e

/-- Source numerics and residual host inequalities for one complete
Parts-1/2 physical fiber.  The canonical orientation is determined by the
`source` field, so parent-neighbour eligibility is required only on the
endpoint actually used by each branch root. -/
structure RichThresholdFiberFacts
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → Bv)
    (rho density : ℝ)
    (e : PhysicalIndex Q sourceDensity E0 Mb) : Type (max u v w) where
  ratio : ℝ
  dx : ℝ
  dy : ℝ
  gamma : ℝ
  epsilon : ℝ
  N0 : ℝ
  lowSide : Fin 2
  highSide : Fin 2
  source : ClassifiedThresholdOwnerNumerics
    (richThresholdFiberForest Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A e)
    ratio dx dy gamma epsilon N0 small
  sides_ne : highSide ≠ lowSide
  factor_nonneg : 0 ≤ density - rho
  permanentBound : Fin 2 → ℕ
  rootLoss : Fin 2 → ℕ
  permanent : ∀ c,
    #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
        e c \
      richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0
        Mb e c) ≤ permanentBound c
  typical : ∀ c (j : CutIndex P),
    #(cutRootNonneighbors P G rootImage
      (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0
        Mb) e c j) ≤ rootLoss c
  total : ∀ c,
    globalCutLossBound P permanentBound rootLoss c +
        thresholdHighBudget dy gamma N0 +
        thresholdReserve rho
          #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb e c) ≤
      #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0
        Mb e c)
  eligible : ∀
    (base : Fin (matchingFiber
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) e).card → Fin 2 ≃ Fin 2)
    (hbase : ∀ t c,
      2 * sideLoadPrefix
          (richThresholdFiberForest Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A e) base t c ≤
        prefixOrder
          (richThresholdFiberForest Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb P S A e) t + small),
    let F := richThresholdFiberForest Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A e
    let O := actualThresholdSwitchOrientation F small
      (thresholdLowBudget dx gamma N0) (thresholdHighBudget dy gamma N0)
      lowSide highSide source.small sides_ne
      (source.suffix_display highSide) base hbase
    ∀ i,
      let c := branchRootSide F O.orient i
      globalCutLossBound P permanentBound rootLoss c +
          (1 + thresholdReserve rho
              #(richWhole Pcluster Gdegree threshold quota R miss Q
                sourceDensity E0 Mb e c) +
            sideLoadBefore F O.orient i c) ≤
        #((richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0
            Mb e c).filter
          (G.Adj (rootImage (cutFiberOwner P
            (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
              (threshold := threshold) (quota := quota) (R := R)
              (miss := miss) (Q := Q) (sourceDensity := sourceDensity)
              (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)) e i))))
  component : ∀ i c,
    ((richThresholdFiberForest Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A e).size i : ℝ) +
        rho * (#(richWhole Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb e c) : ℝ) + 1 ≤
      (density - rho) *
        ((#(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
            E0 Mb e c) : ℝ) -
          globalCutLossBound P permanentBound rootLoss c -
          thresholdHighBudget dy gamma N0)

namespace RichThresholdFiberFacts

/-- Build one fiber package from a classified source orientation and the
remaining residual inequalities.  The permanent `A₀/B₀` deletion is derived
internally and fixed to its exact uniform bound `2 * quota`. -/
def ofSource
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → Bv)
    (rho density : ℝ)
    (e : PhysicalIndex Q sourceDensity E0 Mb)
    (ratio dx dy gamma epsilon N0 : ℝ)
    (lowSide highSide : Fin 2)
    (Dsource : ClassifiedThresholdOwnerNumerics
      (richThresholdFiberForest Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A e)
      ratio dx dy gamma epsilon N0 small)
    (hsides : highSide ≠ lowSide)
    (hfactor : 0 ≤ density - rho)
    (rootLoss : Fin 2 → ℕ)
    (htypical : ∀ c (j : CutIndex P),
      #(cutRootNonneighbors P G rootImage
        (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb) e c j) ≤ rootLoss c)
    (htotal : ∀ c,
      globalCutLossBound P (fun _ ↦ 2 * quota) rootLoss c +
          thresholdHighBudget dy gamma N0 +
          thresholdReserve rho
            #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
              E0 Mb e c) ≤
        #(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0
          Mb e c))
    (heligible : ∀
      (base : Fin (matchingFiber
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e).card → Fin 2 ≃ Fin 2)
      (hbase : ∀ t c,
        2 * sideLoadPrefix
            (richThresholdFiberForest Pcluster Gdegree threshold quota R miss
              Q sourceDensity E0 Mb P S A e) base t c ≤
          prefixOrder
            (richThresholdFiberForest Pcluster Gdegree threshold quota R miss
              Q sourceDensity E0 Mb P S A e) t + small),
      let F := richThresholdFiberForest Pcluster Gdegree threshold quota R
        miss Q sourceDensity E0 Mb P S A e
      let O := actualThresholdSwitchOrientation F small
        (thresholdLowBudget dx gamma N0) (thresholdHighBudget dy gamma N0)
        lowSide highSide Dsource.small hsides
        (Dsource.suffix_display highSide) base hbase
      ∀ i,
        let c := branchRootSide F O.orient i
        globalCutLossBound P (fun _ ↦ 2 * quota) rootLoss c +
            (1 + thresholdReserve rho
                #(richWhole Pcluster Gdegree threshold quota R miss Q
                  sourceDensity E0 Mb e c) +
              sideLoadBefore F O.orient i c) ≤
          #((richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
              E0 Mb e c).filter
            (G.Adj (rootImage (cutFiberOwner P
              (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
                (threshold := threshold) (quota := quota) (R := R)
                (miss := miss) (Q := Q) (sourceDensity := sourceDensity)
                (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)) e i)))))
    (hcomponent : ∀ i c,
      ((richThresholdFiberForest Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A e).size i : ℝ) +
          rho * (#(richWhole Pcluster Gdegree threshold quota R miss Q
            sourceDensity E0 Mb e c) : ℝ) + 1 ≤
        (density - rho) *
          ((#(richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
              E0 Mb e c) : ℝ) -
            globalCutLossBound P (fun _ ↦ 2 * quota) rootLoss c -
            thresholdHighBudget dy gamma N0)) :
    RichThresholdFiberFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootImage rho density e where
  ratio := ratio
  dx := dx
  dy := dy
  gamma := gamma
  epsilon := epsilon
  N0 := N0
  lowSide := lowSide
  highSide := highSide
  source := Dsource
  sides_ne := hsides
  factor_nonneg := hfactor
  permanentBound := fun _ ↦ 2 * quota
  rootLoss := rootLoss
  permanent := card_whole_sdiff_endpoint_le_two_mul_quota Pcluster Gdegree
    threshold quota R miss Q sourceDensity E0 Mb e
  typical := htypical
  total := htotal
  eligible := heligible
  component := hcomponent

/-- Convert source/live-host facts into the concrete edge-local result. -/
theorem cutEdgeDatum
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (Hpair : ReducedPairRealization Pcluster R G rho density)
    (rootImage : Fin P.numParts → Bv)
    (e : PhysicalIndex Q sourceDensity E0 Mb)
    (F : RichThresholdFiberFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootImage rho density e) :
    RichCutEdgeDatum Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb P S A G rootImage (fun _ ↦ rho) (fun _ ↦ density) e := by
  exact richThresholdCutEdgeDatum Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A G hdisjoint Hpair rootImage e F.ratio F.dx F.dy
    F.gamma F.epsilon F.N0 F.lowSide F.highSide F.source F.sides_ne
    F.factor_nonneg F.permanentBound F.rootLoss F.permanent F.typical F.total
    F.eligible F.component

end RichThresholdFiberFacts

/-- Assemble source-faithful threshold data for all three physical families.
The family hypotheses contain only source numerics and residual host facts;
the local embeddings are constructed internally by `cutEdgeDatum`. -/
theorem richCutEdgeData_partTwo_partOne
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (Hpair : ReducedPairRealization Pcluster R G rho density)
    (rootImage : Fin P.numParts → Bv)
    (h0 : ∀ e : K0 Q sourceDensity E0,
      RichThresholdFiberFacts Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootImage rho density
        (exceptionalIndex Q sourceDensity E0 Mb e))
    (h1 : ∀ e : K1 Q sourceDensity E0 Mb,
      RichThresholdFiberFacts Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootImage rho density
        (remainingIndex Q sourceDensity E0 Mb e))
    (hb : ∀ e : Kb Q sourceDensity Mb,
      RichThresholdFiberFacts Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootImage rho density
        (reservedIndex Q sourceDensity E0 Mb e)) :
    CutEdgeData P G G rootImage
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A))
      (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
      (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0
        Mb)
      (fun _ ↦ rho) (fun _ ↦ density) := by
  apply richCutEdgeData_of_families Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A G rootImage (fun _ ↦ rho) (fun _ ↦ density)
  · intro e
    exact (h0 e).cutEdgeDatum Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G hdisjoint Hpair rootImage _
  · intro e
    exact (h1 e).cutEdgeDatum Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G hdisjoint Hpair rootImage _
  · intro e
    exact (hb e).cutEdgeDatum Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G hdisjoint Hpair rootImage _

/-- Membership certificate for a root map chosen from the planned target
cleaning. -/
abbrev RichPlannedRootSelection
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho : ℝ) (plan : RootTargetPlan P)
    (rootImage : Fin P.numParts → Bv) :=
  ∀ q, rootImage q ∈ rootCandidate G rootRho
    (rootWhole Pcluster Gdegree threshold quota R miss Q P)
    (rootRaw Pcluster Gdegree threshold quota R miss Q P)
    (richPlannedRootTargets Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A plan)
    (richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0
      Mb)
    (richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity E0
      Mb) q

/-- Complete Parts-1/2 application: planned cleaning chooses the roots, every
physical fiber is realized by its canonical threshold data, and the original
tree (including all cut edges) is reconstructed. -/
theorem exists_treeCopy_of_richPlannedThresholdFamilies
    (hT : T.IsTree)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (rho density : ℝ)
    (Hpair : ReducedPairRealization Pcluster R G rho density)
    (plan : RootTargetPlan P)
    (Froot : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A G rho density Hpair plan)
    (h0 : ∀ (rootImage : Fin P.numParts → Bv),
      RichPlannedRootSelection (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) G rho plan rootImage →
      ∀ e : K0 Q sourceDensity E0,
        RichThresholdFiberFacts Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootImage rho density
          (exceptionalIndex Q sourceDensity E0 Mb e))
    (h1 : ∀ (rootImage : Fin P.numParts → Bv),
      RichPlannedRootSelection (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) G rho plan rootImage →
      ∀ e : K1 Q sourceDensity E0 Mb,
        RichThresholdFiberFacts Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootImage rho density
          (remainingIndex Q sourceDensity E0 Mb e))
    (hb : ∀ (rootImage : Fin P.numParts → Bv),
      RichPlannedRootSelection (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) G rho plan rootImage →
      ∀ e : Kb Q sourceDensity Mb,
        RichThresholdFiberFacts Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A G rootImage rho density
          (reservedIndex Q sourceDensity E0 Mb e)) :
    Nonempty (T.Copy G) := by
  apply exists_treeCopy_of_richPlannedRootCleaningFacts Pcluster Gdegree
    threshold quota R miss Q sourceDensity E0 Mb P S A hT G hdisjoint rho
    density Hpair plan Froot (fun _ ↦ rho) (fun _ ↦ density)
  intro rootImage hroot
  exact richCutEdgeData_partTwo_partOne Pcluster Gdegree threshold quota R miss
    Q sourceDensity E0 Mb P S A G hdisjoint Hpair rootImage
      (h0 rootImage hroot) (h1 rootImage hroot) (hb rootImage hroot)

end Erdos547b.ZhaoClaim615RichDynamicThresholdFamilies

#print axioms Erdos547b.ZhaoClaim615RichDynamicThresholdFamilies.RichThresholdFiberFacts.cutEdgeDatum
#print axioms Erdos547b.ZhaoClaim615RichDynamicThresholdFamilies.RichThresholdFiberFacts.ofSource
#print axioms Erdos547b.ZhaoClaim615RichDynamicThresholdFamilies.richCutEdgeData_partTwo_partOne
#print axioms Erdos547b.ZhaoClaim615RichDynamicThresholdFamilies.exists_treeCopy_of_richPlannedThresholdFamilies
