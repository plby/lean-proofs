/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichExceptionalForcing
import ErdosProblems.Erdos547b.Claim615RichGlobalOnlinePlanCertifiedApplication

/-!
# Exceptional-family forcing through the synchronized online backend

The older `FixedPhysicalApplicationPackage` routes a whole matching-edge
fiber through one static endpoint-capacity estimate.  Zhao's Lemma 5.8 does
not have such an estimate: its threshold and Appendix cases are realized
owner by owner in the current residual endpoints.  This file gives the
exceptional-family contrapositive the correct non-result boundary.  The
package contains only a source allocation, a root-cleaning certificate, and
the plan-certified local source/live-host data used by the synchronized
online recursion.
-/

open scoped BigOperators SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichExceptionalOnlineForcing

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615RichDynamicApplication
open Erdos547b.ZhaoClaim615RichDynamicRootTargetPlan
open Erdos547b.ZhaoClaim615RichDynamicPlannedRootCleaning
open Erdos547b.ZhaoClaim615RichGlobalOnlinePlannedApplication
open Erdos547b.ZhaoClaim615RichGlobalOnlineSideApplication
open Erdos547b.ZhaoClaim615RichGlobalOnlinePlanCertifiedApplication
open Erdos547b.ZhaoClaim615RichExceptionalForcing
open Erdos547b.ZhaoLemma615
open Erdos547b.ZhaoLemma58GlobalOwnerOnlineState
open Erdos547b.ZhaoLemma58GlobalCutOnline
open Erdos547b.ZhaoLemma58GlobalPlannedOnlineState
open Erdos547b.ZhaoLemma58GlobalPlannedOwnerSuccessor
open Erdos547b.ZhaoRoundedScales
open Erdos547b.ZhaoSection6EventualParameters

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

variable {L : Finset (EvenPadding I)} {eta0 N targetB cap : ℝ}
variable {which : ExceptionalCase} {count cardBound : ℕ}
variable
  (E0 : SelectedExceptionalEdges Q sourceDensity L eta0 which count)
variable
  (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)

variable (P : ZhaoForestPartition T globalRoot small)
variable (G : SimpleGraph Bv) [DecidableRel G.Adj]

/-- The plan-certified local callback needed by the synchronized rich
online constructor.  Naming it keeps the package below shallow without
changing its mathematical content. -/
abbrev RichPlannedOnlineSuccessor
    {available : Finset
      (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
    {target slack : ℕ}
    (S : SelectedF0 P available target slack)
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      cap0 cap1 capb)
    (rootRho : ℝ) (plan : RootTargetPlan P)
    (edgeRho edgeDensity : PhysicalIndex Q sourceDensity E0 Mb → ℝ) :=
  ∀ n (hn : n < P.numParts)
    (state : PlannedCutOnlineOwnerPrefixState P G
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A))
      (richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho plan)
      (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho plan)
      plan.coordinateSides n)
    z,
    z ∈ onlineRootEligible P G
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A))
      (richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho plan)
      (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho plan) n hn state.state →
    (∀ q, q.val < n → z ≠ state.state.state.rootImage q) →
    PlannedOnlineOwnerSuccessorData (branchForest P) G
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A))
      (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
      (richOnlineSideEndpoint Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho plan)
      edgeRho edgeDensity
      (plannedRootCandidate Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A G rootRho plan)
      plan.branchRootSides plan.coordinateSides n hn state.state.state z

/-- Host-side source data after the finite branch-to-edge allocation has
been chosen.  This is deliberately separate from that combinatorial
allocation so the two exceptional cases can reuse the same online forcing
theorem. -/
structure OnlineRealizationData
    {available : Finset
      (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
    {target slack : ℕ}
    (S : SelectedF0 P available target slack)
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      cap0 cap1 capb) : Type (max u v w) where
  rootRho : ℝ
  rootDensity : ℝ
  pairRealization : ReducedPairRealization Pcluster R G rootRho rootDensity
  plan : RootTargetPlan P
  rootCleaning : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota
    R miss Q sourceDensity E0 Mb P S A G rootRho rootDensity pairRealization
      plan
  initialRootImage : Fin P.numParts → Bv
  edgeRho : PhysicalIndex Q sourceDensity E0 Mb → ℝ
  edgeDensity : PhysicalIndex Q sourceDensity E0 Mb → ℝ
  successor : RichPlannedOnlineSuccessor Pcluster Gdegree threshold quota R
    miss Q sourceDensity E0 Mb P G S A rootRho plan edgeRho edgeDensity

/-- Non-result data for one source-faithful exceptional-family realization.
The recursive field is a family of `PlannedOwnerLocalStepData`; it contains
no graph copy, embedding, continuation, or containment conclusion. -/
structure OnlinePhysicalApplicationPackage
    (hT : T.IsTree) : Type (max u v w) where
  available : Finset
    (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)
  target : ℕ
  slack : ℕ
  selected : SelectedF0 P available target slack
  cap0 : K0 Q sourceDensity E0 → ℕ
  cap1 : K1 Q sourceDensity E0 Mb → ℕ
  capb : Kb Q sourceDensity Mb → ℕ
  allocation : PhysicalSourceAllocationWith Q sourceDensity P selected E0 Mb
    cap0 cap1 capb
  rootRho : ℝ
  rootDensity : ℝ
  pairRealization : ReducedPairRealization Pcluster R G rootRho rootDensity
  plan : RootTargetPlan P
  rootCleaning : RichPlannedRootCleaningFacts Pcluster Gdegree threshold quota
    R miss Q sourceDensity E0 Mb P selected allocation G rootRho rootDensity
      pairRealization plan
  initialRootImage : Fin P.numParts → Bv
  edgeRho : PhysicalIndex Q sourceDensity E0 Mb → ℝ
  edgeDensity : PhysicalIndex Q sourceDensity E0 Mb → ℝ
  successor : RichPlannedOnlineSuccessor Pcluster Gdegree threshold quota R
    miss Q sourceDensity E0 Mb P G selected allocation rootRho plan edgeRho
      edgeDensity

/-- Combine a finite source allocation with its source/live-host online
realization data. -/
def onlinePhysicalApplicationPackageOfAllocation
    {hT : T.IsTree}
    {available : Finset
      (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
    {target slack : ℕ}
    (S : SelectedF0 P available target slack)
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      cap0 cap1 capb)
    (D : OnlineRealizationData Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P G S A) :
    OnlinePhysicalApplicationPackage Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P G hT where
  available := available
  target := target
  slack := slack
  selected := S
  cap0 := cap0
  cap1 := cap1
  capb := capb
  allocation := A
  rootRho := D.rootRho
  rootDensity := D.rootDensity
  pairRealization := D.pairRealization
  plan := D.plan
  rootCleaning := D.rootCleaning
  initialRootImage := D.initialRootImage
  edgeRho := D.edgeRho
  edgeDensity := D.edgeDensity
  successor := D.successor

/-- Realize an online package internally through the synchronized
plan-certified owner recursion. -/
theorem OnlinePhysicalApplicationPackage.isContained
    {hT : T.IsTree}
    (D : OnlinePhysicalApplicationPackage Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P G hT)
    (hdisjoint : Disjoint E0.selected Mb.selected) :
    T.IsContained G := by
  exact exists_treeCopy_of_richPlanCertifiedOnline Pcluster Gdegree threshold
    quota R miss Q sourceDensity E0 Mb P D.selected D.allocation hT G
    hdisjoint D.rootRho D.rootDensity D.pairRealization D.plan D.rootCleaning
    D.initialRootImage D.edgeRho D.edgeDensity D.successor

/-- A large exceptional away-family forces containment using only online
source/live-host packages. -/
theorem isContained_of_largeExceptionalAway_online
    {beta : ℚ} (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    {reducedK : ℕ} (hreducedK : section6K₀ beta ≤ reducedK)
    (A B : EvenPadding I) (hA : A = Sum.inl Q.A)
    (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
    (hMbCard : Mb.selected.card ≤ claim617Q beta reducedK)
    (hlarge : (eta beta : ℝ) * reducedK ≤
      (#(exceptionalAwayFamily
        (Erdos547b.ZhaoRichClaim61Lemma611.edgesAwayFromDistinguished
          Q.claim67.M L A B)
        (fun e c ↦ sourceDensity A (orientedEndpoint Q.claim67.M L e c))
        (eta beta : ℝ) which) : ℝ))
    (hT : T.IsTree)
    (packages : ∀ E0 : SelectedExceptionalEdges Q sourceDensity L
        (eta beta : ℝ) which
        (upperScale (((eta beta : ℝ) * reducedK) / 2)),
      Disjoint E0.selected Mb.selected →
        Nonempty (OnlinePhysicalApplicationPackage Pcluster Gdegree threshold
          quota R miss Q sourceDensity E0 Mb P G hT)) :
    T.IsContained G := by
  have hfamily : (eta beta : ℝ) * reducedK ≤
      (#(exceptionalFamily Q sourceDensity L (eta beta : ℝ) which) : ℝ) := by
    calc
      (eta beta : ℝ) * reducedK ≤
          (#(exceptionalAwayFamily
            (Erdos547b.ZhaoRichClaim61Lemma611.edgesAwayFromDistinguished
              Q.claim67.M L A B)
            (fun e c ↦ sourceDensity A
              (orientedEndpoint Q.claim67.M L e c))
            (eta beta : ℝ) which) : ℝ) := hlarge
      _ ≤ (#(exceptionalFamily Q sourceDensity L (eta beta : ℝ)
          which) : ℝ) := by
        exact_mod_cast Finset.card_le_card
          (exceptionalAwayFamily_subset_exceptionalFamily
            (Pcluster := Pcluster) (Gdegree := Gdegree)
            (threshold := threshold) (quota := quota) (R := R)
            (miss := miss) (Q := Q) (sourceDensity := sourceDensity)
            (which := which) (A := A) (B := B) (L := L)
            (eta0 := (eta beta : ℝ)) hA)
  obtain ⟨⟨E0, hdisjoint⟩⟩ :=
    exists_eventualHalfSelectedExceptionalEdges_avoiding Q sourceDensity
      hbeta hbetaOne hreducedK L which Mb.selected hfamily hMbCard
  obtain ⟨D⟩ := packages E0 hdisjoint
  exact OnlinePhysicalApplicationPackage.isContained
    (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
    (quota := quota) (R := R) (miss := miss) (Q := Q)
    (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) (P := P)
    (G := G) D hdisjoint

/-- Contrapositive online form consumed by the rich Lemma-6.11 constructor. -/
theorem exceptionalAway_families_lt_of_onlinePackages
    {beta : ℚ} (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    {reducedK : ℕ} (hreducedK : section6K₀ beta ≤ reducedK)
    (A B : EvenPadding I) (hA : A = Sum.inl Q.A)
    (hL : L = padFinset
      (largeClustersAtLeast Pcluster Gdegree threshold quota))
    (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
    (hMbCard : Mb.selected.card ≤ claim617Q beta reducedK)
    (hT : T.IsTree)
    (unbalancedPackages : ∀ E0 : SelectedExceptionalEdges Q sourceDensity L
        (eta beta : ℝ) .unbalanced
        (upperScale (((eta beta : ℝ) * reducedK) / 2)),
      Disjoint E0.selected Mb.selected →
        Nonempty (OnlinePhysicalApplicationPackage Pcluster Gdegree threshold
          quota R miss Q sourceDensity E0 Mb P G hT))
    (nonextremePackages : ∀ E0 : SelectedExceptionalEdges Q sourceDensity L
        (eta beta : ℝ) .nonextreme
        (upperScale (((eta beta : ℝ) * reducedK) / 2)),
      Disjoint E0.selected Mb.selected →
        Nonempty (OnlinePhysicalApplicationPackage Pcluster Gdegree threshold
          quota R miss Q sourceDensity E0 Mb P G hT))
    (hnot : ¬ T.IsContained G) :
    (((exceptionalAwayFamily
      (Erdos547b.ZhaoRichClaim61Lemma611.edgesAwayFromDistinguished
        Q.claim67.M L A B)
      (fun e c ↦ sourceDensity A (orientedEndpoint Q.claim67.M L e c))
      (eta beta : ℝ) .unbalanced).card : ℕ) : ℝ) <
        (eta beta : ℝ) * reducedK ∧
    (((exceptionalAwayFamily
      (Erdos547b.ZhaoRichClaim61Lemma611.edgesAwayFromDistinguished
        Q.claim67.M L A B)
      (fun e c ↦ sourceDensity A (orientedEndpoint Q.claim67.M L e c))
      (eta beta : ℝ) .nonextreme).card : ℕ) : ℝ) <
        (eta beta : ℝ) * reducedK := by
  subst L
  have hforce :
      (eta beta : ℝ) * reducedK ≤
          ((unbalancedEdges
            (Erdos547b.ZhaoRichClaim61Lemma611.edgesAwayFromDistinguished
              Q.claim67.M
                (padFinset
                  (largeClustersAtLeast Pcluster Gdegree threshold quota)) A B)
            (fun e c ↦ sourceDensity A
              (orientedEndpoint Q.claim67.M
                (padFinset
                  (largeClustersAtLeast Pcluster Gdegree threshold quota)) e c))
            (eta beta : ℝ)).card : ℝ) ∨
        (eta beta : ℝ) * reducedK ≤
          ((nonextremeEdges
            (Erdos547b.ZhaoRichClaim61Lemma611.edgesAwayFromDistinguished
              Q.claim67.M
                (padFinset
                  (largeClustersAtLeast Pcluster Gdegree threshold quota)) A B)
            (fun e c ↦ sourceDensity A
              (orientedEndpoint Q.claim67.M
                (padFinset
                  (largeClustersAtLeast Pcluster Gdegree threshold quota)) e c))
            (eta beta : ℝ)).card : ℝ) → T.IsContained G := by
    intro hlarge
    rcases hlarge with hlarge | hlarge
    · exact isContained_of_largeExceptionalAway_online Pcluster Gdegree
        threshold quota R miss Q sourceDensity P G hbeta hbetaOne hreducedK A B
        hA Mb hMbCard (by simpa only [exceptionalAwayFamily] using hlarge) hT
        unbalancedPackages
    · exact isContained_of_largeExceptionalAway_online Pcluster Gdegree
        threshold quota R miss Q sourceDensity P G hbeta hbetaOne hreducedK A B
        hA Mb hMbCard (by simpa only [exceptionalAwayFamily] using hlarge) hT
        nonextremePackages
  have hsmall :=
    Erdos547b.ZhaoRichClaim61Lemma611.exceptional_families_away_lt_of_not_contained
      T G Q.claim67 A B sourceDensity (eta beta : ℝ) (reducedK : ℝ)
        hforce hnot
  simpa only [exceptionalAwayFamily] using hsmall

end Erdos547b.ZhaoClaim615RichExceptionalOnlineForcing

#print axioms Erdos547b.ZhaoClaim615RichExceptionalOnlineForcing.OnlinePhysicalApplicationPackage.isContained
#print axioms Erdos547b.ZhaoClaim615RichExceptionalOnlineForcing.exceptionalAway_families_lt_of_onlinePackages
