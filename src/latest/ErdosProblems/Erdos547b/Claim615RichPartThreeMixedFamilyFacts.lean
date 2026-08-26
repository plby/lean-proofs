/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPartThreeMixedOnlineRealization

/-!
# Family-indexed facts for the mixed Part-3 online realization

The source construction naturally supplies Appendix facts on the selected
exceptional family and fixed-orientation facts on the remaining and reserved
families.  This file reindexes those three honest families through the
canonical physical `Fin` index.  It adds no embedding, copy, continuation, or
containment premise.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPartThreeMixedFamilyFacts

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
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
open Erdos547b.ZhaoClaim615RichPhysicalFiberPlan
open Erdos547b.ZhaoClaim615RichPhysicalPartThreeRootPlan
open Erdos547b.ZhaoClaim615RichDynamicApplication
open Erdos547b.ZhaoClaim615RichDynamicHostLayout
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615RichGlobalRootSidePlan
open Erdos547b.ZhaoClaim615RichRootSideOnlineRealization
open Erdos547b.ZhaoClaim615RichPartThreeOnlineRealization
open Erdos547b.ZhaoClaim615RichPartThreeMixedOnlineRealization
open Erdos547b.ZhaoClaim615RichExceptionalOnlineForcing
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters

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
variable {count cardBound : ℕ}
variable (E0 : SelectedExceptionalEdges Q sourceDensity L eta .nonextreme count)
variable (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
variable (P : ZhaoForestPartition T globalRoot small)
variable {target slack : ℕ}
variable (S : SelectedF0 P (nontrivialMajorBranches P) target slack)
variable {cap0 : K0 Q sourceDensity E0 → ℕ}
variable {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
variable {capb : Kb Q sourceDensity Mb → ℕ}
variable
  (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0 cap1 capb)

/-- A unified physical index is adaptive precisely when it is the canonical
image of an exceptional-family index. -/
def isExceptionalPhysicalIndex
    (e : PhysicalIndex Q sourceDensity E0 Mb) : Prop :=
  match (Fintype.equivFin
      (PhysicalEdge Q sourceDensity E0 Mb)).symm e with
  | Sum.inl _ => True
  | Sum.inr _ => False

/-- The three family-indexed collections of state-independent local facts.
The first field records the genuine nonextreme source-row fact that both
exceptional endpoints are admissible root sides. -/
structure PartThreeFamilyFullFiberFacts
    (hT : T.IsTree)
    (havailable : nontrivialMajorBranches P ⊆ halfBranches P)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ) (hrootRho : 0 ≤ rootRho)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (D : PhysicalPartThreeAuxiliaryRootPlan Q sourceDensity E0 Mb P S A)
    (Kroot : RichRootSideCleaningScalarFacts Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        (physicalRootGoodSidePlan.{v, w, u} Pcluster Gdegree threshold quota R
          miss Q sourceDensity E0 Mb)) : Type (max u v w) where
  exceptional_all : ∀ e0 c,
    Erdos547b.ZhaoClaim615RichPhysicalFiberPlan.physicalRootGood
      (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
      (quota := quota) (R := R) (miss := miss) (Q := Q)
      (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (exceptionalIndex Q sourceDensity E0 Mb e0) c
  appendix : ∀ e0,
    RichAppendixFullFiberEdgeFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rootRho rootDensity H
      (partThreeMixedPlan Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A D
          (isExceptionalPhysicalIndex (Pcluster := Pcluster)
            (Gdegree := Gdegree) (threshold := threshold) (quota := quota)
            (R := R) (miss := miss) Q sourceDensity E0 Mb))
      (partThreeMixedRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A hT havailable G rootRho rootDensity hrootRho
        H D (isExceptionalPhysicalIndex (Pcluster := Pcluster)
          (Gdegree := Gdegree) (threshold := threshold) (quota := quota)
          (R := R) (miss := miss) Q sourceDensity E0 Mb) Kroot)
      (exceptionalIndex Q sourceDensity E0 Mb e0)
  remaining : ∀ e1,
    RichRootSideFixedFullFiberEdgeFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rootRho rootDensity H
      (partThreeMixedPlan Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A D
          (isExceptionalPhysicalIndex (Pcluster := Pcluster)
            (Gdegree := Gdegree) (threshold := threshold) (quota := quota)
            (R := R) (miss := miss) Q sourceDensity E0 Mb))
      (partThreeMixedRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A hT havailable G rootRho rootDensity hrootRho
        H D (isExceptionalPhysicalIndex (Pcluster := Pcluster)
          (Gdegree := Gdegree) (threshold := threshold) (quota := quota)
          (R := R) (miss := miss) Q sourceDensity E0 Mb) Kroot)
      (partThreeAuxiliaryGlobalOrient (Pcluster := Pcluster)
        (Gdegree := Gdegree) (threshold := threshold) (quota := quota)
        (R := R) (miss := miss) Q sourceDensity E0 Mb P S D)
      (remainingIndex Q sourceDensity E0 Mb e1)
  reserved : ∀ eb,
    RichRootSideFixedFullFiberEdgeFacts Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A G rootRho rootDensity H
      (partThreeMixedPlan Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A D
          (isExceptionalPhysicalIndex (Pcluster := Pcluster)
            (Gdegree := Gdegree) (threshold := threshold) (quota := quota)
            (R := R) (miss := miss) Q sourceDensity E0 Mb))
      (partThreeMixedRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb P S A hT havailable G rootRho rootDensity hrootRho
        H D (isExceptionalPhysicalIndex (Pcluster := Pcluster)
          (Gdegree := Gdegree) (threshold := threshold) (quota := quota)
          (R := R) (miss := miss) Q sourceDensity E0 Mb) Kroot)
      (partThreeAuxiliaryGlobalOrient (Pcluster := Pcluster)
        (Gdegree := Gdegree) (threshold := threshold) (quota := quota)
        (R := R) (miss := miss) Q sourceDensity E0 Mb P S D)
      (reservedIndex Q sourceDensity E0 Mb eb)

/-- Reindex the literal exceptional/remaining/reserved families into the
single mixed-fiber record consumed by the synchronized recursion. -/
noncomputable def PartThreeFamilyFullFiberFacts.toMixed
    (hT : T.IsTree)
    (havailable : nontrivialMajorBranches P ⊆ halfBranches P)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ) (hrootRho : 0 ≤ rootRho)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (D : PhysicalPartThreeAuxiliaryRootPlan Q sourceDensity E0 Mb P S A)
    (Kroot : RichRootSideCleaningScalarFacts Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        (physicalRootGoodSidePlan.{v, w, u} Pcluster Gdegree threshold quota R
          miss Q sourceDensity E0 Mb))
    (K : PartThreeFamilyFullFiberFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A hT havailable G rootRho rootDensity hrootRho H
      D Kroot) :
    PartThreeMixedFullFiberFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A hT havailable G rootRho rootDensity hrootRho H
      D (isExceptionalPhysicalIndex (Pcluster := Pcluster)
        (Gdegree := Gdegree) (threshold := threshold) (quota := quota)
        (R := R) (miss := miss) Q sourceDensity E0 Mb) Kroot := by
  classical
  refine {
    adaptive_all := ?_
    appendix := ?_
    fixed := ?_
  }
  · intro e he c
    let tagged := (Fintype.equivFin
      (PhysicalEdge Q sourceDensity E0 Mb)).symm e
    have htag : Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb) tagged = e :=
      (Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb)).apply_symm_apply e
    rw [← htag] at he ⊢
    rcases tagged with e0 | e1
    · rw [mem_physicalRootGoodSidePlan]
      exact K.exceptional_all e0 c
    · have : False := by
        simpa only [isExceptionalPhysicalIndex, Equiv.symm_apply_apply] using he
      exact this.elim
  · intro e he
    let tagged := (Fintype.equivFin
      (PhysicalEdge Q sourceDensity E0 Mb)).symm e
    have htag : Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb) tagged = e :=
      (Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb)).apply_symm_apply e
    rw [← htag] at he ⊢
    rcases tagged with e0 | e1
    · exact K.appendix e0
    · have : False := by
        simpa only [isExceptionalPhysicalIndex, Equiv.symm_apply_apply] using he
      exact this.elim
  · intro e he
    let tagged := (Fintype.equivFin
      (PhysicalEdge Q sourceDensity E0 Mb)).symm e
    have htag : Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb) tagged = e :=
      (Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb)).apply_symm_apply e
    rw [← htag] at he ⊢
    rcases tagged with e0 | e1
    · have ha : isExceptionalPhysicalIndex (Pcluster := Pcluster)
          (Gdegree := Gdegree) (threshold := threshold) (quota := quota)
          (R := R) (miss := miss) Q sourceDensity E0 Mb
          (Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb)
            (Sum.inl e0)) := by
        simp only [isExceptionalPhysicalIndex, Equiv.symm_apply_apply]
      exact (he ha).elim
    · rcases e1 with e1 | eb
      · exact K.remaining e1
      · exact K.reserved eb

/-- Family-wise source/live-host facts give the complete non-result online
realization datum.  This is the direct callback expected by the source
allocation package constructor. -/
noncomputable def onlineRealizationDataOfPartThreeFamilyFullFiberFacts
    (hT : T.IsTree)
    (havailable : nontrivialMajorBranches P ⊆ halfBranches P)
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootRho rootDensity : ℝ) (hrootRho : 0 ≤ rootRho)
    (H : ReducedPairRealization Pcluster R G rootRho rootDensity)
    (D : PhysicalPartThreeAuxiliaryRootPlan Q sourceDensity E0 Mb P S A)
    (Kroot : RichRootSideCleaningScalarFacts Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A G rootRho rootDensity H
        (physicalRootGoodSidePlan.{v, w, u} Pcluster Gdegree threshold quota R
          miss Q sourceDensity E0 Mb))
    (initialRootImage : Fin P.numParts → Bv)
    (K : PartThreeFamilyFullFiberFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A hT havailable G rootRho rootDensity hrootRho H
      D Kroot) :
    OnlineRealizationData Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P G S A :=
  onlineRealizationDataOfPartThreeMixedFullFiberFacts Pcluster Gdegree
    threshold quota R miss Q sourceDensity E0 Mb P S A hT havailable hdisjoint
    G rootRho rootDensity hrootRho H D
      (isExceptionalPhysicalIndex (Pcluster := Pcluster)
        (Gdegree := Gdegree) (threshold := threshold) (quota := quota)
        (R := R) (miss := miss) Q sourceDensity E0 Mb)
    Kroot initialRootImage
      (K.toMixed Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb
        P S A hT havailable G rootRho rootDensity hrootRho H D Kroot)

end Erdos547b.ZhaoClaim615RichPartThreeMixedFamilyFacts

#print axioms Erdos547b.ZhaoClaim615RichPartThreeMixedFamilyFacts.PartThreeFamilyFullFiberFacts.toMixed
#print axioms Erdos547b.ZhaoClaim615RichPartThreeMixedFamilyFacts.onlineRealizationDataOfPartThreeFamilyFullFiberFacts
