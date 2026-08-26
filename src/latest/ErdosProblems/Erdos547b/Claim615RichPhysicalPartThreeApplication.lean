/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPhysicalPartThree
import ErdosProblems.Erdos547b.Claim615RichPhysicalFiberScalarApplication

/-!
# Complete physical Part-3 application for Claim 6.15

The nonextreme exceptional family is oriented by Appendix A.2; the remaining
and reserved families retain their canonical Part-1 orientations.  This file
assembles those certificates and invokes the full coordinate hierarchy.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPhysicalPartThreeApplication

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim616CoordinateCanonicalOptional
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615HierarchicalCoordinateSourceLayout
open Erdos547b.ZhaoClaim615HierarchicalCoordinateHostPools
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichPhysicalOrientationLoads
open Erdos547b.ZhaoClaim615RichPhysicalFiberApplication
open Erdos547b.ZhaoClaim615RichPhysicalFiberPlan
open Erdos547b.ZhaoClaim615RichPhysicalPartOne
open Erdos547b.ZhaoClaim615RichPhysicalPartThree
open Erdos547b.ZhaoClaim615RichPhysicalFiberScalarApplication
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.RegularPair
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
variable {count cardBound : ℕ}
variable
  (E0 : SelectedExceptionalEdges Q sourceDensity L eta .nonextreme count)
variable
  (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)

variable (P : ZhaoForestPartition T globalRoot small)
variable {target slack : ℕ}
variable
  (S : SelectedF0 P (nontrivialMajorBranches P) target slack)

/-- Source-row and scalar facts for the two ordinary physical families. -/
structure OrdinaryPartOneFacts
    (rho pairDensity removalBudget gamma epsilon : ℝ) : Type (max u v w) where
  N_pos : 0 < N
  gamma_nonneg : 0 ≤ gamma
  epsilon_nonneg : 0 ≤ epsilon
  rounding : (2 : ℝ) + 3 * small ≤ 3 * (epsilon * N)
  eta_pos : 0 < eta
  adj_A : ∀ x, 0 < sourceDensity (Sum.inl Q.A) x →
    (padGraph R).Adj (Sum.inl Q.A) x
  adj_B : ∀ x, 0 < sourceDensity (Sum.inl Q.B) x →
    (padGraph R).Adj (Sum.inl Q.B) x
  remaining_target_nonneg : ∀ e,
    0 ≤ (remainingLowDensity Q sourceDensity E0 Mb e +
      remainingHighDensity Q sourceDensity E0 Mb e - 2 * gamma -
      3 * epsilon) * N
  remaining_high_nonneg : ∀ e,
    0 ≤ (remainingHighDensity Q sourceDensity E0 Mb e - gamma) * N
  reserved_target_nonneg : ∀ e,
    0 ≤ (reservedLowDensity Q sourceDensity Mb e +
      reservedHighDensity Q sourceDensity Mb e - 2 * gamma -
      3 * epsilon) * N
  reserved_high_nonneg : ∀ e,
    0 ≤ (reservedHighDensity Q sourceDensity Mb e - gamma) * N
  remaining_margin : ∀ e c,
    (thresholdHighBudget
        (remainingHighDensity Q sourceDensity E0 Mb e) gamma N : ℝ) +
        small + 1 + removalBudget + 1 ≤
      physicalFiberRhs Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb rho pairDensity (remainingIndex Q sourceDensity E0 Mb e) c
  reserved_margin : ∀ e c,
    (thresholdHighBudget
        (reservedHighDensity Q sourceDensity Mb e) gamma N : ℝ) +
        small + 1 + removalBudget + 1 ≤
      physicalFiberRhs Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb rho pairDensity (reservedIndex Q sourceDensity E0 Mb e) c

/-- Aggregate packing inequalities for an arbitrary Appendix-A exceptional
capacity and the two canonical Part-1 ordinary capacities. -/
structure PartThreePackingFacts
    (cap0 : K0 Q sourceDensity E0 → ℕ) (gamma epsilon : ℝ) : Prop where
  count_pos : 0 < count
  targetB_pos : 0 < targetB
  A_edge_nonneg : ∀ e ∈ allMatchingEdges Q.claim67.M,
    0 ≤ N * (sourceDensity (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M L e 0) +
      sourceDensity (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M L e 1))
  remaining_A_pos : 0 < sourceDegree Q.claim67.M L sourceDensity N
    (Sum.inl Q.A) (allMatchingEdges Q.claim67.M \
      (E0.selected ∪ Mb.selected))
  exceptional_budget : branchMass P S.selected +
    Fintype.card (K0 Q sourceDensity E0) * small ≤ ∑ e, cap0 e
  remaining_budget :
    ((branchMass P (majorResidualBranches P S) +
        Fintype.card (K1 Q sourceDensity E0 Mb) * small +
        Fintype.card (K1 Q sourceDensity E0 Mb) : ℕ) : ℝ) ≤
      ∑ e : K1 Q sourceDensity E0 Mb,
        (remainingLowDensity Q sourceDensity E0 Mb e +
          remainingHighDensity Q sourceDensity E0 Mb e - 2 * gamma -
          3 * epsilon) * N
  reserved_budget :
    ((branchMass P (minorBranches P) +
        Fintype.card (Kb Q sourceDensity Mb) * small +
        Fintype.card (Kb Q sourceDensity Mb) : ℕ) : ℝ) ≤
      ∑ e : Kb Q sourceDensity Mb,
        (reservedLowDensity Q sourceDensity Mb e +
          reservedHighDensity Q sourceDensity Mb e - 2 * gamma -
          3 * epsilon) * N

/-- Assemble Appendix-A.2 certificates on the exceptional family and Part-1
certificates on the other two families. -/
noncomputable def physicalPartThreePartOnePlan
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    (rho pairDensity removalBudget gamma epsilon : ℝ)
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon))
    (F : OrdinaryPartOneFacts (small := small) Pcluster Gdegree threshold quota
      R miss Q sourceDensity E0 Mb rho pairDensity removalBudget gamma epsilon)
    (F0 : ∀ e : K0 Q sourceDensity E0,
      ExceptionalPartThreeFacts Q sourceDensity E0 Mb P S A rho pairDensity
        removalBudget gamma epsilon e) :
    PhysicalFiberPlan Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb P S cap0
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon) A
      rho pairDensity removalBudget :=
  physicalFiberPlanOfFamilyCertificates Pcluster Gdegree threshold quota R miss
    Q sourceDensity E0 Mb P S A rho pairDensity removalBudget
    (fun e ↦ exceptionalPartThreeCertificate
      (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
      (quota := quota) (R := R) (miss := miss) (Q := Q)
      (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) A rho pairDensity removalBudget gamma epsilon
      F.eta_pos F.adj_A e (F0 e))
    (fun e ↦ remainingPartOneCertificate
      (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
      (quota := quota) (R := R) (miss := miss) (Q := Q)
      (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) rho pairDensity removalBudget gamma epsilon A e
      F.N_pos F.gamma_nonneg F.epsilon_nonneg
      (F.remaining_target_nonneg e) (F.remaining_high_nonneg e) F.rounding
      F.adj_A (F.remaining_margin e))
    (fun e ↦ reservedPartOneCertificate
      (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
      (quota := quota) (R := R) (miss := miss) (Q := Q)
      (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) rho pairDensity removalBudget gamma epsilon A
      (fun j hj ↦ (mem_nontrivialMajorBranches P j).mp hj |>.1) e
      F.N_pos F.gamma_nonneg F.epsilon_nonneg
      (F.reserved_target_nonneg e) (F.reserved_high_nonneg e) F.rounding
      F.adj_B (F.reserved_margin e))

/-- Full containment for the nonextreme exceptional case from Appendix-A.2
numeric facts and common hierarchy-cleaning scalars. -/
theorem isContained_of_physicalPartThreeFacts
    (hT : T.IsTree) (hsmall : 1 ≤ small)
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    (rho pairDensity removalBudget gamma epsilon : ℝ)
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon))
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (Hpair : ReducedPairRealization Pcluster R G rho pairDensity)
    (F : OrdinaryPartOneFacts (small := small) Pcluster Gdegree threshold quota
      R miss Q sourceDensity E0 Mb rho pairDensity removalBudget gamma epsilon)
    (F0 : ∀ e : K0 Q sourceDensity E0,
      ExceptionalPartThreeFacts Q sourceDensity E0 Mb P S A rho pairDensity
        removalBudget gamma epsilon e)
    (m : ℕ)
    (H : PhysicalFiberGlobalFacts Pcluster Gdegree threshold quota R miss Q P
      hT rho pairDensity removalBudget m) :
    T.IsContained G := by
  let plan := physicalPartThreePartOnePlan Pcluster Gdegree threshold quota R
    miss Q sourceDensity E0 Mb P S rho pairDensity removalBudget gamma epsilon
    A F F0
  exact isContained_of_physicalFiberPlanScalarFacts Pcluster Gdegree threshold
    quota R miss Q sourceDensity E0 Mb hT P hsmall S A
    (fun j hj ↦ (mem_nontrivialMajorBranches P j).mp hj |>.1) hdisjoint G rho
    pairDensity removalBudget plan Hpair m H

/-- Packing form of the nonextreme application.  The source allocation is
chosen internally; the Appendix numeric record may depend on the resulting
literal physical fibers, but remains purely source/scalar data. -/
theorem isContained_of_physicalPartThreePackingFacts
    (hT : T.IsTree) (hsmall : 1 ≤ small)
    (cap0 : K0 Q sourceDensity E0 → ℕ)
    (rho pairDensity removalBudget gamma epsilon : ℝ)
    (packing : PartThreePackingFacts (P := P) (S := S)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (cap0 := cap0) (gamma := gamma) (epsilon := epsilon))
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (Hpair : ReducedPairRealization Pcluster R G rho pairDensity)
    (F : OrdinaryPartOneFacts (small := small) Pcluster Gdegree threshold quota
      R miss Q sourceDensity E0 Mb rho pairDensity removalBudget gamma epsilon)
    (F0 : ∀ (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0
        (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
        (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon)),
      ∀ e : K0 Q sourceDensity E0,
        ExceptionalPartThreeFacts Q sourceDensity E0 Mb P S A rho pairDensity
          removalBudget gamma epsilon e)
    (m : ℕ)
    (H : PhysicalFiberGlobalFacts Pcluster Gdegree threshold quota R miss Q P
      hT rho pairDensity removalBudget m) :
    T.IsContained G := by
  obtain ⟨A⟩ := exists_sourceAllocation_partOne_physical
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) gamma epsilon cap0 packing.count_pos
    packing.targetB_pos packing.A_edge_nonneg packing.remaining_A_pos
    packing.exceptional_budget packing.remaining_budget packing.reserved_budget
  exact isContained_of_physicalPartThreeFacts Pcluster Gdegree threshold quota R
    miss Q sourceDensity E0 Mb P S hT hsmall rho pairDensity removalBudget
    gamma epsilon A hdisjoint G Hpair F (F0 A) m H

end Erdos547b.ZhaoClaim615RichPhysicalPartThreeApplication

#print axioms Erdos547b.ZhaoClaim615RichPhysicalPartThreeApplication.physicalPartThreePartOnePlan
#print axioms Erdos547b.ZhaoClaim615RichPhysicalPartThreeApplication.isContained_of_physicalPartThreeFacts
#print axioms Erdos547b.ZhaoClaim615RichPhysicalPartThreeApplication.isContained_of_physicalPartThreePackingFacts
