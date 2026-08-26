/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPhysicalPartTwo
import ErdosProblems.Erdos547b.Claim615RichPhysicalFiberApplication
import ErdosProblems.Erdos547b.Claim615CoordinateRootLoad
import ErdosProblems.Erdos547b.HierarchicalCoordinateRemovalBudgetBoundsGeneral

/-!
# Complete threshold-oriented physical application for Claim 6.15

The exceptional family is oriented by Zhao Lemma 5.4(2), while the
remaining and reserved families use Lemma 5.4(1).  This file packages the
source and scalar premises of those three constructors, builds the global
physical-fiber plan internally, and applies the full coordinate hierarchy.
No orientation certificate, embedding, copy, or continuation is an input.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPhysicalThresholdApplication

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
open Erdos547b.ZhaoClaim615RichPhysicalPartTwo
open Erdos547b.ZhaoClaim615CoordinateRootLoad
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.RegularPair
open Erdos547b.ZhaoHierarchicalCoordinateRemovalBudgetBoundsGeneral
open Erdos547b.ZhaoLemma54ThresholdSourceNumerics
open Erdos547b.ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalTargetUnifiedApplication.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools
open Erdos547b.ZhaoLemma59HierarchicalCoordinatePools.HierarchicalSegmentForest

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
  (E0 : SelectedExceptionalEdges Q sourceDensity L eta .unbalanced count)
variable
  (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)

variable (P : ZhaoForestPartition T globalRoot small)
variable {target slack : ℕ} {ratio : ℝ}
variable
  (S : SelectedF0 P (balancedMajorBranches P ratio) target slack)

/-- The source and scalar hypotheses needed to orient all three physical
families.  Every field is a statement about the source density row or a
literal host-capacity inequality; the chosen orientations are outputs. -/
structure PhysicalThresholdFacts
    (rho pairDensity removalBudget gamma epsilon : ℝ) :
    Type (max u v w) where
  ratio_nonneg : 0 ≤ ratio
  ratio_le_half : ratio ≤ 1 / 2
  N_pos : 0 < N
  gamma_nonneg : 0 ≤ gamma
  epsilon_nonneg : 0 ≤ epsilon
  rounding : (2 : ℝ) + 3 * small ≤ 3 * (epsilon * N)
  eta_pos : 0 < eta
  row_A_nonneg : ∀ x, 0 ≤ sourceDensity (Sum.inl Q.A) x
  adj_A : ∀ x, 0 < sourceDensity (Sum.inl Q.A) x →
    (padGraph R).Adj (Sum.inl Q.A) x
  adj_B : ∀ x, 0 < sourceDensity (Sum.inl Q.B) x →
    (padGraph R).Adj (Sum.inl Q.B) x
  exceptional_target_nonneg : ∀ e,
    0 ≤ exceptionalPartTwoTarget Q sourceDensity E0
      ratio gamma epsilon N e
  exceptional_high_nonneg : ∀ e,
    0 ≤ (exceptionalHighDensity Q sourceDensity E0 e - gamma) * N
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
  exceptional_margin : ∀ e c,
    (thresholdHighBudget
        (exceptionalHighDensity Q sourceDensity E0 e) gamma N : ℝ) +
        small + 1 + removalBudget + 1 ≤
      physicalFiberRhs Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb rho pairDensity
        (exceptionalIndex Q sourceDensity E0 Mb e) c
  remaining_margin : ∀ e c,
    (thresholdHighBudget
        (remainingHighDensity Q sourceDensity E0 Mb e) gamma N : ℝ) +
        small + 1 + removalBudget + 1 ≤
      physicalFiberRhs Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb rho pairDensity
        (remainingIndex Q sourceDensity E0 Mb e) c
  reserved_margin : ∀ e c,
    (thresholdHighBudget
        (reservedHighDensity Q sourceDensity Mb e) gamma N : ℝ) +
        small + 1 + removalBudget + 1 ≤
      physicalFiberRhs Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb rho pairDensity
        (reservedIndex Q sourceDensity E0 Mb e) c

/-- Global cleaning and distinguished-reservoir inequalities.  Unlike the
three fiber margins, these facts are independent of the source allocation
and of the orientations chosen by the threshold constructors. -/
structure PhysicalThresholdGlobalFacts
    (hT : T.IsTree) (rho pairDensity removalBudget : ℝ) (m : ℕ) : Prop where
  rho_nonneg : 0 ≤ rho
  whole_card : ∀ slot : RootSlot (MatchingEdge Q.claim67.M),
    #(slotWhole Pcluster Gdegree threshold quota R miss Q slot) = m
  removal :
    ((Fintype.card (SegmentIndex hT P (canonicalOptional P)) + small : ℕ) : ℝ) *
        (rho * m) ≤ removalBudget
  A_reserve : rho * #(clusterVertices Pcluster Q.A) ≤ quota
  B_reserve : rho * #(clusterVertices Pcluster Q.B) ≤ quota
  matching_reserve : ∀ e : MatchingEdge Q.claim67.M, ∀ side : Fin 2,
    rho * #(slotWhole Pcluster Gdegree threshold quota R miss Q
        (Sum.inr ⟨e, side⟩)) + (2 * quota : ℕ) ≤
      #(slotWhole Pcluster Gdegree threshold quota R miss Q
        (Sum.inr ⟨e, side⟩))
  distinguished_margin : ∀ side,
    (Fintype.card (SegmentIndex hT P (canonicalOptional P)) + small + 1 : ℝ) +
        removalBudget + 1 ≤
      (pairDensity - rho) *
        #(slotRaw Pcluster Gdegree threshold quota R miss Q (Sum.inl side))
  direct_root_budget :
    (#(Finset.univ.filter fun i ↦
        (AllocationHierarchy hT P (canonicalOptional P)).parent i =
          Sum.inl 0) : ℝ) *
      (rho * #(slotWhole Pcluster Gdegree threshold quota R miss Q
        (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)))) <
      #(slotRaw Pcluster Gdegree threshold quota R miss Q
        (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)))

/-- Exact aggregate source inequalities that pack the three branch families
into the concrete exceptional, remaining, and reserved physical edges. -/
structure PhysicalThresholdPackingFacts
    (gamma epsilon : ℝ) : Prop where
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
  exceptional_budget :
    ((branchMass P S.selected +
        Fintype.card (K0 Q sourceDensity E0) * small +
        Fintype.card (K0 Q sourceDensity E0) : ℕ) : ℝ) ≤
      sourceDegree Q.claim67.M L sourceDensity N (Sum.inl Q.A) E0.selected +
        (Fintype.card (K0 Q sourceDensity E0) : ℝ) *
          ((ratio / (1 - ratio) * eta - 2 * gamma - 3 * epsilon) * N)
  remaining_budget :
    ((branchMass P (majorResidualBranches P S) +
        Fintype.card (K1 Q sourceDensity E0 Mb) * small +
        Fintype.card (K1 Q sourceDensity E0 Mb) : ℕ) : ℝ) +
      (Fintype.card (K1 Q sourceDensity E0 Mb) : ℝ) *
        ((2 * gamma + 3 * epsilon) * N) ≤
      sourceDegree Q.claim67.M L sourceDensity N (Sum.inl Q.A)
        (positiveRemainingEdgesA Q sourceDensity L N
          (E0.selected ∪ Mb.selected))
  reserved_budget :
    ((branchMass P (minorBranches P) +
        Fintype.card (Kb Q sourceDensity Mb) * small +
        Fintype.card (Kb Q sourceDensity Mb) : ℕ) : ℝ) +
      (Fintype.card (Kb Q sourceDensity Mb) : ℝ) *
        ((2 * gamma + 3 * epsilon) * N) ≤
      sourceDegree Q.claim67.M L sourceDensity N (Sum.inl Q.B) Mb.selected

/-- Construct the literal global physical-fiber plan from the three checked
threshold constructors. -/
noncomputable def physicalPartTwoPartOnePlan
    (rho pairDensity removalBudget gamma epsilon : ℝ)
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon))
    (havailable : balancedMajorBranches P ratio ⊆ halfBranches P)
    (F : PhysicalThresholdFacts (small := small) (ratio := ratio)
      Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb rho pairDensity removalBudget gamma epsilon) :
    PhysicalFiberPlan Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb P S
      (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon) A
      rho pairDensity removalBudget :=
  physicalFiberPlanOfFamilyCertificates Pcluster Gdegree threshold quota R miss
    Q sourceDensity E0 Mb P S A rho pairDensity removalBudget
    (fun e ↦ exceptionalPartTwoCertificate
      (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
      (quota := quota) (R := R) (miss := miss) (Q := Q)
      (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (ratio := ratio) (S := S) rho pairDensity removalBudget gamma
      epsilon N A e F.ratio_nonneg F.ratio_le_half F.N_pos F.gamma_nonneg
      F.epsilon_nonneg (F.exceptional_target_nonneg e)
      (F.exceptional_high_nonneg e) F.rounding F.eta_pos F.row_A_nonneg F.adj_A
      (F.exceptional_margin e))
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
      havailable e F.N_pos F.gamma_nonneg F.epsilon_nonneg
      (F.reserved_target_nonneg e) (F.reserved_high_nonneg e) F.rounding
      F.adj_B (F.reserved_margin e))

/-- Full coordinate-hierarchy containment from the concrete Part-2/Part-1
source allocation and its scalar facts.  The physical-fiber plan and every
local orientation certificate are constructed internally. -/
theorem isContained_of_physicalThresholdSourceAllocation
    (hT : T.IsTree) (hsmall : 1 ≤ small)
    (rho pairDensity removalBudget gamma epsilon : ℝ)
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon))
    (havailable : balancedMajorBranches P ratio ⊆ halfBranches P)
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (Hpair : ReducedPairRealization Pcluster R G rho pairDensity)
    (F : PhysicalThresholdFacts (small := small) (ratio := ratio)
      Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb rho pairDensity removalBudget gamma epsilon)
    (hA : rho * #(clusterVertices Pcluster Q.A) ≤ quota)
    (hB : rho * #(clusterVertices Pcluster Q.B) ≤ quota)
    (hmatching : ∀ e : MatchingEdge Q.claim67.M, ∀ side : Fin 2,
      rho * #(slotWhole Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨e, side⟩)) + (2 * quota : ℕ) ≤
        #(slotWhole Pcluster Gdegree threshold quota R miss Q
          (Sum.inr ⟨e, side⟩)))
    (hremoval : ∀ i a,
      coordinateRemovalBudget
        (AllocationHierarchy hT P (canonicalOptional P)) rho
        (coordinateHierarchyRootSlot hT P (canonicalOptional P) ∅
          (sourceVertexReservoirSide P) S
          (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
          (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
          (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon) A
          (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
          (edgeb Q sourceDensity Mb)
            (physicalFiberOrient Q sourceDensity E0 Mb P S A
              (physicalPartTwoPartOnePlan Pcluster Gdegree threshold quota R miss
              Q sourceDensity E0 Mb P S rho pairDensity removalBudget gamma
              epsilon A havailable F).orient))
        (slotWhole Pcluster Gdegree threshold quota R miss Q)
        (fun i a ↦ slotWhole Pcluster Gdegree threshold quota R miss Q
          (coordinateHierarchyInteriorSlot hT P (canonicalOptional P) S
            (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
            (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
            (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon) A
            (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
            (edgeb Q sourceDensity Mb)
              (physicalFiberOrient Q sourceDensity E0 Mb P S A
                (physicalPartTwoPartOnePlan Pcluster Gdegree threshold quota R
                miss Q sourceDensity E0 Mb P S rho pairDensity removalBudget
                gamma epsilon A havailable F).orient) i a)) i a ≤ removalBudget)
    (hreserveCapacity : ∀ side,
      (coordinatePoolLoad (AllocationHierarchy hT P (canonicalOptional P))
            (coordinateHierarchyRootSlot hT P (canonicalOptional P) ∅
              (sourceVertexReservoirSide P) S
              (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
              (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
              (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon) A
              (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
              (edgeb Q sourceDensity Mb)
              (physicalFiberOrient Q sourceDensity E0 Mb P S A
                (physicalPartTwoPartOnePlan Pcluster Gdegree threshold quota R
                  miss Q sourceDensity E0 Mb P S rho pairDensity
                  removalBudget gamma epsilon A havailable F).orient))
            (coordinateHierarchyInteriorSlot hT P (canonicalOptional P) S
              (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
              (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
              (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon) A
              (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
              (edgeb Q sourceDensity Mb)
              (physicalFiberOrient Q sourceDensity E0 Mb P S A
                (physicalPartTwoPartOnePlan Pcluster Gdegree threshold quota R
                  miss Q sourceDensity E0 Mb P S rho pairDensity
                  removalBudget gamma epsilon A havailable F).orient))
            (Sum.inl side : RootSlot (MatchingEdge Q.claim67.M)) +
          small + 1 : ℝ) + removalBudget + 1 ≤
        (pairDensity - rho) *
          #(slotRaw Pcluster Gdegree threshold quota R miss Q (Sum.inl side)))
    (hbadBudget :
      (#(Finset.univ.filter fun i ↦
          (AllocationHierarchy hT P (canonicalOptional P)).parent i =
            Sum.inl 0) : ℝ) *
        (rho * #(slotWhole Pcluster Gdegree threshold quota R miss Q
          (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)))) <
        #(slotRaw Pcluster Gdegree threshold quota R miss Q
          (Sum.inl (componentReservoirSide P ⟨0, P.numParts_pos⟩)))) :
    T.IsContained G := by
  let plan := physicalPartTwoPartOnePlan Pcluster Gdegree threshold quota R miss
    Q sourceDensity E0 Mb P S rho pairDensity removalBudget gamma epsilon A
      havailable F
  exact isContained_of_physicalFiberSideLoads Pcluster Gdegree threshold quota
    R miss Q sourceDensity E0 Mb hT P hsmall S A havailable hdisjoint G rho
    pairDensity removalBudget plan Hpair hA hB hmatching hremoval
    hreserveCapacity hbadBudget

/-- Scalar form of the complete physical threshold application.  The
coordinate cleaning bound and the distinguished-pool load are now derived
from a common slot size and the number of hierarchy segments. -/
theorem isContained_of_physicalThresholdScalarFacts
    (hT : T.IsTree) (hsmall : 1 ≤ small)
    (rho pairDensity removalBudget gamma epsilon : ℝ)
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon))
    (havailable : balancedMajorBranches P ratio ⊆ halfBranches P)
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (Hpair : ReducedPairRealization Pcluster R G rho pairDensity)
    (F : PhysicalThresholdFacts (small := small) (ratio := ratio)
      Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb rho pairDensity removalBudget gamma epsilon)
    (m : ℕ)
    (H : PhysicalThresholdGlobalFacts Pcluster Gdegree threshold quota R miss Q
      P hT rho pairDensity removalBudget m) :
    T.IsContained G := by
  classical
  let plan := physicalPartTwoPartOnePlan Pcluster Gdegree threshold quota R miss
    Q sourceDensity E0 Mb P S rho pairDensity removalBudget gamma epsilon A
      havailable F
  let orient := physicalFiberOrient Q sourceDensity E0 Mb P S A plan.orient
  let rootSlot := coordinateHierarchyRootSlot hT P (canonicalOptional P) ∅
    (sourceVertexReservoirSide P) S
    (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
    (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
    (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon) A
    (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
    (edgeb Q sourceDensity Mb) orient
  let interiorSlot := coordinateHierarchyInteriorSlot hT P
    (canonicalOptional P) S
    (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
    (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
    (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon) A
    (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
    (edgeb Q sourceDensity Mb) orient
  let whole := slotWhole Pcluster Gdegree threshold quota R miss Q
  let interiorWhole : (i : SegmentIndex hT P (canonicalOptional P)) →
      Fin ((AllocationHierarchy hT P (canonicalOptional P)).segments.size i) →
        Finset Bv := fun i a ↦ whole (interiorSlot i a)
  have hsegmentSmall : ∀ i,
      (AllocationHierarchy hT P (canonicalOptional P)).segments.size i ≤ small :=
    by
      intro i
      cases hclass : segmentSourceClass hT P (canonicalOptional P) i with
      | inl q =>
          have hiRoot : i ∈ rootSegments hT P (canonicalOptional P) :=
            (mem_rootSegments_iff hT P (canonicalOptional P) i).2 ⟨q, hclass⟩
          rw [rootSegment_size_eq_one hT P (canonicalOptional P) i hiRoot]
          exact hsmall
      | inr j =>
          exact (segment_size_le_sourceBranch hT P (canonicalOptional P) i j
            hclass).trans (canonical_branch_size_le_small P j)
  have hcandidate : ∀ i a,
      #(rawCandidate (AllocationHierarchy hT P (canonicalOptional P)) rootSlot
        whole interiorWhole i a) ≤ m := by
    intro i a
    simp only [rawCandidate]
    split
    · exact (H.whole_card _).le
    · exact (H.whole_card _).le
  have hremoval : ∀ i a,
      coordinateRemovalBudget (AllocationHierarchy hT P (canonicalOptional P))
        rho rootSlot whole interiorWhole i a ≤ removalBudget :=
    coordinateRemovalBudget_le
      (AllocationHierarchy hT P (canonicalOptional P)) rho removalBudget
      rootSlot whole interiorWhole small m H.rho_nonneg hsegmentSmall hcandidate
      (by simpa only [SegmentIndex, Fintype.card_fin] using H.removal)
  have hreserveLoad : ∀ side,
      coordinatePoolLoad (AllocationHierarchy hT P (canonicalOptional P))
          rootSlot interiorSlot (Sum.inl side : RootSlot (MatchingEdge Q.claim67.M)) ≤
        Fintype.card (SegmentIndex hT P (canonicalOptional P)) := by
    intro side
    exact coordinatePoolLoad_reserve_le_card_segments hT P
      (canonicalOptional P) ∅ (sourceVertexReservoirSide P) S
      (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon) A
      (edge0 Q sourceDensity E0) (edge1 Q sourceDensity E0 Mb)
      (edgeb Q sourceDensity Mb) orient side
  have hreserveCapacity : ∀ side,
      (coordinatePoolLoad (AllocationHierarchy hT P (canonicalOptional P))
            rootSlot interiorSlot (Sum.inl side : RootSlot (MatchingEdge Q.claim67.M)) +
          small + 1 : ℝ) + removalBudget + 1 ≤
        (pairDensity - rho) *
          #(slotRaw Pcluster Gdegree threshold quota R miss Q (Sum.inl side)) := by
    intro side
    have hloadR :
        (coordinatePoolLoad (AllocationHierarchy hT P (canonicalOptional P))
          rootSlot interiorSlot (Sum.inl side : RootSlot (MatchingEdge Q.claim67.M)) : ℝ) ≤
          Fintype.card (SegmentIndex hT P (canonicalOptional P)) := by
      exact_mod_cast hreserveLoad side
    linarith [H.distinguished_margin side]
  apply isContained_of_physicalThresholdSourceAllocation Pcluster Gdegree
    threshold quota R miss Q sourceDensity E0 Mb P S hT hsmall rho pairDensity
    removalBudget gamma epsilon A havailable hdisjoint G Hpair F H.A_reserve
    H.B_reserve H.matching_reserve
  · simpa only [rootSlot, interiorSlot, whole, interiorWhole, orient, plan] using
      hremoval
  · simpa only [rootSlot, interiorSlot, orient, plan] using hreserveCapacity
  · exact H.direct_root_budget

/-- Final source-degree form of the physical threshold application.  The
three finite packings, every local orientation certificate, and the global
coordinate hierarchy are all constructed internally. -/
theorem isContained_of_physicalThresholdPackingFacts
    (hT : T.IsTree) (hsmall : 1 ≤ small)
    (rho pairDensity removalBudget gamma epsilon : ℝ)
    (havailable : balancedMajorBranches P ratio ⊆ halfBranches P)
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (Hpair : ReducedPairRealization Pcluster R G rho pairDensity)
    (F : PhysicalThresholdFacts (small := small) (ratio := ratio)
      Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb rho
      pairDensity removalBudget gamma epsilon)
    (packing : PhysicalThresholdPackingFacts
      (P := P) (S := S) (Q := Q) (sourceDensity := sourceDensity)
      (E0 := E0) (Mb := Mb) (gamma := gamma) (epsilon := epsilon))
    (m : ℕ)
    (H : PhysicalThresholdGlobalFacts Pcluster Gdegree threshold quota R miss Q
      P hT rho pairDensity removalBudget m) :
    T.IsContained G := by
  have hratio_lt_one : ratio < 1 := by linarith [F.ratio_le_half]
  obtain ⟨A⟩ := exists_sourceAllocation_partTwo_partOne_of_sourceDegrees
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (ratio := ratio) (S := S) gamma epsilon packing.count_pos
    packing.targetB_pos packing.A_edge_nonneg packing.remaining_A_pos
    F.ratio_nonneg hratio_lt_one F.N_pos.le packing.exceptional_budget
    packing.remaining_budget packing.reserved_budget
  exact isContained_of_physicalThresholdScalarFacts Pcluster Gdegree threshold
    quota R miss Q sourceDensity E0 Mb P S hT hsmall rho pairDensity
    removalBudget gamma epsilon A havailable hdisjoint G Hpair F m H

end Erdos547b.ZhaoClaim615RichPhysicalThresholdApplication

#print axioms Erdos547b.ZhaoClaim615RichPhysicalThresholdApplication.physicalPartTwoPartOnePlan
#print axioms Erdos547b.ZhaoClaim615RichPhysicalThresholdApplication.isContained_of_physicalThresholdSourceAllocation
#print axioms Erdos547b.ZhaoClaim615RichPhysicalThresholdApplication.isContained_of_physicalThresholdScalarFacts
#print axioms Erdos547b.ZhaoClaim615RichPhysicalThresholdApplication.isContained_of_physicalThresholdPackingFacts
