/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPhysicalFiberApplication
import ErdosProblems.Erdos547b.Lemma58FiberOrientationCertificate

/-!
# Assemble local orientation certificates into the Claim-6.15 physical plan
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPhysicalFiberPlan

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
open Erdos547b.ZhaoClaim615HierarchicalCoordinateHostPools
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichPhysicalOrientationLoads
open Erdos547b.ZhaoClaim615RichPhysicalFiberApplication
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58FiberOrientationCertificate
open Erdos547b.ZhaoLemma54ThresholdSourceNumerics
open Erdos547b.ZhaoLemma54AppendixA

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

private abbrev assign :=
  assignedPhysicalIndex (Q := Q) (sourceDensity := sourceDensity)
    (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)

/-- The literal ordered branch forest assigned to one physical edge. -/
abbrev physicalFiberForest (e : PhysicalIndex Q sourceDensity E0 Mb) :=
  selectedForest (branchForest P).branches
    (matchingFiber (assign (Q := Q) (sourceDensity := sourceDensity)
      (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)) e)

/-- Root-side admissibility for one physical edge. -/
def physicalRootGood (e : PhysicalIndex Q sourceDensity E0 Mb)
    (c : Fin 2) : Prop :=
  (padGraph R).Adj (physicalRootVertex Q sourceDensity E0 Mb e)
    (matchingEdgeEndpoint (indexedPhysicalEdge Q sourceDensity E0 Mb e).1 c)

/-- The literal coordinate capacity right-hand side for one physical edge. -/
def physicalFiberRhs (rho density : ℝ)
    (e : PhysicalIndex Q sourceDensity E0 Mb) (c : Fin 2) : ℝ :=
  (density - rho) * #(slotRaw Pcluster Gdegree threshold quota R miss Q
    (Sum.inr ⟨indexedPhysicalEdge Q sourceDensity E0 Mb e, c⟩))

/-- Exact local certificate type for one physical edge. -/
abbrev PhysicalFiberCertificate (rho density removalBudget : ℝ)
    (e : PhysicalIndex Q sourceDensity E0 Mb) :=
  FiberOrientationCertificate
    (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) e)
    (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) e)
    small removalBudget
    (physicalFiberRhs Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb rho density e)

/-- Paste independently proved threshold/Appendix certificates into the one
global physical-fiber plan consumed by the coordinate hierarchy. -/
noncomputable def physicalFiberPlanOfCertificates
    (rho density removalBudget : ℝ)
    (D : ∀ e : PhysicalIndex Q sourceDensity E0 Mb,
      PhysicalFiberCertificate (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) rho density removalBudget e) :
    PhysicalFiberPlan Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb P S cap0 cap1 capb A rho density removalBudget where
  orient := fun e ↦ (D e).orient
  root_adj := by
    intro e i
    exact (D e).root_good i
  capacity := by
    intro e c
    exact (D e).capacity c

/-- Eliminate the canonical `Fin` reindexing and construct a local
certificate from the corresponding exceptional, remaining, or reserved
family certificate. -/
noncomputable def physicalFiberCertificateOfFamilies
    (rho density removalBudget : ℝ)
    (D0 : ∀ e : K0 Q sourceDensity E0,
      PhysicalFiberCertificate (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) rho density removalBudget
        (exceptionalIndex Q sourceDensity E0 Mb e))
    (D1 : ∀ e : K1 Q sourceDensity E0 Mb,
      PhysicalFiberCertificate (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) rho density removalBudget
        (remainingIndex Q sourceDensity E0 Mb e))
    (Db : ∀ e : Kb Q sourceDensity Mb,
      PhysicalFiberCertificate (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) rho density removalBudget
        (reservedIndex Q sourceDensity E0 Mb e))
    (e : PhysicalIndex Q sourceDensity E0 Mb) :
    PhysicalFiberCertificate (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) rho density removalBudget e := by
  let tagged := (Fintype.equivFin
    (PhysicalEdge Q sourceDensity E0 Mb)).symm e
  have htag : Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb) tagged = e :=
    (Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb)).apply_symm_apply e
  rcases tagged with e0 | e1
  · exact htag ▸ D0 e0
  · rcases e1 with e1 | eb
    · exact htag ▸ D1 e1
    · exact htag ▸ Db eb

/-- The family-wise form of `physicalFiberPlanOfCertificates`. -/
noncomputable def physicalFiberPlanOfFamilyCertificates
    (rho density removalBudget : ℝ)
    (D0 : ∀ e : K0 Q sourceDensity E0,
      PhysicalFiberCertificate (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) rho density removalBudget
        (exceptionalIndex Q sourceDensity E0 Mb e))
    (D1 : ∀ e : K1 Q sourceDensity E0 Mb,
      PhysicalFiberCertificate (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) rho density removalBudget
        (remainingIndex Q sourceDensity E0 Mb e))
    (Db : ∀ e : Kb Q sourceDensity Mb,
      PhysicalFiberCertificate (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) rho density removalBudget
        (reservedIndex Q sourceDensity E0 Mb e)) :
    PhysicalFiberPlan Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb P S cap0 cap1 capb A rho density removalBudget :=
  physicalFiberPlanOfCertificates Pcluster Gdegree threshold quota R miss Q
    sourceDensity E0 Mb P S A rho density removalBudget
    (physicalFiberCertificateOfFamilies Pcluster Gdegree threshold quota R miss
      Q sourceDensity E0 Mb P S A rho density removalBudget D0 D1 Db)

/-- Specialize the classified Parts-1/2 constructor to one literal physical
fiber. -/
noncomputable def physicalClassifiedThresholdCertificate
    (rho density removalBudget ratio dx dy gamma epsilon N : ℝ)
    (e : PhysicalIndex Q sourceDensity E0 Mb)
    (lowSide highSide : Fin 2)
    (D : ClassifiedThresholdOwnerNumerics
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) e)
      ratio dx dy gamma epsilon N small)
    (hsides : highSide ≠ lowSide)
    (hhigh : physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      e highSide)
    (hlow : thresholdLowBudget dx gamma N ≠ 0 →
      physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        e lowSide)
    (hmargin : ∀ c,
      (thresholdHighBudget dy gamma N : ℝ) + small + 1 + removalBudget + 1 ≤
        physicalFiberRhs Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb rho density e c) :
    PhysicalFiberCertificate (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) rho density removalBudget e :=
  classifiedThresholdCertificate
    (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) e)
    (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) e)
    ratio dx dy gamma epsilon N small removalBudget
    (physicalFiberRhs Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb rho density e) lowSide highSide D hsides hhigh hlow hmargin

/-- Specialize the checked Appendix-A constructor to one literal physical
fiber. -/
noncomputable def physicalAppendixCertificate
    (rho density removalBudget gamma epsilon N : ℝ)
    (e : PhysicalIndex Q sourceDensity E0 Mb)
    (rootReserve sideReserve X Y P0 Q0 : ℕ)
    (D : AppendixA2NumericData
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) e)
      small rootReserve sideReserve X Y P0 Q0 gamma epsilon N)
    (hroot : ∀ c,
      physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) e c)
    (hsideNonneg : 0 ≤ (gamma + 3 * epsilon) * N)
    (hmargin0 : (X : ℝ) + small + 1 + removalBudget + 1 ≤
      physicalFiberRhs Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb rho density e 0)
    (hmargin1 : (Y : ℝ) + small + 1 + removalBudget + 1 ≤
      physicalFiberRhs Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb rho density e 1) :
    PhysicalFiberCertificate (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) rho density removalBudget e :=
  appendixCertificateOfNumericData
    (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) e)
    (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) e)
    small rootReserve sideReserve X Y P0 Q0 gamma epsilon N removalBudget
    (physicalFiberRhs Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb rho density e) D hroot hsideNonneg hmargin0 hmargin1

end Erdos547b.ZhaoClaim615RichPhysicalFiberPlan

#print axioms Erdos547b.ZhaoClaim615RichPhysicalFiberPlan.physicalFiberPlanOfCertificates
#print axioms Erdos547b.ZhaoClaim615RichPhysicalFiberPlan.physicalFiberCertificateOfFamilies
#print axioms Erdos547b.ZhaoClaim615RichPhysicalFiberPlan.physicalFiberPlanOfFamilyCertificates
#print axioms Erdos547b.ZhaoClaim615RichPhysicalFiberPlan.physicalClassifiedThresholdCertificate
#print axioms Erdos547b.ZhaoClaim615RichPhysicalFiberPlan.physicalAppendixCertificate
