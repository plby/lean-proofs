/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPhysicalFiberPlan
import ErdosProblems.Erdos547b.Lemma58FiberRootOrientation

/-!
# Physical rich root orientations without static fiber capacity

This is the source-only part of the old `PhysicalFiberPlan`.  It pastes the
orientations supplied by Zhao Lemma 5.4 and records the source-row adjacency
needed for branch roots.  Dynamic residual capacity is intentionally absent.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPhysicalRootOrientation

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
open Erdos547b.ZhaoClaim615RichPhysicalOrientationLoads
open Erdos547b.ZhaoClaim615RichPhysicalFiberPlan
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58FiberRootOrientation
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

/-- Root-only orientation data on every literal physical matching edge. -/
structure PhysicalRootOrientationPlan : Type (max u v w) where
  orient : ∀ e : PhysicalIndex Q sourceDensity E0 Mb,
    Fin (matchingFiber
      (assignedPhysicalIndex (Q := Q) (sourceDensity := sourceDensity)
        (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)) e).card →
      Fin 2 ≃ Fin 2
  root_adj : ∀ e i,
    (padGraph R).Adj (physicalRootVertex Q sourceDensity E0 Mb e)
      (matchingEdgeEndpoint (indexedPhysicalEdge Q sourceDensity E0 Mb e).1
        (orient e i 0))

/-- Package arbitrary per-fiber root orientations. -/
def physicalRootOrientationPlanOfCertificates
    (D : ∀ e : PhysicalIndex Q sourceDensity E0 Mb,
      FiberRootOrientation
        (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A) e)
        (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          e)) :
    PhysicalRootOrientationPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A where
  orient := fun e ↦ (D e).orient
  root_adj := by
    intro e i
    exact (D e).root_good i

/-- Eliminate the canonical `Fin` tag and assemble family-wise root
orientation certificates. -/
noncomputable def physicalRootOrientationCertificateOfFamilies
    (D0 : ∀ e : K0 Q sourceDensity E0,
      FiberRootOrientation
        (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)
          (exceptionalIndex Q sourceDensity E0 Mb e))
        (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (exceptionalIndex Q sourceDensity E0 Mb e)))
    (D1 : ∀ e : K1 Q sourceDensity E0 Mb,
      FiberRootOrientation
        (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)
          (remainingIndex Q sourceDensity E0 Mb e))
        (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (remainingIndex Q sourceDensity E0 Mb e)))
    (Db : ∀ e : Kb Q sourceDensity Mb,
      FiberRootOrientation
        (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)
          (reservedIndex Q sourceDensity E0 Mb e))
        (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (reservedIndex Q sourceDensity E0 Mb e)))
    (e : PhysicalIndex Q sourceDensity E0 Mb) :
    FiberRootOrientation
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) e)
      (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        e) := by
  let tagged := (Fintype.equivFin
    (PhysicalEdge Q sourceDensity E0 Mb)).symm e
  have htag : Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb) tagged = e :=
    (Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb)).apply_symm_apply e
  rcases tagged with e0 | e1
  · exact htag ▸ D0 e0
  · rcases e1 with e1 | eb
    · exact htag ▸ D1 e1
    · exact htag ▸ Db eb

/-- Family-wise constructor for the root-only physical plan. -/
noncomputable def physicalRootOrientationPlanOfFamilies
    (D0 : ∀ e : K0 Q sourceDensity E0,
      FiberRootOrientation
        (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)
          (exceptionalIndex Q sourceDensity E0 Mb e))
        (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (exceptionalIndex Q sourceDensity E0 Mb e)))
    (D1 : ∀ e : K1 Q sourceDensity E0 Mb,
      FiberRootOrientation
        (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)
          (remainingIndex Q sourceDensity E0 Mb e))
        (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (remainingIndex Q sourceDensity E0 Mb e)))
    (Db : ∀ e : Kb Q sourceDensity Mb,
      FiberRootOrientation
        (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)
          (reservedIndex Q sourceDensity E0 Mb e))
        (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (reservedIndex Q sourceDensity E0 Mb e))) :
    PhysicalRootOrientationPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A :=
  physicalRootOrientationPlanOfCertificates Pcluster Gdegree threshold quota R
    miss Q sourceDensity E0 Mb P S A
      (physicalRootOrientationCertificateOfFamilies Pcluster Gdegree threshold
        quota R miss Q sourceDensity E0 Mb P S A D0 D1 Db)

/-- Specialize classified Parts-1/2 source numerics to one physical fiber,
without asking for a static endpoint capacity. -/
noncomputable def physicalClassifiedRootOrientation
    (ratio dx dy gamma epsilon N : ℝ)
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
        e lowSide) :
    FiberRootOrientation
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) e)
      (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        e) :=
  classifiedThresholdRootOrientation
    (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) e)
    (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) e)
    ratio dx dy gamma epsilon N small lowSide highSide D hsides hhigh hlow

/-- Specialize Appendix A.2 source numerics to one physical fiber, again
retaining no static endpoint-capacity field. -/
noncomputable def physicalAppendixRootOrientation
    (gamma epsilon N : ℝ)
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
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        e c) :
    FiberRootOrientation
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) e)
      (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        e) :=
  appendixRootOrientation
    (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) e)
    (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) e)
    small rootReserve sideReserve X Y P0 Q0 gamma epsilon N D hroot

end Erdos547b.ZhaoClaim615RichPhysicalRootOrientation

#print axioms Erdos547b.ZhaoClaim615RichPhysicalRootOrientation.physicalRootOrientationPlanOfFamilies
#print axioms Erdos547b.ZhaoClaim615RichPhysicalRootOrientation.physicalClassifiedRootOrientation
#print axioms Erdos547b.ZhaoClaim615RichPhysicalRootOrientation.physicalAppendixRootOrientation
