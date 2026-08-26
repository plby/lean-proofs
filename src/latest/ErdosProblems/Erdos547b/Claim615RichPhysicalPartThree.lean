/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPhysicalPartOne

/-!
# Source-faithful Part-3 certificates on physical Claim-6.15 edges

For a selected nonextreme edge, both raw endpoints are adjacent to the rich
`A` cluster.  The checked Appendix-A.2 numeric record therefore chooses the
orientation and supplies the two endpoint load bounds without an embedding,
copy, or orientation premise.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPhysicalPartThree

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
open Erdos547b.ZhaoClaim615RichPhysicalPartOne
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoLemma54AppendixA

universe u v w

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

variable {Bv : Type v} {I : Type w}
variable [Fintype Bv] [DecidableEq Bv] [Fintype I] [DecidableEq I]
variable {Pcluster : ClusterAssignment Bv I}
variable {Gdegree : SimpleGraph Bv} [DecidableRel Gdegree.Adj]
variable {threshold quota : ℕ} {R : SimpleGraph I} [DecidableRel R.Adj]
variable {miss : ℕ}
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
variable {available : Finset
  (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
variable {target slack : ℕ}
variable (S : SelectedF0 P available target slack)

/-- The literal Appendix-A.2 numeric data on one exceptional physical
fiber, together with the two host-coordinate margins it must satisfy. -/
structure ExceptionalPartThreeFacts
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      cap0 cap1 capb)
    (rho pairDensity removalBudget gamma epsilon : ℝ)
    (e : K0 Q sourceDensity E0) : Type (max u v w) where
  rootReserve : ℕ
  sideReserve : ℕ
  X : ℕ
  Y : ℕ
  P0 : ℕ
  Q0 : ℕ
  numeric : AppendixA2NumericData
    (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A)
      (exceptionalIndex Q sourceDensity E0 Mb e))
    small rootReserve sideReserve X Y P0 Q0 gamma epsilon N
  side_nonneg : 0 ≤ (gamma + 3 * epsilon) * N
  margin_zero : (X : ℝ) + small + 1 + removalBudget + 1 ≤
    physicalFiberRhs Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb rho pairDensity (exceptionalIndex Q sourceDensity E0 Mb e) 0
  margin_one : (Y : ℝ) + small + 1 + removalBudget + 1 ≤
    physicalFiberRhs Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb rho pairDensity (exceptionalIndex Q sourceDensity E0 Mb e) 1

/-- A selected nonextreme edge and its Appendix-A.2 source numerics produce
the actual local physical-fiber certificate. -/
noncomputable def exceptionalPartThreeCertificate
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      cap0 cap1 capb)
    (rho pairDensity removalBudget gamma epsilon : ℝ)
    (heta : 0 < eta)
    (hAdj : ∀ x, 0 < sourceDensity (Sum.inl Q.A) x →
      (padGraph R).Adj (Sum.inl Q.A) x)
    (e : K0 Q sourceDensity E0)
    (F : ExceptionalPartThreeFacts Q sourceDensity E0 Mb P S A rho
      pairDensity removalBudget gamma epsilon e) :
    PhysicalFiberCertificate (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) rho pairDensity removalBudget
      (exceptionalIndex Q sourceDensity E0 Mb e) := by
  apply physicalAppendixCertificate
    (Pcluster := Pcluster) (Gdegree := Gdegree) (threshold := threshold)
    (quota := quota) (R := R) (miss := miss) (Q := Q)
    (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A) rho pairDensity removalBudget gamma epsilon N
    (exceptionalIndex Q sourceDensity E0 Mb e) F.rootReserve F.sideReserve F.X
    F.Y F.P0 F.Q0 F.numeric
  · intro c
    have hadj := nonextremeRawSide_adj_A Q sourceDensity L eta heta hAdj
      (edge0 Q sourceDensity E0 e) (E0.edge_mem_family Q sourceDensity e) c
    simpa only [physicalRootGood, physicalRootVertex_exceptionalIndex,
      indexedPhysicalEdge_exceptionalIndex] using hadj
  · exact F.side_nonneg
  · exact F.margin_zero
  · exact F.margin_one

end Erdos547b.ZhaoClaim615RichPhysicalPartThree

#print axioms Erdos547b.ZhaoClaim615RichPhysicalPartThree.exceptionalPartThreeCertificate
