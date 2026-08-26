/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPhysicalRootOrientationFamilies

/-!
# Source-only complete-fiber threshold plan for Claim 6.15

The three physical matching families all use Zhao's maximal-cutoff threshold
orientation in the unbalanced case.  This module pastes those literal
orientations and retains their complete-fiber high-budget load bounds.  It
does not assert a static endpoint capacity or mention an embedding result.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPhysicalThresholdRootPlan

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
open Erdos547b.ZhaoClaim615RichPhysicalPartTwo
open Erdos547b.ZhaoClaim615RichPhysicalRootOrientation
open Erdos547b.ZhaoClaim615RichPhysicalRootOrientationFamilies
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoLemma58FiberRootOrientation
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma54ThresholdSourceNumerics

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
  (E0 : SelectedExceptionalEdges Q sourceDensity L eta .unbalanced count)
variable
  (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)

variable (P : ZhaoForestPartition T globalRoot small)
variable {target slack : ℕ} {ratio : ℝ}
variable (S : SelectedF0 P (balancedMajorBranches P ratio) target slack)

/-- Source and rounding facts needed by the three root-orientation
constructors.  In particular there is no host-capacity margin here. -/
structure PhysicalThresholdSourceFacts
    (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
    (gamma epsilon : ℝ) : Prop where
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

/-- A root-admissible orientation and complete-fiber load bound on every
physical matching edge. -/
structure PhysicalThresholdRootPlan
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      cap0 cap1 capb) : Type (max u v w) where
  fiber : ∀ e : PhysicalIndex Q sourceDensity E0 Mb,
    FiberRootOrientationWithLoad
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) e)
      (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) e)

namespace PhysicalThresholdRootPlan

/-- Forget the load bound and retain the global root-only physical plan. -/
def toRootOrientationPlan
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    {A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      cap0 cap1 capb}
    (D : PhysicalThresholdRootPlan Q sourceDensity E0 Mb P S A) :
    PhysicalRootOrientationPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A where
  orient := fun e ↦ (D.fiber e).orient
  root_adj := fun e i ↦ (D.fiber e).root_good i

/-- The pasted orientation obeys its stored complete-fiber load bound. -/
theorem sideLoad_le
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    {A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      cap0 cap1 capb}
    (D : PhysicalThresholdRootPlan Q sourceDensity E0 Mb P S A)
    (e : PhysicalIndex Q sourceDensity E0 Mb) (c : Fin 2) :
    sideLoad
        (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A) e)
        ((D.toRootOrientationPlan).orient e) c ≤
      (D.fiber e).loadBound :=
  (D.fiber e).load_le c

end PhysicalThresholdRootPlan

/-- Reindex family-wise root/load certificates by the canonical physical
`Fin` index. -/
noncomputable def physicalThresholdFiberOfFamilies
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      cap0 cap1 capb)
    (D0 : ∀ e : K0 Q sourceDensity E0,
      FiberRootOrientationWithLoad
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
      FiberRootOrientationWithLoad
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
      FiberRootOrientationWithLoad
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
    FiberRootOrientationWithLoad
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) e)
      (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) e) := by
  let tagged := (Fintype.equivFin
    (PhysicalEdge Q sourceDensity E0 Mb)).symm e
  have htag : Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb) tagged = e :=
    (Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb)).apply_symm_apply e
  rcases tagged with e0 | e1
  · exact htag ▸ D0 e0
  · rcases e1 with e1 | eb
    · exact htag ▸ D1 e1
    · exact htag ▸ Db eb

/-- Construct the source-only unbalanced threshold plan on all three
physical families. -/
noncomputable def physicalPartTwoPartOneRootPlan
    (gamma epsilon : ℝ)
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      (exceptionalPartTwoCapacity Q sourceDensity E0 ratio gamma epsilon N)
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon))
    (havailable : balancedMajorBranches P ratio ⊆ halfBranches P)
    (F : PhysicalThresholdSourceFacts (small := small) (ratio := ratio)
      Q sourceDensity E0 Mb gamma epsilon) :
    PhysicalThresholdRootPlan Q sourceDensity E0 Mb P S A where
  fiber := physicalThresholdFiberOfFamilies Q sourceDensity E0 Mb P S A
    (fun e ↦ (exceptionalPartTwoRootOrientation Q sourceDensity Mb P S A rfl e
      F.ratio_nonneg F.ratio_le_half F.N_pos F.gamma_nonneg
      F.epsilon_nonneg (F.exceptional_target_nonneg e)
      (F.exceptional_high_nonneg e) F.rounding F.eta_pos F.row_A_nonneg
      F.adj_A).withLoad
        (thresholdHighBudget
          (exceptionalHighDensity Q sourceDensity E0 e) gamma N)
        (exceptionalPartTwoRootOrientation_sideLoad_le Q sourceDensity Mb P S
          A rfl e F.ratio_nonneg F.ratio_le_half F.N_pos F.gamma_nonneg
          F.epsilon_nonneg (F.exceptional_target_nonneg e)
          (F.exceptional_high_nonneg e) F.rounding F.eta_pos F.row_A_nonneg
          F.adj_A))
    (fun e ↦ remainingPartOneRootOrientationTotal Q sourceDensity E0 Mb P S
      A e F.N_pos F.gamma_nonneg F.epsilon_nonneg F.rounding F.adj_A)
    (fun e ↦ reservedPartOneRootOrientationTotal Q sourceDensity E0 Mb P S
      A havailable e F.N_pos F.gamma_nonneg F.epsilon_nonneg F.rounding
      F.adj_B)

end Erdos547b.ZhaoClaim615RichPhysicalThresholdRootPlan

#print axioms Erdos547b.ZhaoClaim615RichPhysicalThresholdRootPlan.physicalThresholdFiberOfFamilies
#print axioms Erdos547b.ZhaoClaim615RichPhysicalThresholdRootPlan.physicalPartTwoPartOneRootPlan
#print axioms Erdos547b.ZhaoClaim615RichPhysicalThresholdRootPlan.PhysicalThresholdRootPlan.sideLoad_le
