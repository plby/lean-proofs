/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPhysicalThresholdRootPlan
import ErdosProblems.Erdos547b.Claim615RichPhysicalPartThree
import ErdosProblems.Erdos547b.Claim615RichGlobalRootSidePlan

/-!
# Source-only root plan for the nonextreme exceptional case

Exceptional fibers will be realized by Appendix A and therefore retain both
root-admissible sides.  The remaining and reserved fibers use their genuine
complete-fiber Part-1 orientations.  A harmless orientation on the exceptional
fiber is stored only so that all ordinary orientations can be pasted through
the existing physical indexing API; its load bound is the full fiber order.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPhysicalPartThreeRootPlan

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
open Erdos547b.ZhaoClaim615RichPhysicalPartThree
open Erdos547b.ZhaoClaim615RichPhysicalRootOrientation
open Erdos547b.ZhaoClaim615RichPhysicalRootOrientationFamilies
open Erdos547b.ZhaoClaim615RichPhysicalThresholdRootPlan
open Erdos547b.ZhaoClaim615RichDynamicApplication
open Erdos547b.ZhaoClaim615RichGlobalRootSidePlan
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoLemma58FiberRootOrientation
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58ChosenOwnerBatches
open Erdos547b.ZhaoLemma58ChosenMatchingAssembly
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoLemma58GlobalPlannedOwnerSuccessor
open Erdos547b.ZhaoLemma58GlobalFixedOrientationPlan
open Erdos547b.ZhaoLemma58SelectedOrientationReindex
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
  (E0 : SelectedExceptionalEdges Q sourceDensity L eta .nonextreme count)
variable
  (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)

variable (P : ZhaoForestPartition T globalRoot small)
variable {target slack : ℕ}
variable (S : SelectedF0 P (nontrivialMajorBranches P) target slack)

/-- Source and rounding facts needed for the two ordinary Part-1 families and
for root admissibility on both sides of every nonextreme exceptional edge. -/
structure PhysicalPartThreeRootSourceFacts
    (E0 : SelectedExceptionalEdges Q sourceDensity L eta .nonextreme count)
    (Mb : PreliminaryReservedEdges Q sourceDensity L N targetB cap cardBound)
    (gamma epsilon : ℝ) : Prop where
  N_pos : 0 < N
  gamma_nonneg : 0 ≤ gamma
  epsilon_nonneg : 0 ≤ epsilon
  rounding : (2 : ℝ) + 3 * small ≤ 3 * (epsilon * N)
  eta_pos : 0 < eta
  adj_A : ∀ x, 0 < sourceDensity (Sum.inl Q.A) x →
    (padGraph R).Adj (Sum.inl Q.A) x
  adj_B : ∀ x, 0 < sourceDensity (Sum.inl Q.B) x →
    (padGraph R).Adj (Sum.inl Q.B) x

/-- A dummy complete-fiber orientation on a nonextreme exceptional edge.
Both sides are root-admissible; the full order is an automatic load bound. -/
noncomputable def exceptionalPartThreeAuxiliaryRootOrientation
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      cap0 cap1 capb)
    (heta : 0 < eta)
    (hAdj : ∀ x, 0 < sourceDensity (Sum.inl Q.A) x →
      (padGraph R).Adj (Sum.inl Q.A) x)
    (e : K0 Q sourceDensity E0) :
    FiberRootOrientationWithLoad
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
        (exceptionalIndex Q sourceDensity E0 Mb e))
      (physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (exceptionalIndex Q sourceDensity E0 Mb e)) := by
  let forest := physicalFiberForest (Pcluster := Pcluster)
    (Gdegree := Gdegree) (threshold := threshold) (quota := quota) (R := R)
    (miss := miss) (Q := Q) (sourceDensity := sourceDensity) (E0 := E0)
    (Mb := Mb) (P := P) (S := S) (A := A)
    (exceptionalIndex Q sourceDensity E0 Mb e)
  let orient : Fin (matchingFiber
      (assignedPhysicalIndex (Q := Q) (sourceDensity := sourceDensity)
        (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A))
      (exceptionalIndex Q sourceDensity E0 Mb e)).card → Fin 2 ≃ Fin 2 :=
    fun _ ↦ Equiv.refl _
  refine {
    orient := orient
    root_good := ?_
    loadBound := forest.order
    load_le := ?_
  }
  · intro i
    have hadj := nonextremeRawSide_adj_A Q sourceDensity L eta heta
      hAdj (edge0 Q sourceDensity E0 e)
        (E0.edge_mem_family Q sourceDensity e) 0
    simpa only [physicalRootGood, physicalRootVertex_exceptionalIndex,
      indexedPhysicalEdge_exceptionalIndex, orient, Equiv.refl_apply] using hadj
  · intro c
    change sideLoad forest orient c ≤ forest.order
    have htotal := sideLoad_zero_add_one forest orient
    fin_cases c
    · change sideLoad forest orient 0 ≤ forest.order
      omega
    · change sideLoad forest orient 1 ≤ forest.order
      omega

/-- A complete-fiber root orientation and load bound for every physical edge
in the nonextreme source allocation. -/
structure PhysicalPartThreeAuxiliaryRootPlan
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

namespace PhysicalPartThreeAuxiliaryRootPlan

def toRootOrientationPlan
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    {A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      cap0 cap1 capb}
    (D : PhysicalPartThreeAuxiliaryRootPlan Q sourceDensity E0 Mb P S A) :
    PhysicalRootOrientationPlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A where
  orient := fun e ↦ (D.fiber e).orient
  root_adj := fun e i ↦ (D.fiber e).root_good i

end PhysicalPartThreeAuxiliaryRootPlan

/-- Literal global branch orientation obtained by reading the orientation of
the branch's assigned physical fiber. -/
def partThreeAuxiliaryGlobalOrient
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    {A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      cap0 cap1 capb}
    (D : PhysicalPartThreeAuxiliaryRootPlan Q sourceDensity E0 Mb P S A)
    : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P → Fin 2 ≃ Fin 2 :=
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  assembledOrient assign (fun e ↦
    extendSelectedOrient (matchingFiber assign e) (D.fiber e).orient)

/-- Restricting the pasted complete-fiber orientation to an owner batch keeps
its root side inside the maximal physical root-good side plan. -/
theorem auxiliary_onlineOwnerBatch_root_mem
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
    {capb : Kb Q sourceDensity Mb → ℕ}
    {A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      cap0 cap1 capb}
    (D : PhysicalPartThreeAuxiliaryRootPlan Q sourceDensity E0 Mb P S A)
    (e : PhysicalIndex Q sourceDensity E0 Mb)
    (n : ℕ) (hn : n < P.numParts)
    (i : Fin (onlineOwnerBatch (branchForest P)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) e n hn).card) :
    (onlineOwnerBatchFixedOrientation (branchForest P)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A))
      (partThreeAuxiliaryGlobalOrient (Pcluster := Pcluster)
        (Gdegree := Gdegree) (threshold := threshold) (quota := quota)
        (R := R) (miss := miss) Q sourceDensity E0 Mb P S D) e n hn i) 0 ∈
      (physicalRootGoodSidePlan Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb).sides e := by
  let assign := richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  let orient := partThreeAuxiliaryGlobalOrient (Pcluster := Pcluster)
    (Gdegree := Gdegree) (threshold := threshold) (quota := quota) (R := R)
    (miss := miss) Q sourceDensity E0 Mb P S D
  rw [mem_physicalRootGoodSidePlan]
  have hgood := (D.fiber e).root_good
    (selectedEquiv (onlineOwnerBatch (branchForest P) assign e n hn) i)
  change physicalRootGood (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) e
      ((onlineOwnerBatchFixedOrientation (branchForest P) assign orient e n hn
        i) 0)
  let j := onlineOwnerBatchBranch (branchForest P) assign e n hn i
  let iFiber := selectedEquiv
    (onlineOwnerBatch (branchForest P) assign e n hn) i
  have hrestrict :
      onlineOwnerBatchFixedOrientation (branchForest P) assign orient e n hn i =
        globalFixedFiberOrientation (branchForest P) assign orient e iFiber :=
    rfl
  have hfiber :
      globalFixedFiberOrientation (branchForest P) assign orient e =
        (D.fiber e).orient := by
    simpa only [orient, partThreeAuxiliaryGlobalOrient] using
      (globalFixedFiberOrientation_assembledOrient (branchForest P) assign
        (fun f ↦ (D.fiber f).orient) e)
  rw [hrestrict, congrFun hfiber iFiber]
  exact hgood

/-- Reindex the three family-wise certificates through the canonical physical
`Fin` index. -/
noncomputable def physicalPartThreeFiberOfFamilies
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

/-- Paste the harmless exceptional orientation and the two genuine Part-1
orientations into one physical complete-fiber root plan. -/
noncomputable def physicalPartThreeAuxiliaryRootPlan
    {cap0 : K0 Q sourceDensity E0 → ℕ}
    (gamma epsilon : ℝ)
    (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
      cap0
      (remainingPartOneCapacity Q sourceDensity E0 Mb gamma epsilon)
      (reservedPartOneCapacity Q sourceDensity Mb gamma epsilon))
    (F : PhysicalPartThreeRootSourceFacts (small := small)
      Q sourceDensity E0 Mb gamma epsilon) :
    PhysicalPartThreeAuxiliaryRootPlan Q sourceDensity E0 Mb P S A where
  fiber := physicalPartThreeFiberOfFamilies Q sourceDensity E0 Mb P S A
    (fun e ↦ exceptionalPartThreeAuxiliaryRootOrientation Q sourceDensity
      E0 Mb P S A F.eta_pos F.adj_A e)
    (fun e ↦ remainingPartOneRootOrientationTotal Q sourceDensity E0 Mb P S
      A e F.N_pos F.gamma_nonneg F.epsilon_nonneg F.rounding F.adj_A)
    (fun e ↦ reservedPartOneRootOrientationTotal Q sourceDensity E0 Mb P S
      A (fun j hj ↦ (mem_nontrivialMajorBranches P j).mp hj |>.1) e
      F.N_pos F.gamma_nonneg F.epsilon_nonneg F.rounding F.adj_B)

end Erdos547b.ZhaoClaim615RichPhysicalPartThreeRootPlan

#print axioms Erdos547b.ZhaoClaim615RichPhysicalPartThreeRootPlan.exceptionalPartThreeAuxiliaryRootOrientation
#print axioms Erdos547b.ZhaoClaim615RichPhysicalPartThreeRootPlan.physicalPartThreeAuxiliaryRootPlan
