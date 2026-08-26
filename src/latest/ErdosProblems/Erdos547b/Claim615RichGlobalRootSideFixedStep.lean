/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichGlobalRootSidePlan
import ErdosProblems.Erdos547b.Lemma58GlobalFixedOrientationPlan

/-!
# Fixed owner steps under a finite rich root-side plan

The existing root-side wrappers cover canonical threshold and Appendix steps.
This companion packages a continuation whose orientation was fixed once on
the complete physical fiber, while retaining membership in the larger finite
root-side plan used by the mixed nonextreme application.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichGlobalRootSideFixedStep

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichDynamicApplication
open Erdos547b.ZhaoClaim615RichGlobalRootSidePlan
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoLemma58OwnerLocalStep
open Erdos547b.ZhaoLemma58PlannedOwnerLocalStep
open Erdos547b.ZhaoLemma58GlobalPlannedOwnerSuccessor
open Erdos547b.ZhaoLemma58GlobalFixedOrientationPlan

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
variable (E0 : SelectedExceptionalEdges Q sourceDensity L eta which count)
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
  (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb cap0 cap1 capb)

/-- Attach a finite rich root-side plan to a fixed-orientation owner step. -/
def plannedFixedOwnerLocalStepData_of_rootSidePlan
    (hT : T.IsTree)
    (Dside : PhysicalRootSidePlan Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (e : PhysicalIndex Q sourceDensity E0 Mb)
    (n : ℕ) (hn : n < P.numParts)
    (externalParent : Fin (onlineOwnerBatch (branchForest P)
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) e n hn).card → Bv)
    (whole live : Fin 2 → Finset Bv) (rho density : ℝ)
    (D : FixedOrientationStepData
      (onlineOwnerBatchForest (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e n hn) G externalParent
      (onlineOwnerBatchFixedOrientation (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) orient e n hn)
      whole live rho density)
    (hroot : ∀ i,
      (onlineOwnerBatchFixedOrientation (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) orient e n hn i) 0 ∈ Dside.sides e) :
    PlannedOwnerLocalStepData
      (onlineOwnerBatchForest (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e n hn) G externalParent
      whole live rho density
      (onlineOwnerBatchRootAllowed (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e n hn
        (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A Dside).branchRootSides)
      (onlineOwnerBatchCoordinateAllowed (branchForest P)
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e n hn
        (richRootSideTargetPlan Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A Dside).coordinateSides) :=
  .fixed D
    (onlineOwnerBatch_root_mem_rootSidePlan Pcluster Gdegree threshold quota R
      miss Q sourceDensity E0 Mb P S A Dside e n hn _ hroot)
    (onlineOwnerBatch_coordinate_mem_rootSidePlan Pcluster Gdegree threshold
      quota R miss Q sourceDensity E0 Mb P S A hT Dside e n hn _ hroot)

end Erdos547b.ZhaoClaim615RichGlobalRootSideFixedStep

#print axioms Erdos547b.ZhaoClaim615RichGlobalRootSideFixedStep.plannedFixedOwnerLocalStepData_of_rootSidePlan
