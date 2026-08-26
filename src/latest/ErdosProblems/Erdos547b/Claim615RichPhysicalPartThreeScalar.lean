/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPhysicalPartThree
import ErdosProblems.Erdos547b.Claim615RichPhysicalFiberMass

/-!
# A common-capacity Appendix-A.2 record for physical exceptional fibers

In the nonextreme case both endpoints have the same eventual lower capacity.
The six natural parameters of Appendix A.2 may therefore be specialized to
one common endpoint budget.  This file records that specialization and the
source fact that every component selected from `nontrivialMajorBranches` has
at least two vertices.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPhysicalPartThreeScalar

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichPhysicalFiberPlan
open Erdos547b.ZhaoClaim615RichPhysicalFiberMass
open Erdos547b.ZhaoClaim615RichPhysicalPartThree
open Erdos547b.ZhaoLemma54AppendixA
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.RegularPair

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
variable
  (S : SelectedF0 P (nontrivialMajorBranches P) target slack)
variable {cap0 : K0 Q sourceDensity E0 → ℕ}
variable {cap1 : K1 Q sourceDensity E0 Mb → ℕ}
variable {capb : Kb Q sourceDensity Mb → ℕ}
variable
  (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
    cap0 cap1 capb)

/-- Every component of a physical exceptional fiber is one of the selected
nontrivial branches. -/
theorem exceptionalFiber_size_ge_two
    (e : K0 Q sourceDensity E0)
    (i : Fin (matchingFiber
      (assignedPhysicalIndex (Q := Q) (sourceDensity := sourceDensity)
        (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A))
      (exceptionalIndex Q sourceDensity E0 Mb e)).card) :
    2 ≤ (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A)
      (exceptionalIndex Q sourceDensity E0 Mb e)).size i := by
  let assign := assignedPhysicalIndex (Q := Q)
    (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  let fiber := matchingFiber assign
    (exceptionalIndex Q sourceDensity E0 Mb e)
  let j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P :=
    selectedEquiv fiber i
  have hjfiber : j ∈ fiber := (selectedEquiv fiber i).property
  have hassign : assign j = exceptionalIndex Q sourceDensity E0 Mb e :=
    (mem_matchingFiber assign
      (exceptionalIndex Q sourceDensity E0 Mb e) j).mp hjfiber
  have hjSelected : j ∈ S.selected :=
    (assignedPhysicalIndex_eq_exceptional_iff
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) j e).mp hassign |>.1
  have hjNontrivial : j ∈ nontrivialMajorBranches P :=
    S.selected_available hjSelected
  exact (mem_nontrivialMajorBranches P j).mp hjNontrivial |>.2

/-- Construct the complete physical Appendix-A.2 fact record by taking all
four endpoint/root capacities equal to one natural budget `Z`. -/
noncomputable def exceptionalPartThreeFactsOfCommonCapacity
    (e : K0 Q sourceDensity E0)
    (rho pairDensity removalBudget gamma epsilon : ℝ)
    (rootReserve sideReserve Z : ℕ)
    (hrootSide : rootReserve ≤ sideReserve)
    (hsideZ : sideReserve ≤ Z)
    (hsideSlots :
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
        (exceptionalIndex Q sourceDensity E0 Mb e)).order +
          2 * sideReserve + small ≤ 2 * Z)
    (hrootRound : 3 * epsilon * N ≤ rootReserve)
    (hsideRound : (gamma + 3 * epsilon) * N ≤ sideReserve)
    (hsideNonneg : 0 ≤ (gamma + 3 * epsilon) * N)
    (hmargin : ∀ c : Fin 2,
      (Z : ℝ) + small + 1 + removalBudget + 1 ≤
        physicalFiberRhs Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb rho pairDensity
            (exceptionalIndex Q sourceDensity E0 Mb e) c) :
    ExceptionalPartThreeFacts Q sourceDensity E0 Mb P S A rho
      pairDensity removalBudget gamma epsilon e :=
  let assign := assignedPhysicalIndex (Q := Q)
    (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
  let b := (matchingFiber assign
    (exceptionalIndex Q sourceDensity E0 Mb e)).card
  let F : OrderedRootedForest b :=
    physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
    (exceptionalIndex Q sourceDensity E0 Mb e)
  have hcomponents : b ≤ F.order := by
    change b ≤ ∑ i, F.size i
    calc
      b = ∑ _i : Fin b, 1 := by simp
      _ ≤ ∑ i : Fin b, F.size i := by
        apply Finset.sum_le_sum
        intro i _hi
        have hi :=
          exceptionalFiber_size_ge_two Q sourceDensity E0 Mb P S A e i
        have hi' : 2 ≤ F.size i := by
          simpa only [F, b, assign] using hi
        omega
  have hrootSlots : b + 2 * rootReserve ≤ 2 * Z := by
    have hrootSide' : rootReserve ≤ sideReserve := hrootSide
    have := hsideSlots
    dsimp only [F, b, assign] at hcomponents ⊢
    omega
  { rootReserve := rootReserve
    sideReserve := sideReserve
    X := Z
    Y := Z
    P0 := Z
    Q0 := Z
    numeric :=
      { component_lower := exceptionalFiber_size_ge_two
          Q sourceDensity E0 Mb P S A e
        component_upper := physicalFiber_size_le_small
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)
            (exceptionalIndex Q sourceDensity E0 Mb e)
        X_le_Y := le_rfl
        P_le_X := le_rfl
        rootReserve_le_P := hrootSide.trans hsideZ
        rootReserve_le_Q := hrootSide.trans hsideZ
        rootReserve_le_sideReserve := hrootSide
        root_slots := by simpa only [two_mul] using hrootSlots
        side_slots := by simpa only [Nat.min_self, two_mul] using hsideSlots
        root_rounding := hrootRound
        side_rounding := hsideRound }
    side_nonneg := hsideNonneg
    margin_zero := hmargin 0
    margin_one := hmargin 1 }

end Erdos547b.ZhaoClaim615RichPhysicalPartThreeScalar

#print axioms Erdos547b.ZhaoClaim615RichPhysicalPartThreeScalar.exceptionalFiber_size_ge_two
#print axioms Erdos547b.ZhaoClaim615RichPhysicalPartThreeScalar.exceptionalPartThreeFactsOfCommonCapacity
