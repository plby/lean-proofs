/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPhysicalFiberPlan

/-!
# Source-allocation mass bounds on the three physical fibers
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichPhysicalFiberMass

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichPhysicalFiberPlan
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58MatchingAssembly
open Erdos547b.ZhaoLemma58SelectedOrientationReindex
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

/-- Every component of every reindexed physical fiber retains the canonical
small-branch bound. -/
theorem physicalFiber_size_le_small
    (e : PhysicalIndex Q sourceDensity E0 Mb)
    (i : Fin (matchingFiber
      (assign (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) e).card) :
    (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) e).size i ≤ small := by
  exact canonical_branch_size_le_small P
    (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv
      (matchingFiber
        (assign (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)) e) i)

theorem exceptionalFiber_order_le_capacity
    (e : K0 Q sourceDensity E0) :
    (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity)
      (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)
      (exceptionalIndex Q sourceDensity E0 Mb e)).order ≤
        cap0 e := by
  rw [selectedForest_order]
  have hfiber : matchingFiber (assign (Q := Q) (sourceDensity := sourceDensity)
      (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A))
      (exceptionalIndex Q sourceDensity E0 Mb e) =
        S.selected.filter (A.F0edge · = e) := by
    ext j
    rw [mem_matchingFiber, Finset.mem_filter]
    exact assignedPhysicalIndex_eq_exceptional_iff
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) j e
  rw [hfiber]
  exact A.F0_load e

theorem remainingFiber_order_le_capacity
    (e : K1 Q sourceDensity E0 Mb) :
    (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity)
      (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)
      (remainingIndex Q sourceDensity E0 Mb e)).order ≤
        cap1 e := by
  rw [selectedForest_order]
  have hfiber : matchingFiber (assign (Q := Q) (sourceDensity := sourceDensity)
      (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A))
      (remainingIndex Q sourceDensity E0 Mb e) =
        (majorResidualBranches P S).filter (A.F1edge · = e) := by
    ext j
    rw [mem_matchingFiber, Finset.mem_filter]
    exact assignedPhysicalIndex_eq_remaining_iff
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) j e
  rw [hfiber]
  exact A.F1_load e

theorem reservedFiber_order_le_capacity
    (havailable : available ⊆ halfBranches P)
    (e : Kb Q sourceDensity Mb) :
    (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity)
      (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)
      (reservedIndex Q sourceDensity E0 Mb e)).order ≤
        capb e := by
  rw [selectedForest_order]
  have hfiber : matchingFiber (assign (Q := Q) (sourceDensity := sourceDensity)
      (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A))
      (reservedIndex Q sourceDensity E0 Mb e) =
        (minorBranches P).filter (A.Fbedge · = e) := by
    ext j
    rw [mem_matchingFiber, Finset.mem_filter]
    exact assignedPhysicalIndex_eq_reserved_iff
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) havailable j e
  rw [hfiber]
  exact A.Fb_load e

/-- A remaining-family average capacity satisfying the literal Part-1
density display yields the full classified threshold source record. -/
theorem remainingFiber_partOneNumerics
    (e : K1 Q sourceDensity E0 Mb)
    (dx dy gamma epsilon N0 : ℝ)
    (hlowHigh : dx ≤ dy) (hN : 0 ≤ N0)
    (hhigh : 0 ≤ (dy - gamma) * N0)
    (hepsilon : 0 ≤ epsilon)
    (hcapacity : (cap1 e : ℝ) ≤
      (dx + dy - 2 * gamma - 3 * epsilon) * N0)
    (hround : (2 : ℝ) + 3 * small ≤ 3 * (epsilon * N0)) :
    ClassifiedThresholdOwnerNumerics
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
        (remainingIndex Q sourceDensity E0 Mb e))
      0 dx dy gamma epsilon N0 small := by
  apply ClassifiedThresholdOwnerNumerics.of_partOneMass
  · exact hlowHigh
  · exact hN
  · exact hhigh
  · exact hepsilon
  · exact physicalFiber_size_le_small
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A)
      (remainingIndex Q sourceDensity E0 Mb e)
  · have horder := remainingFiber_order_le_capacity
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) e
    have horderR :
        ((physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)
          (remainingIndex Q sourceDensity E0 Mb e)).order : ℝ) ≤
            cap1 e := by
      exact_mod_cast horder
    exact horderR.trans hcapacity
  · exact hround

/-- The identical Part-1 construction for a reserved `B`-fiber. -/
theorem reservedFiber_partOneNumerics
    (havailable : available ⊆ halfBranches P)
    (e : Kb Q sourceDensity Mb)
    (dx dy gamma epsilon N0 : ℝ)
    (hlowHigh : dx ≤ dy) (hN : 0 ≤ N0)
    (hhigh : 0 ≤ (dy - gamma) * N0)
    (hepsilon : 0 ≤ epsilon)
    (hcapacity : (capb e : ℝ) ≤
      (dx + dy - 2 * gamma - 3 * epsilon) * N0)
    (hround : (2 : ℝ) + 3 * small ≤ 3 * (epsilon * N0)) :
    ClassifiedThresholdOwnerNumerics
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
        (reservedIndex Q sourceDensity E0 Mb e))
      0 dx dy gamma epsilon N0 small := by
  apply ClassifiedThresholdOwnerNumerics.of_partOneMass
  · exact hlowHigh
  · exact hN
  · exact hhigh
  · exact hepsilon
  · exact physicalFiber_size_le_small
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A)
      (reservedIndex Q sourceDensity E0 Mb e)
  · have horder := reservedFiber_order_le_capacity
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) havailable e
    have horderR :
        ((physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A)
          (reservedIndex Q sourceDensity E0 Mb e)).order : ℝ) ≤
            capb e := by
      exact_mod_cast horder
    exact horderR.trans hcapacity
  · exact hround

/-- An exceptional fiber selected from the balanced major branches inherits
the two-sided colour-ratio classification needed by Zhao Lemma 5.4(2).
Together with a literal per-edge capacity display, this gives the complete
rounded threshold source record for that fiber. -/
theorem exceptionalFiber_partTwoNumerics
    (ratio dx dy gamma epsilon N0 : ℝ)
    (havailable : available = balancedMajorBranches P ratio)
    (e : K0 Q sourceDensity E0)
    (hratio0 : 0 ≤ ratio) (hratioHalf : ratio ≤ 1 / 2)
    (hlowHigh : dx ≤ dy) (hN : 0 ≤ N0)
    (hhigh : 0 ≤ (dy - gamma) * N0)
    (hepsilon : 0 ≤ epsilon)
    (hcapacity : (cap0 e : ℝ) ≤
      (dx + dy - 2 * gamma - 3 * epsilon) * N0 +
        ratio / (1 - ratio) * (dy - dx) * N0)
    (hround : (2 : ℝ) + 3 * small ≤ 3 * (epsilon * N0)) :
    ClassifiedThresholdOwnerNumerics
      (physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)
        (exceptionalIndex Q sourceDensity E0 Mb e))
      ratio dx dy gamma epsilon N0 small := by
  let fiber := matchingFiber
    (assign (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A))
    (exceptionalIndex Q sourceDensity E0 Mb e)
  let F := physicalFiberForest (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
    (P := P) (S := S) (A := A)
    (exceptionalIndex Q sourceDensity E0 Mb e)
  have hselected (i : Fin fiber.card) :
      ((Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv
        fiber i : {j // j ∈ fiber}) :
          ZhaoClaim615CoordinateSourceAllocation.BranchIndex P) ∈ S.selected := by
    let j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P :=
      Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv fiber i
    have hjfiber : j ∈ fiber :=
      (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv
        fiber i).property
    have hassign := (mem_matchingFiber
      (assign (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A))
      (exceptionalIndex Q sourceDensity E0 Mb e) j).mp hjfiber
    exact (assignedPhysicalIndex_eq_exceptional_iff
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A) j e).mp hassign |>.1
  have Pdata : PartTwoLocalData F Finset.univ ratio dx dy gamma epsilon N0 := by
    refine {
      c_nonneg := hratio0
      c_le_half := hratioHalf
      low_le_high := hlowHigh
      ratio_lower := ?_
      ratio_upper := ?_
      mass_le := ?_
    }
    · intro i _
      let j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P :=
        Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv
          fiber i
      have hj := S.selected_available (hselected i)
      rw [havailable] at hj
      have hjratio := (mem_balancedMajorBranches P ratio j).mp hj |>.2.1
      change ratio ≤ (#(branchColourClass P j 0) : ℝ) /
        ((branchForest P).branches.size j : ℝ)
      exact hjratio.le
    · intro i _
      let j : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P :=
        Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv
          fiber i
      have hj := S.selected_available (hselected i)
      rw [havailable] at hj
      have hjratio := (mem_balancedMajorBranches P ratio j).mp hj |>.2.2
      change (#(branchColourClass P j 0) : ℝ) /
          ((branchForest P).branches.size j : ℝ) ≤ 1 - ratio
      exact hjratio.le
    · have horder := exceptionalFiber_order_le_capacity
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A) e
      have horderR : (F.order : ℝ) ≤ cap0 e := by
        exact_mod_cast horder
      simpa only [OrderedRootedForest.order, F] using horderR.trans hcapacity
  exact ClassifiedThresholdOwnerNumerics.of_partTwoLocalData F ratio dx dy
    gamma epsilon N0 small Pdata hN hhigh hepsilon
    (physicalFiber_size_le_small
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A)
      (exceptionalIndex Q sourceDensity E0 Mb e)) hround

end Erdos547b.ZhaoClaim615RichPhysicalFiberMass

#print axioms Erdos547b.ZhaoClaim615RichPhysicalFiberMass.exceptionalFiber_order_le_capacity
#print axioms Erdos547b.ZhaoClaim615RichPhysicalFiberMass.physicalFiber_size_le_small
#print axioms Erdos547b.ZhaoClaim615RichPhysicalFiberMass.remainingFiber_order_le_capacity
#print axioms Erdos547b.ZhaoClaim615RichPhysicalFiberMass.reservedFiber_order_le_capacity
#print axioms Erdos547b.ZhaoClaim615RichPhysicalFiberMass.remainingFiber_partOneNumerics
#print axioms Erdos547b.ZhaoClaim615RichPhysicalFiberMass.reservedFiber_partOneNumerics
#print axioms Erdos547b.ZhaoClaim615RichPhysicalFiberMass.exceptionalFiber_partTwoNumerics
