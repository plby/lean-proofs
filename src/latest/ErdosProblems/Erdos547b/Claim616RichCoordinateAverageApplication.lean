/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616RichCoordinateSourceApplication
import ErdosProblems.Erdos547b.IntegralAverageCapacity

/-!
# Canonical average capacities for rich coordinate containment

The three source-family capacities and the selected-cluster capacity are
chosen canonically by rounding their average demands upward.  Consequently
the public containment theorem no longer asks for `SourcePackingScalars` or
an already-constructed source allocation.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim616RichCoordinateAverageApplication

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim68ParityHalf
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616SourceBridge
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616RichCoordinateAllocation
open Erdos547b.ZhaoClaim616RichCoordinateCanonicalNumerics
open Erdos547b.ZhaoClaim616RichCoordinateSourceApplication
open Erdos547b.ZhaoIntegralAverageCapacity
open Erdos547b.ZhaoLemma59Part2Full

universe u v w

/-- Average root-cluster load, plus the one-component packing slack. -/
def canonicalClusterCapacity
    (target slack small bins : ℕ) : ℕ :=
  averageCapacity ((target + slack) * small) bins + small

/-- Average selected deep demand over the `4 · rhoK` accessible edges. -/
def canonicalSelectedCapacity
    (selectedDeep rhoK : ℕ) : ℕ :=
  averageCapacity selectedDeep (4 * rhoK)

/-- Average whole-branch demand, plus the one-component packing slack. -/
def canonicalBranchCapacity
    (demand bins small : ℕ) : ℕ :=
  averageCapacity demand bins + small

variable {V : Type u} {B : Type v} {K : Type w}
variable [Fintype V] [DecidableEq V]
variable [Fintype B] [DecidableEq B] [Fintype K] [DecidableEq K]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}
variable (G Gdegree : SimpleGraph B)
variable [DecidableRel G.Adj] [DecidableRel Gdegree.Adj]
variable (cluster : K → Finset B) (epsilon density : ℚ)
variable [DecidableRel (regularityReducedGraph G cluster epsilon density).Adj]
variable {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
variable {C67 : Claim67Certificate
  (regularityReducedGraph G cluster epsilon density) L miss}
variable {degreeA : Finset (MatchingEdge C67.M) → ℝ}
variable
  (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
    degreeA)
variable (Aroot Broot : K) (C : Finset K) (rhoK : ℕ)
variable (Pcluster : ClusterAssignment B K) (threshold quota : ℕ)
variable
  (H : IndexedHostSystem G cluster epsilon density Aroot Broot C
    (MatchingDecomposition.Mout
      (R := regularityReducedGraph G cluster epsilon density) D)
    (MatchingDecomposition.V2
        (R := regularityReducedGraph G cluster epsilon density) D ∩
      (matchingSupport (MatchingDecomposition.Mout
          (R := regularityReducedGraph G cluster epsilon density) D) \
        matchingSupport (MatchingDecomposition.Mb
          (R := regularityReducedGraph G cluster epsilon density) D)))
    rhoK Pcluster threshold quota Gdegree)

include H

/-- The canonical average-capacity specialization.  Only positivity of the
three bin families remains from source packing; all four aggregate capacity
inequalities are consequences of upward rounding. -/
theorem isContained_of_richCoordinateAverageCapacities
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (hsmall : 1 ≤ small)
    (S : SelectedF0Within (branchForest P) (halfBranches P) target slack)
    (mbSide : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D → Fin 2)
    (hCV1 : C ⊆ MatchingDecomposition.V1
      (R := regularityReducedGraph G cluster epsilon density) D)
    (hV1Adj : ∀ x ∈ MatchingDecomposition.V1
      (R := regularityReducedGraph G cluster epsilon density) D,
        (regularityReducedGraph G cluster epsilon density).Adj Aroot x)
    (hMbAdj : ∀ e : ReservedEdge
      (R := regularityReducedGraph G cluster epsilon density) D,
        (regularityReducedGraph G cluster epsilon density).Adj Broot
          (matchingEdgeEndpoint e.1.1 (mbSide e)))
    (hrhoK : 0 < rhoK)
    (hremaining : 0 < (MatchingDecomposition.MoneEdges
      (R := regularityReducedGraph G cluster epsilon density) D C).card)
    (hreserved : 0 < (MatchingDecomposition.mbEdges
      (R := regularityReducedGraph G cluster epsilon density) D).card)
    (m : ℕ) (removalBudget : ℝ)
    (scale : CanonicalClusterScaleFacts cluster Aroot Broot
      (epsilon : ℝ) quota m)
    (margins : CanonicalMarginScalars P.numParts small
      (canonicalClusterCapacity target slack small C.card)
      (canonicalSelectedCapacity
        (∑ j ∈ S.selected, ((branchForest P).branches.size j - 1)) rhoK)
      (canonicalBranchCapacity (OrderedBranchForest.edgeDemand (F1 P S))
        (MatchingDecomposition.MoneEdges
          (R := regularityReducedGraph G cluster epsilon density) D C).card
        small)
      (canonicalBranchCapacity (OrderedBranchForest.edgeDemand (Fb P))
        (MatchingDecomposition.mbEdges
          (R := regularityReducedGraph G cluster epsilon density) D).card
        small)
      quota m (epsilon : ℝ) (density : ℝ) removalBudget)
    (online : CanonicalOnlineScalars
      (Fintype.card
          (Erdos547b.ZhaoClaim68BranchAdapter.ChildKey
            (Erdos547b.ZhaoLemma614HierarchicalFullTree.wholeOrderedTree
              T hT globalRoot)) +
        (P.numParts + Fintype.card (BranchIndex P) + P.numParts))
      small m quota (epsilon : ℝ) removalBudget) :
    T.IsContained G := by
  have hC : 0 < C.card := by
    rw [H.cluster_card]
    exact hrhoK
  have hselectedBins : 0 < 4 * rhoK :=
    Nat.mul_pos (by norm_num) hrhoK
  let packing : SourcePackingScalars target slack small C.card rhoK
      (MatchingDecomposition.MoneEdges
        (R := regularityReducedGraph G cluster epsilon density) D C).card
      (MatchingDecomposition.mbEdges
        (R := regularityReducedGraph G cluster epsilon density) D).card
      (canonicalClusterCapacity target slack small C.card)
      (canonicalSelectedCapacity
        (∑ j ∈ S.selected, ((branchForest P).branches.size j - 1)) rhoK)
      (canonicalBranchCapacity (OrderedBranchForest.edgeDemand (F1 P S))
        (MatchingDecomposition.MoneEdges
          (R := regularityReducedGraph G cluster epsilon density) D C).card
        small)
      (canonicalBranchCapacity (OrderedBranchForest.edgeDemand (Fb P))
        (MatchingDecomposition.mbEdges
          (R := regularityReducedGraph G cluster epsilon density) D).card
        small)
      (∑ j ∈ S.selected, ((branchForest P).branches.size j - 1))
      (OrderedBranchForest.edgeDemand (F1 P S))
      (OrderedBranchForest.edgeDemand (Fb P)) := {
    rhoK_pos := hrhoK
    remaining_pos := hremaining
    reserved_pos := hreserved
    level0 := by
      simpa only [canonicalClusterCapacity] using
        total_add_slack_le ((target + slack) * small) C.card small hC
    selected := by
      simpa only [canonicalSelectedCapacity] using
        total_le_mul_averageCapacity
          (∑ j ∈ S.selected, ((branchForest P).branches.size j - 1))
          (4 * rhoK) hselectedBins
    residual := by
      simpa only [canonicalBranchCapacity] using
        total_add_slack_le (OrderedBranchForest.edgeDemand (F1 P S))
          (MatchingDecomposition.MoneEdges
            (R := regularityReducedGraph G cluster epsilon density) D C).card
          small hremaining
    minor := by
      simpa only [canonicalBranchCapacity] using
        total_add_slack_le (OrderedBranchForest.edgeDemand (Fb P))
          (MatchingDecomposition.mbEdges
            (R := regularityReducedGraph G cluster epsilon density) D).card
          small hreserved
  }
  exact isContained_of_richCoordinatePackingScalars G Gdegree cluster epsilon
    density D Aroot Broot C rhoK Pcluster threshold quota H hT P hsmall S
    (canonicalClusterCapacity target slack small C.card)
    (canonicalSelectedCapacity
      (∑ j ∈ S.selected, ((branchForest P).branches.size j - 1)) rhoK)
    (canonicalBranchCapacity (OrderedBranchForest.edgeDemand (F1 P S))
      (MatchingDecomposition.MoneEdges
        (R := regularityReducedGraph G cluster epsilon density) D C).card small)
    (canonicalBranchCapacity (OrderedBranchForest.edgeDemand (Fb P))
      (MatchingDecomposition.mbEdges
        (R := regularityReducedGraph G cluster epsilon density) D).card small)
    mbSide hCV1 hV1Adj hMbAdj m removalBudget scale margins packing online

end Erdos547b.ZhaoClaim616RichCoordinateAverageApplication

#print axioms Erdos547b.ZhaoClaim616RichCoordinateAverageApplication.isContained_of_richCoordinateAverageCapacities
