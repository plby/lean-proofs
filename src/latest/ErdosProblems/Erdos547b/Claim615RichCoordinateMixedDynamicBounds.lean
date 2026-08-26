/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichCoordinateMixedDynamicApplication
import ErdosProblems.Erdos547b.HierarchicalCoordinateMixedDynamicResidual

/-!
# Pool-load boundary for the rich Claim 6.15 mixed hierarchy

This is the Claim 6.15 specialization of the generic coordinate-pool load
accounting.  Its hypotheses no longer mention live residual sets.  Earlier
images are charged once through the literal coordinate pool load.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichCoordinateMixedDynamicBounds

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615HierarchicalCoordinateSourceLayout
open Erdos547b.ZhaoClaim615HierarchicalCoordinateHostPools
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615CoordinateMixedDynamicLayout
open Erdos547b.ZhaoClaim615CoordinateMixedDynamicEmbedding
open Erdos547b.ZhaoClaim615RichCoordinateMixedDynamicApplication
open Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicResidual
open Erdos547b.ZhaoLemma59HierarchicalCoordinateMixedDynamicResidual.MixedDynamicNonselectedLoadFacts
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoSection6Dichotomy

universe u v w

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small target slack : ℕ}

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

section Source

/-- Literal coordinate-pool load and parent-degree bounds suffice for the
full rich mixed-dynamic Claim 6.15 embedding. -/
theorem isContained_of_richMixedDynamicLoadFacts
    (hT : T.IsTree) (P : ZhaoForestPartition T globalRoot small)
    (optional : Finset V)
    {available : Finset
      (ZhaoClaim615CoordinateSourceAllocation.BranchIndex P)}
    (S : SelectedF0 P available target slack)
    {K0 K1 Kb : Type*}
    [Fintype K0] [DecidableEq K0]
    [Fintype K1] [DecidableEq K1]
    [Fintype Kb] [DecidableEq Kb]
    (capacity0 : K0 → ℕ) (capacity1 : K1 → ℕ) (capacityb : Kb → ℕ)
    (A : SourceAllocation P S K0 K1 Kb capacity0 capacity1 capacityb)
    (edge0 : K0 → MatchingEdge Q.claim67.M)
    (edge1 : K1 → MatchingEdge Q.claim67.M)
    (edgeb : Kb → MatchingEdge Q.claim67.M)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (Hpair : ReducedPairRealization Pcluster R G rho density)
    (hparity : OptionalBranchRootParity P optional)
    (z : Bv)
    (Hload : MixedDynamicNonselectedLoadFacts
      (AllocationHierarchy hT P optional) G (fun _ : Fin 1 => z)
      (mixedSourceRootOnly hT P optional)
      (mixedSourceRootPool hT P optional S capacity0 capacity1 capacityb A
        edge0 edge1 edgeb orient)
      (mixedSourceInteriorPool hT P optional S capacity0 capacity1 capacityb A
        edge0 edge1 edgeb orient)
      (mixedSourcePairPool hT P optional S capacity0 capacity1 capacityb A
        edge0 edge1 edgeb)
      (mixedSourceOrient hT P optional orient)
      (slotWhole Pcluster Gdegree threshold quota R miss Q)
      (mixedRichRawAfterRoot Pcluster Gdegree threshold quota R miss Q z)
      rho (fun _ => density)) :
    T.IsContained G := by
  classical
  let Hres := MixedDynamicNonselectedLoadFacts.toResidualFacts
    (AllocationHierarchy hT P optional) G (fun _ : Fin 1 => z)
    (mixedSourceRootOnly hT P optional)
    (mixedSourceSelected hT P optional)
    (mixedSourceRootPool hT P optional S capacity0 capacity1 capacityb A
      edge0 edge1 edgeb orient)
    (mixedSourceInteriorPool hT P optional S capacity0 capacity1 capacityb A
      edge0 edge1 edgeb orient)
    (mixedSourcePairPool hT P optional S capacity0 capacity1 capacityb A
      edge0 edge1 edgeb)
    (mixedSourceOrient hT P optional orient)
    (slotWhole Pcluster Gdegree threshold quota R miss Q)
    (mixedRichRawAfterRoot Pcluster Gdegree threshold quota R miss Q z)
    rho (fun _ => density) (fun _ => density)
    (fun i hi => by
      change False at hi
      exact hi) Hload
  exact isContained_of_richMixedDynamicResidualFacts Pcluster Gdegree threshold
    quota R miss Q hT P optional S capacity0 capacity1 capacityb A edge0 edge1
    edgeb orient G rho density Hpair hparity z Hres

end Source

end Erdos547b.ZhaoClaim615RichCoordinateMixedDynamicBounds

#print axioms Erdos547b.ZhaoClaim615RichCoordinateMixedDynamicBounds.isContained_of_richMixedDynamicLoadFacts
