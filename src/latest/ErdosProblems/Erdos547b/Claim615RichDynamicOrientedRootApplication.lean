/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichDynamicRootCleaning
import ErdosProblems.Erdos547b.Lemma58OrientedFullCutTree

/-!
# Rich root cleaning with literal source orientation

This wrapper connects the exact rich target list to the
orientation-sensitive cut-tree backend.  The same `orient` occurs in root
cleaning, edge-local certificates, and final matching assembly.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichDynamicOrientedRootApplication

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim616HierarchyAttachments
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichDynamicHostLayout
open Erdos547b.ZhaoClaim615RichDynamicApplication
open Erdos547b.ZhaoClaim615RichDynamicRootLayout
open Erdos547b.ZhaoClaim615RichDynamicRootTargets
open Erdos547b.ZhaoClaim615RichDynamicRootCleaning
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoLemma58RootCandidateCleaning
open Erdos547b.ZhaoLemma58OrientedFullCutTree

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
variable
  (A : PhysicalSourceAllocationWith Q sourceDensity P S E0 Mb
    cap0 cap1 capb)

/-- Apply rich root cleaning to fixed-orientation edge-local certificates.
There is no broad cut-parent bad set: every forbidden set is indexed by the
literal matching edge and side of the deleted parent. -/
theorem exists_treeCopy_of_richRootCleaningFacts_fixedOrient
    (hT : T.IsTree)
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (orient : ZhaoClaim615CoordinateSourceAllocation.BranchIndex P →
      Fin 2 ≃ Fin 2)
    (F : RichRootCleaningFacts Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rho density H orient)
    (hdata : ∀ rootImage : Fin P.numParts → Bv,
      (∀ q, rootImage q ∈ rootCandidate G rho
        (rootWhole Pcluster Gdegree threshold quota R miss Q P)
        (rootRaw Pcluster Gdegree threshold quota R miss Q P)
        (richRootTargets Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb P S A orient)
        (richTargetWhole Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb)
        (richTargetRaw Pcluster Gdegree threshold quota R miss Q
          sourceDensity E0 Mb) q) →
      FixedOrientedCutEdgeData P G G rootImage
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
          E0 Mb) orient) :
    Nonempty (T.Copy G) := by
  refine exists_treeCopy_of_targetCleanedRoots_and_fixedOrientedDataWithLinks
    P G G le_rfl rho
    (rootWhole Pcluster Gdegree threshold quota R miss Q P)
    (rootRaw Pcluster Gdegree threshold quota R miss Q P)
    (richRootTargets Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb P S A orient)
    (richTargetWhole Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb)
    (richTargetRaw Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb)
    (richRootLoss Pcluster Gdegree threshold quota R miss Q sourceDensity E0
      Mb P S A rho orient) ?_ ?_ ?_
    (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A))
    (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb) orient ?_ ?_ ?_
  · exact F.rootTargetBad_le Pcluster Gdegree threshold quota R miss Q
      sourceDensity E0 Mb P S A G rho density H orient
  · intro q
    simpa only [card_rootRaw] using F.root_budget q
  · exact F.rootLink Pcluster Gdegree threshold quota R miss Q sourceDensity
      E0 Mb P S A hT G rho density H orient
  · exact endpointSupport_disjoint
      (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      hdisjoint
  · intro q e c
    exact rootRawSide_disjoint_endpoint
      (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (componentReservoirSide P q) e c
  · exact hdata

end Erdos547b.ZhaoClaim615RichDynamicOrientedRootApplication

#print axioms Erdos547b.ZhaoClaim615RichDynamicOrientedRootApplication.exists_treeCopy_of_richRootCleaningFacts_fixedOrient
