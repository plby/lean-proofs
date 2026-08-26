/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichDynamicRootLayout

/-!
# Target-cleaned distinguished roots for dynamic Zhao Claim 6.15

This module specializes the complete cut-aware root-cleaning theorem to the
literal rich matching endpoints and the parity-dependent `A₀`/`B₀` root
reservoirs.  Separation of roots from every matching endpoint is discharged
internally from the permanent reserve deletion.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichDynamicRootApplication

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
open Erdos547b.ZhaoLemma58RootCandidateCleaning
open Erdos547b.ZhaoLemma58CutForestReconstruction
open Erdos547b.ZhaoLemma58FullCutTree

universe u v w x

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

/-- The full dynamic tree-copy endpoint with every structural choice fixed to
the rich physical matching and the literal parity-dependent root reserves.
Only the target-cleaning scalar estimates and genuine edge-local Lemma-5.8
data remain at the caller boundary. -/
theorem exists_treeCopy_of_richTargetCleanedRoots
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (hdisjoint : Disjoint E0.selected Mb.selected)
    {Target : Type x} [Fintype Target] [DecidableEq Target]
    (rootRho : ℝ)
    (targets : Fin P.numParts → Finset Target)
    (targetWhole targetRaw : Target → Finset Bv)
    (rootLoss : Fin P.numParts → ℕ)
    (hrootBad : ∀ q,
      #(rootTargetBad G rootRho
        (rootWhole Pcluster Gdegree threshold quota R miss Q P)
        (rootRaw Pcluster Gdegree threshold quota R miss Q P)
        targets targetWhole targetRaw q) ≤ rootLoss q)
    (hrootBudget : ∀ q, P.numParts + rootLoss q ≤ quota)
    (hrootLink : ∀ j (hj : j.val ≠ 0)
      (_hroot : P.parent j hj = P.roots (P.parentPart j hj))
      , ∃ t ∈ targets (P.parentPart j hj),
          targetRaw t =
            rootRaw Pcluster Gdegree threshold quota R miss Q P j ∧
          (P.numParts : ℝ) + rootLoss j ≤
            (G.edgeDensity
                (rootWhole Pcluster Gdegree threshold quota R miss Q P
                  (P.parentPart j hj))
                (targetWhole t) - rootRho) * #(targetRaw t))
    (rho density : PhysicalIndex Q sourceDensity E0 Mb → ℝ)
    (hdata : ∀ rootImage : Fin P.numParts → Bv,
      (∀ q, rootImage q ∈ rootCandidate G rootRho
        (rootWhole Pcluster Gdegree threshold quota R miss Q P)
        (rootRaw Pcluster Gdegree threshold quota R miss Q P)
        targets targetWhole targetRaw q) →
      CutEdgeData P G G rootImage
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
        (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
        rho density) :
    Nonempty (T.Copy G) := by
  refine exists_treeCopy_of_targetCleanedRoots_and_cutEdgeDataWithLinks
    P G G le_rfl
    rootRho
    (rootWhole Pcluster Gdegree threshold quota R miss Q P)
    (rootRaw Pcluster Gdegree threshold quota R miss Q P)
    targets targetWhole targetRaw rootLoss hrootBad ?_ hrootLink
    (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A))
    (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
    (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
    rho density ?_ ?_ ?_ ?_ ?_
  · intro q
    simpa only [card_rootRaw] using hrootBudget q
  · exact endpoint_subset_whole
      (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
  · exact whole_disjoint
      (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      hdisjoint
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

end Erdos547b.ZhaoClaim615RichDynamicRootApplication

#print axioms Erdos547b.ZhaoClaim615RichDynamicRootApplication.exists_treeCopy_of_richTargetCleanedRoots
