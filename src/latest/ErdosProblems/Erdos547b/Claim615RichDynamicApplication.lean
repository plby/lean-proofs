/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichDynamicHostLayout
import ErdosProblems.Erdos547b.Lemma58FullCutTree

/-!
# Cut-aware dynamic application for Zhao Claim 6.15

This module fixes every structural input of the full dynamic Lemma-5.8
constructor to the concrete rich families selected for Claim 6.15.  In
particular, callers no longer provide an arbitrary matching index,
assignment, endpoint family, or disjointness proof.  The only edge-local
input left is genuine `CutEdgeLocalData`, whose two constructors are the
checked Parts-1/2 threshold realization and the owner-wise Part-3 Appendix
realization.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichDynamicApplication

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim615CoordinateSourceAllocation
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichDynamicHostLayout
open Erdos547b.ZhaoLemma58CutEdgeLocal
open Erdos547b.ZhaoLemma58CutForestReconstruction
open Erdos547b.ZhaoLemma58FullCutTree

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

/-- The concrete branch-to-physical-edge assignment. -/
abbrev richAssign :=
  assignedPhysicalIndex (Q := Q) (sourceDensity := sourceDensity)
    (E0 := E0) (Mb := Mb) (P := P) (S := S) (A := A)

/-- The concrete whole endpoint clusters. -/
abbrev richWhole :=
  whole (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)

/-- The concrete endpoints after permanent root-reserve deletion. -/
abbrev richEndpoint :=
  endpoint (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)

/-- One concrete edge-local datum at a fixed physical index. -/
abbrev RichCutEdgeDatum
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → Bv)
    (rho density : PhysicalIndex Q sourceDensity E0 Mb → ℝ)
    (e : PhysicalIndex Q sourceDensity E0 Mb) :=
  Nonempty (CutEdgeLocalData P
    (cutFiberForest P
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) e)
    G G
    (fun i ↦ rootImage (cutFiberOwner P
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) e i))
    (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb e)
    (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb e)
    (cutFiberOwner P
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A)) e)
    (cutParentBad P G rootImage
      (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb) e)
    (globalCutParentBad P G rootImage
      (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb) e)
    (rho e) (density e))

/-- Assemble the three tagged local families into the single edge-local
function expected by `Lemma58FullCutTree`. -/
theorem richCutEdgeData_of_families
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rootImage : Fin P.numParts → Bv)
    (rho density : PhysicalIndex Q sourceDensity E0 Mb → ℝ)
    (h0 : ∀ e : K0 Q sourceDensity E0,
      RichCutEdgeDatum Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb P S A G rootImage rho density
          (exceptionalIndex Q sourceDensity E0 Mb e))
    (h1 : ∀ e : K1 Q sourceDensity E0 Mb,
      RichCutEdgeDatum Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb P S A G rootImage rho density
          (remainingIndex Q sourceDensity E0 Mb e))
    (hb : ∀ e : Kb Q sourceDensity Mb,
      RichCutEdgeDatum Pcluster Gdegree threshold quota R miss Q sourceDensity
        E0 Mb P S A G rootImage rho density
          (reservedIndex Q sourceDensity E0 Mb e)) :
    CutEdgeData P G G rootImage
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A))
      (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
      (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
      rho density := by
  intro e
  let tagged :=
    (Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb)).symm e
  have htag : Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb) tagged = e :=
    (Fintype.equivFin (PhysicalEdge Q sourceDensity E0 Mb)).apply_symm_apply e
  rcases tagged with e0 | erest
  · have he : exceptionalIndex Q sourceDensity E0 Mb e0 = e := htag
    rw [← he]
    exact h0 e0
  · rcases erest with e1 | eb
    · have he : remainingIndex Q sourceDensity E0 Mb e1 = e := htag
      rw [← he]
      exact h1 e1
    · have he : reservedIndex Q sourceDensity E0 Mb eb = e := htag
      rw [← he]
      exact hb eb

/-- Specialize the complete cut-aware constructor to the literal rich
physical matching. -/
theorem exists_treeCopy_of_richCutEdgeData
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (rootImage : Fin P.numParts → Bv)
    (rho density : PhysicalIndex Q sourceDensity E0 Mb → ℝ)
    (hdata : CutEdgeData P G G rootImage
      (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        (P := P) (S := S) (A := A))
      (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
      (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
      rho density)
    (hrootInjective : Function.Injective rootImage)
    (hrootOutside : ∀ q e c,
      rootImage q ∉ richEndpoint Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb e c)
    (hrootCut : ∀ j (hj : j.val ≠ 0),
      P.parent j hj = P.roots (P.parentPart j hj) →
      G.Adj (rootImage j) (rootImage (P.parentPart j hj))) :
    Nonempty (T.Copy G) := by
  apply exists_treeCopy_of_cutEdgeLocalData P G G le_rfl rootImage
    (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A))
    (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
    (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
    rho density
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
  · exact hdata
  · exact hrootInjective
  · exact hrootOutside
  · exact hrootCut

/-- Root-candidate form.  Root injection and the root/root cut edges are
constructed internally by the checked online root-skeleton theorem. -/
theorem exists_treeCopy_of_richRootCandidates
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (candidate : Fin P.numParts → Finset Bv)
    (hcandidate : ∀ i, P.numParts ≤ #(candidate i))
    (hlink : ∀ j (hj : j.val ≠ 0)
      (_hroot : P.parent j hj = P.roots (P.parentPart j hj))
      z, z ∈ candidate (P.parentPart j hj) →
      P.numParts ≤ #((candidate j).filter (G.Adj z)))
    (rho density : PhysicalIndex Q sourceDensity E0 Mb → ℝ)
    (hrootOutside : ∀ q z, z ∈ candidate q → ∀ e c,
      z ∉ richEndpoint Pcluster Gdegree threshold quota R miss Q
        sourceDensity E0 Mb e c)
    (hdata : ∀ rootImage : Fin P.numParts → Bv,
      (∀ q, rootImage q ∈ candidate q) →
      CutEdgeData P G G rootImage
        (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
          (threshold := threshold) (quota := quota) (R := R) (miss := miss)
          (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
          (P := P) (S := S) (A := A))
        (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
        (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
        rho density) :
    Nonempty (T.Copy G) := by
  apply exists_treeCopy_of_rootCandidates_and_cutEdgeData P G G le_rfl
    candidate hcandidate hlink
    (richAssign (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
      (P := P) (S := S) (A := A))
    (richWhole Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
    (richEndpoint Pcluster Gdegree threshold quota R miss Q sourceDensity E0 Mb)
    rho density
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
  · exact hrootOutside
  · exact hdata

end Erdos547b.ZhaoClaim615RichDynamicApplication

#print axioms Erdos547b.ZhaoClaim615RichDynamicApplication.richCutEdgeData_of_families
#print axioms Erdos547b.ZhaoClaim615RichDynamicApplication.exists_treeCopy_of_richCutEdgeData
#print axioms Erdos547b.ZhaoClaim615RichDynamicApplication.exists_treeCopy_of_richRootCandidates
