/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichPhysicalMatching
import ErdosProblems.Erdos547b.Claim615RichCoordinatePairFacts

/-!
# Dynamic matching endpoint layout for Zhao Claim 6.15

This is the host-side companion to `Claim615RichPhysicalMatching`.  Every
canonical physical index is interpreted as the two padded clusters of its
literal Claim-6.7 matching edge.  The permanent root reserves are deleted
from the live endpoint sets.  Matching endpoint injectivity supplies all
same-edge and cross-edge disjointness required by the cut-aware dynamic
Lemma-5.8 backend.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim615RichDynamicHostLayout

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoSection6Dichotomy
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichPhysicalEdgeFamilies
open Erdos547b.ZhaoClaim615RichPhysicalMatching
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts

universe v w

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

/-- The full padded cluster at one physical matching endpoint. -/
def whole (e : PhysicalIndex Q sourceDensity E0 Mb) (c : Fin 2) : Finset Bv :=
  padCluster (clusterVertices Pcluster)
    (matchingEdgeEndpoint (indexedPhysicalEdge Q sourceDensity E0 Mb e).1 c)

/-- The permanently available endpoint after deleting the two root
reserves.  Later dynamic recursion removes its own earlier images and
cut-parent bad sets from this set. -/
def endpoint (e : PhysicalIndex Q sourceDensity E0 Mb) (c : Fin 2) :
    Finset Bv :=
  whole (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb) e c \
    (Q.A₀ ∪ Q.B₀)

local notation "physicalWhole" =>
  whole (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)

local notation "physicalEndpoint" =>
  endpoint (Pcluster := Pcluster) (Gdegree := Gdegree)
    (threshold := threshold) (quota := quota) (R := R) (miss := miss)
    (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)

theorem endpoint_subset_whole
    (e : PhysicalIndex Q sourceDensity E0 Mb) (c : Fin 2) :
    physicalEndpoint e c ⊆ physicalWhole e c :=
  Finset.sdiff_subset

/-- Permanent deletion of the two distinguished root reservoirs costs at
most `2 * quota` vertices on every physical endpoint. -/
theorem card_whole_sdiff_endpoint_le_two_mul_quota
    (e : PhysicalIndex Q sourceDensity E0 Mb) (c : Fin 2) :
    #(physicalWhole e c \ physicalEndpoint e c) ≤ 2 * quota := by
  have hsub : physicalWhole e c \ physicalEndpoint e c ⊆ Q.A₀ ∪ Q.B₀ := by
    intro z hz
    have hz' := Finset.mem_sdiff.mp hz
    by_contra hreserve
    apply hz'.2
    exact Finset.mem_sdiff.mpr ⟨hz'.1, hreserve⟩
  calc
    #(physicalWhole e c \ physicalEndpoint e c) ≤ #(Q.A₀ ∪ Q.B₀) :=
      Finset.card_le_card hsub
    _ ≤ #Q.A₀ + #Q.B₀ := Finset.card_union_le _ _
    _ = 2 * quota := by rw [Q.A₀_card, Q.B₀_card]; omega

private theorem matchingEndpoint_injective :
    Function.Injective (fun ec : MatchingEdge Q.claim67.M × Fin 2 ↦
      matchingEdgeEndpoint ec.1.1 ec.2) := by
  rintro ⟨e, c⟩ ⟨f, d⟩ hendpoint
  let flip : Fin 2 → Fin 2 := fun q ↦ if q = 0 then 1 else 0
  have horiented (g : MatchingEdge Q.claim67.M) (q : Fin 2) :
      orientedEndpoint Q.claim67.M ∅ g (flip q) =
        matchingEdgeEndpoint g.1 q := by
    fin_cases q <;>
      simp [flip, orientedEndpoint, matchingEdgeEndpoint]
  have hpair : (e, flip c) = (f, flip d) := by
    apply orientedEndpoint_injective Q.claim67.M Q.claim67.isMatching
      (∅ : Finset (EvenPadding I))
    change orientedEndpoint Q.claim67.M ∅ e (flip c) =
      orientedEndpoint Q.claim67.M ∅ f (flip d)
    simpa only [horiented] using hendpoint
  have hedge : e = f := congrArg Prod.fst hpair
  subst f
  have hside : c = d := by
    have hflip := congrArg Prod.snd hpair
    fin_cases c <;> fin_cases d <;> simp [flip] at hflip ⊢
  subst d
  rfl

/-- Distinct endpoint occurrences of the indexed physical family have
distinct padded reduced vertices. -/
theorem indexedEndpoint_injective
    (hdisjoint : Disjoint E0.selected Mb.selected) :
    Function.Injective (fun ec :
      PhysicalIndex Q sourceDensity E0 Mb × Fin 2 ↦
        matchingEdgeEndpoint
          (indexedPhysicalEdge Q sourceDensity E0 Mb ec.1).1 ec.2) := by
  rintro ⟨e, c⟩ ⟨f, d⟩ h
  have hp :
      (indexedPhysicalEdge Q sourceDensity E0 Mb e, c) =
        (indexedPhysicalEdge Q sourceDensity E0 Mb f, d) := by
    apply matchingEndpoint_injective
      (Pcluster := Pcluster) (Gdegree := Gdegree)
      (threshold := threshold) (quota := quota) (R := R) (miss := miss)
      (Q := Q)
    exact h
  have hef : indexedPhysicalEdge Q sourceDensity E0 Mb e =
      indexedPhysicalEdge Q sourceDensity E0 Mb f := congrArg Prod.fst hp
  have heq : e = f :=
    indexedPhysicalEdge_injective Q sourceDensity E0 Mb hdisjoint hef
  subst f
  have hcd : c = d := congrArg Prod.snd hp
  subst d
  rfl

/-- The two clusters of one indexed matching edge are disjoint. -/
theorem whole_disjoint
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (e : PhysicalIndex Q sourceDensity E0 Mb) :
    Disjoint (physicalWhole e 0) (physicalWhole e 1) := by
  have hvertex : matchingEdgeEndpoint
        (indexedPhysicalEdge Q sourceDensity E0 Mb e).1 0 ≠
      matchingEdgeEndpoint
        (indexedPhysicalEdge Q sourceDensity E0 Mb e).1 1 := by
    intro h
    have hp : (e, (0 : Fin 2)) = (e, (1 : Fin 2)) := by
      apply indexedEndpoint_injective
        (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        hdisjoint
      exact h
    have hside : (0 : Fin 2) = 1 := congrArg Prod.snd hp
    omega
  simpa only [whole, clusterVertices_padAssignment] using
    clusterVertices_disjoint (padAssignment Pcluster) hvertex

/-- Endpoint supports of two different physical indices are disjoint on
every choice of sides. -/
theorem endpoint_disjoint_of_ne
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (e f : PhysicalIndex Q sourceDensity E0 Mb) (hef : e ≠ f)
    (c d : Fin 2) :
    Disjoint (physicalEndpoint e c) (physicalEndpoint f d) := by
  have hvertex : matchingEdgeEndpoint
        (indexedPhysicalEdge Q sourceDensity E0 Mb e).1 c ≠
      matchingEdgeEndpoint
        (indexedPhysicalEdge Q sourceDensity E0 Mb f).1 d := by
    intro h
    have hp : (e, c) = (f, d) := by
      apply indexedEndpoint_injective
        (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        hdisjoint
      exact h
    exact hef (congrArg Prod.fst hp)
  have hwhole : Disjoint
      (physicalWhole e c) (physicalWhole f d) := by
    simpa only [whole, clusterVertices_padAssignment] using
      clusterVertices_disjoint (padAssignment Pcluster) hvertex
  exact hwhole.mono Finset.sdiff_subset Finset.sdiff_subset

/-- The exact cross-fiber support disjointness expected by matching
assembly. -/
theorem endpointSupport_disjoint
    (hdisjoint : Disjoint E0.selected Mb.selected)
    (e f : PhysicalIndex Q sourceDensity E0 Mb) (hef : e ≠ f) :
    Disjoint
      (physicalEndpoint e 0 ∪ physicalEndpoint e 1)
      (physicalEndpoint f 0 ∪ physicalEndpoint f 1) := by
  rw [Finset.disjoint_left]
  intro z hze hzf
  rcases Finset.mem_union.mp hze with hze | hze <;>
    rcases Finset.mem_union.mp hzf with hzf | hzf
  · exact Finset.disjoint_left.mp
      (endpoint_disjoint_of_ne
        (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        hdisjoint e f hef 0 0) hze hzf
  · exact Finset.disjoint_left.mp
      (endpoint_disjoint_of_ne
        (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        hdisjoint e f hef 0 1) hze hzf
  · exact Finset.disjoint_left.mp
      (endpoint_disjoint_of_ne
        (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        hdisjoint e f hef 1 0) hze hzf
  · exact Finset.disjoint_left.mp
      (endpoint_disjoint_of_ne
        (Pcluster := Pcluster) (Gdegree := Gdegree)
        (threshold := threshold) (quota := quota) (R := R) (miss := miss)
        (Q := Q) (sourceDensity := sourceDensity) (E0 := E0) (Mb := Mb)
        hdisjoint e f hef 1 1) hze hzf

/-- Every physical edge supplies the regular pair represented by its two
whole endpoint clusters. -/
theorem whole_pair
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (e : PhysicalIndex Q sourceDensity E0 Mb) :
    G.IsUniform rho (physicalWhole e 0) (physicalWhole e 1) ∧
      density ≤ G.edgeDensity
        (physicalWhole e 0) (physicalWhole e 1) := by
  have hadj := matchingEdgeEndpoint_adj Q.claim67.M
    (indexedPhysicalEdge Q sourceDensity E0 Mb e).1
    (indexedPhysicalEdge Q sourceDensity E0 Mb e).2
  simpa only [whole] using H.pair_of_adj _ _ hadj

end Erdos547b.ZhaoClaim615RichDynamicHostLayout

#print axioms Erdos547b.ZhaoClaim615RichDynamicHostLayout.indexedEndpoint_injective
#print axioms Erdos547b.ZhaoClaim615RichDynamicHostLayout.whole_disjoint
#print axioms Erdos547b.ZhaoClaim615RichDynamicHostLayout.endpointSupport_disjoint
#print axioms Erdos547b.ZhaoClaim615RichDynamicHostLayout.whole_pair
