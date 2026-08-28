import Wikipedia.NoExoticSixSphere.FiniteCurveCuts
import Mathlib.Topology.Connected.Clopen

/-!
# Components of the cut curve stay inside an actual interval chart

Deleting the finite endpoint set makes every selected open chart region
clopen in the remaining space. Connected components therefore cannot leave
a region they meet. Their closures in the original space are compact and
remain inside that region's genuine chart source.
-/

open Set Function Topology

namespace NoExoticSixSphere.CurveDecomposition

variable {X ι : Type*} [TopologicalSpace X]

theorem isClopen_away_from_frontier (S U : Set X) (hU : IsOpen U)
    (hfr : frontier U ⊆ S) :
    IsClopen ((Subtype.val : {x : X // x ∉ S} → X) ⁻¹' U) := by
  have he : (Subtype.val : {x : X // x ∉ S} → X) ⁻¹' U = Subtype.val ⁻¹' closure U := by
    ext x
    constructor
    · exact fun hx ↦ subset_closure hx
    · intro hx
      by_contra hn
      apply x.property
      apply hfr
      rw [frontier, hU.interior_eq]
      exact ⟨hx, hn⟩
  refine ⟨?_, hU.preimage continuous_subtype_val⟩
  rw [he]
  exact isClosed_closure.preimage continuous_subtype_val

def cutComponent (S : Set X) (x : {x : X // x ∉ S}) : Set X :=
  Subtype.val '' connectedComponent x

theorem mem_cutComponent (S : Set X) (x : {x : X // x ∉ S}) : x.val ∈ cutComponent S x :=
  ⟨x, mem_connectedComponent, rfl⟩

theorem cutComponent_subset_compl (S : Set X) (x : {x : X // x ∉ S}) : cutComponent S x ⊆ Sᶜ := by
  rintro y ⟨z, hz, rfl⟩
  exact z.property

theorem isConnected_cutComponent (S : Set X) (x : {x : X // x ∉ S}) :
    IsConnected (cutComponent S x) :=
  isConnected_connectedComponent.image Subtype.val continuous_subtype_val.continuousOn

theorem cutComponent_subset_interval [T2Space X] (t : Finset ι)
    (N : ι → IntervalNeighborhood X) (hcov : univ ⊆ ⋃ i ∈ t, (N i).openSet)
    (x : {x : X // x ∉ cutSet t N}) :
    ∃ i ∈ t, cutComponent (cutSet t N) x ⊆ (N i).openSet := by
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcov (mem_univ x.val))
  have hcl := isClopen_away_from_frontier (cutSet t N) (N i).openSet
    (N i).isOpen_openSet (frontier_subset_cutSet t N hi)
  refine ⟨i, hi, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact hcl.connectedComponent_subset hxi hz

theorem compact_closure_cutComponent [T2Space X] (t : Finset ι)
    (N : ι → IntervalNeighborhood X) (hcov : univ ⊆ ⋃ i ∈ t, (N i).openSet)
    (x : {x : X // x ∉ cutSet t N}) :
    IsCompact (closure (cutComponent (cutSet t N) x)) ∧
      ∃ i ∈ t, closure (cutComponent (cutSet t N) x) ⊆ (N i).closedSet := by
  obtain ⟨i, hi, hc⟩ := cutComponent_subset_interval t N hcov x
  have hs : closure (cutComponent (cutSet t N) x) ⊆ (N i).closedSet := by
    rw [← (N i).closure_openSet]
    exact closure_mono hc
  exact ⟨(N i).isCompact_closedSet.of_isClosed_subset isClosed_closure hs, i, hi, hs⟩

end NoExoticSixSphere.CurveDecomposition
