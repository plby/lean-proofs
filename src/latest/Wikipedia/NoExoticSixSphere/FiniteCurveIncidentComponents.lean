import Wikipedia.NoExoticSixSphere.CurveBranchComponentComparison

/-!
# At most two actual components can be incident to a cut

Edges are the actual component subsets of the original space, so distinct
components with the same two endpoints are not identified. Each incident
component contains a nonempty local branch. Choosing one actual point from
each available branch therefore bounds the incident set by two components.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.CurveDecomposition

variable {X : Type*} [TopologicalSpace X]

def componentSet (S : Set X) : Set (Set X) := range (cutComponent S)

def incidentComponents (S : Set X) (v : X) : Set (Set X) :=
  {C | C ∈ componentSet S ∧ v ∈ closure C}

theorem IntervalNeighborhood.incident_components_subset_pair
    (d : IntervalNeighborhood X) (v : X) (hv : v ∈ d.openSet) (S : Set X) (hvS : v ∈ S)
    (hcut : ∀ y ∈ d.closedSet, y ∈ S → y = v)
    (hzero : ∀ y ∈ d.chart.source, (d.chart y).val = 0 → y ∈ S) :
    ∃ p q : {x : X // x ∉ S},
      incidentComponents S v ⊆ {cutComponent S p, cutComponent S q} := by
  classical
  obtain ⟨r, hr⟩ := (d.isConnected_rightBranch v hv).nonempty
  let q : {x : X // x ∉ S} := ⟨r, d.rightBranch_subset_compl v hv S hcut hr⟩
  by_cases hl : (d.leftBranch v).Nonempty
  · obtain ⟨l, hl⟩ := hl
    let p : {x : X // x ∉ S} := ⟨l, d.leftBranch_subset_compl v hv S hcut hl⟩
    refine ⟨p, q, ?_⟩
    rintro C ⟨⟨x, rfl⟩, hx⟩
    rcases d.incident_component_contains_branch v hv S hvS hcut hzero x hx with h | h
    · exact Or.inl (cutComponent_eq_of_mem S x p (h.2 hl)).symm
    · exact Or.inr (cutComponent_eq_of_mem S x q (h.2 hr)).symm
  · refine ⟨q, q, ?_⟩
    rintro C ⟨⟨x, rfl⟩, hx⟩
    rcases d.incident_component_contains_branch v hv S hvS hcut hzero x hx with h | h
    · exact False.elim (hl h.1)
    · exact Or.inl (cutComponent_eq_of_mem S x q (h.2 hr)).symm

theorem IntervalNeighborhood.finite_incidentComponents
    (d : IntervalNeighborhood X) (v : X) (hv : v ∈ d.openSet) (S : Set X) (hvS : v ∈ S)
    (hcut : ∀ y ∈ d.closedSet, y ∈ S → y = v)
    (hzero : ∀ y ∈ d.chart.source, (d.chart y).val = 0 → y ∈ S) :
    (incidentComponents S v).Finite := by
  obtain ⟨p, q, hpq⟩ := d.incident_components_subset_pair v hv S hvS hcut hzero
  exact ((finite_singleton (cutComponent S q)).insert (cutComponent S p)).subset hpq

end NoExoticSixSphere.CurveDecomposition
