import Wikipedia.NoExoticSixSphere.FiniteCurveIncidentComponents

/-!
# Exact one-branch and two-branch incidence at a cut

At chart-coordinate zero the incident component set is a singleton. At a
positive coordinate it consists of two distinct actual components, provided
the cut is not an ambient interior point of any component closure. The latter
condition is proved separately using the common boundary identification.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.CurveDecomposition

variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem IntervalNeighborhood.incident_components_eq_singleton
    (d : IntervalNeighborhood X) (v : X) (hv : v ∈ d.openSet) (S : Set X) (hvS : v ∈ S)
    (hcut : ∀ y ∈ d.closedSet, y ∈ S → y = v)
    (hzero : ∀ y ∈ d.chart.source, (d.chart y).val = 0 → y ∈ S)
    (hz : (d.chart v).val = 0) :
    ∃ q : {x : X // x ∉ S}, incidentComponents S v = {cutComponent S q} := by
  obtain ⟨r, hr⟩ := (d.isConnected_rightBranch v hv).nonempty
  let q : {x : X // x ∉ S} := ⟨r, d.rightBranch_subset_compl v hv S hcut hr⟩
  have hR : d.rightBranch v ⊆ cutComponent S q :=
    preconnected_subset_cutComponent S (d.rightBranch v)
      (d.isConnected_rightBranch v hv).isPreconnected (d.rightBranch_subset_compl v hv S hcut) q hr
  have hcl := closure_mono hR (d.center_mem_closure_rightBranch v hv)
  refine ⟨q, ?_⟩
  ext C
  constructor
  · rintro ⟨⟨x, rfl⟩, hx⟩
    rcases d.incident_component_contains_branch v hv S hvS hcut hzero x hx with h | h
    · rw [d.leftBranch_eq_empty v hz] at h
      exact False.elim (not_nonempty_empty h.1)
    · exact mem_singleton_iff.mpr (cutComponent_eq_of_mem S x q (h.2 hr)).symm
  · intro he
    rw [mem_singleton_iff] at he
    subst C
    exact ⟨⟨q, rfl⟩, hcl⟩

theorem IntervalNeighborhood.incident_components_eq_pair
    (d : IntervalNeighborhood X) (v : X) (hv : v ∈ d.openSet) (S : Set X) (hvS : v ∈ S)
    (hcut : ∀ y ∈ d.closedSet, y ∈ S → y = v)
    (hzero : ∀ y ∈ d.chart.source, (d.chart y).val = 0 → y ∈ S)
    (hpos : 0 < (d.chart v).val)
    (hno : ∀ x : {x : X // x ∉ S}, v ∉ interior (closure (cutComponent S x))) :
    ∃ p q : {x : X // x ∉ S}, cutComponent S p ≠ cutComponent S q ∧
      incidentComponents S v = {cutComponent S p, cutComponent S q} := by
  obtain ⟨l, hl⟩ := (d.isConnected_leftBranch v hv hpos).nonempty
  obtain ⟨r, hr⟩ := (d.isConnected_rightBranch v hv).nonempty
  let p : {x : X // x ∉ S} := ⟨l, d.leftBranch_subset_compl v hv S hcut hl⟩
  let q : {x : X // x ∉ S} := ⟨r, d.rightBranch_subset_compl v hv S hcut hr⟩
  have hL : d.leftBranch v ⊆ cutComponent S p :=
    preconnected_subset_cutComponent S (d.leftBranch v)
      (d.isPreconnected_leftBranch v hv) (d.leftBranch_subset_compl v hv S hcut) p hl
  have hR : d.rightBranch v ⊆ cutComponent S q :=
    preconnected_subset_cutComponent S (d.rightBranch v)
      (d.isConnected_rightBranch v hv).isPreconnected (d.rightBranch_subset_compl v hv S hcut) q hr
  have hclL := closure_mono hL (d.center_mem_closure_leftBranch v hv hpos)
  have hclR := closure_mono hR (d.center_mem_closure_rightBranch v hv)
  have hne : cutComponent S p ≠ cutComponent S q := by
    intro he
    have hR' : d.rightBranch v ⊆ cutComponent S p := by
      rw [he]
      exact hR
    have hU : d.openSet ⊆ closure (cutComponent S p) := by
      intro y hy
      by_cases hyv : y = v
      · exact hyv.symm ▸ hclL
      have hyB : y ∈ d.leftBranch v ∪ d.rightBranch v := by
        rw [← d.punctured_eq_branches v hv S hcut hzero]
        exact ⟨hy, hyv⟩
      exact hyB.elim (fun h ↦ subset_closure (hL h)) (fun h ↦ subset_closure (hR' h))
    exact hno p (interior_maximal hU d.isOpen_openSet hv)
  refine ⟨p, q, hne, ?_⟩
  ext C
  constructor
  · rintro ⟨⟨x, rfl⟩, hx⟩
    rcases d.incident_component_contains_branch v hv S hvS hcut hzero x hx with h | h
    · exact Or.inl (cutComponent_eq_of_mem S x p (h.2 hl)).symm
    · exact Or.inr (cutComponent_eq_of_mem S x q (h.2 hr)).symm
  · rintro (he | he)
    · subst C
      exact ⟨⟨p, rfl⟩, hclL⟩
    · have he' := mem_singleton_iff.mp he
      subst C
      exact ⟨⟨q, rfl⟩, hclR⟩

end NoExoticSixSphere.CurveDecomposition
