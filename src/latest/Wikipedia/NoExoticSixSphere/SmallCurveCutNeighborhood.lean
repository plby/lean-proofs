import Wikipedia.NoExoticSixSphere.CurveIntervalNeighborhood

/-!
# Compact interval neighborhoods containing no other cuts

The target interval is chosen inside the preimage of a specified original
open neighborhood. Its entire compact inverse image stays there. Applying
this to the complement of the other finitely many cuts isolates one cut
without changing its original atlas chart.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.CurveDecomposition

open InvolutionQuotient HalfLineIntervals

variable {X : Type*} [TopologicalSpace X]

theorem exists_interval_neighborhood_within (e : OpenPartialHomeomorph X HalfLine)
    (x : X) (hx : x ∈ e.source) (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ d : IntervalNeighborhood X, d.chart = e ∧ x ∈ d.openSet ∧ d.closedSet ⊆ U := by
  have hW : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.symm.isOpen_inter_preimage hU
  have hxW : e x ∈ e.target ∩ e.symm ⁻¹' U := by
    refine ⟨e.map_source hx, ?_⟩
    change e.symm (e x) ∈ U
    simpa only [e.left_inv hx] using hxU
  obtain ⟨a, b, hab, hxI, hI⟩ := exists_interval_in_open hW (e x) hxW
  refine ⟨⟨e, a, b, hab, fun _ hz ↦ (hI hz).1⟩, rfl, ⟨hx, hxI⟩, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact (hI hz).2

theorem exists_interval_avoiding_other_cuts [T1Space X] (S : Set X) (hS : S.Finite)
    (e : OpenPartialHomeomorph X HalfLine) (x : X) (hx : x ∈ e.source) :
    ∃ d : IntervalNeighborhood X, d.chart = e ∧ x ∈ d.openSet ∧
      ∀ y ∈ d.closedSet, y ∈ S → y = x := by
  have hother : (S \ {x}).Finite := hS.sdiff
  have hopen : IsOpen (S \ {x})ᶜ := hother.isClosed.isOpen_compl
  have hxU : x ∈ (S \ {x})ᶜ := by
    rintro ⟨hs, hn⟩
    exact hn rfl
  obtain ⟨d, hde, hxd, hdU⟩ := exists_interval_neighborhood_within e x hx _ hopen hxU
  refine ⟨d, hde, hxd, ?_⟩
  intro y hy hyS
  by_contra hne
  exact hdU hy ⟨hyS, hne⟩

end NoExoticSixSphere.CurveDecomposition
