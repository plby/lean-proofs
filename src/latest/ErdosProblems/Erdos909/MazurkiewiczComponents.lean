/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Topology.Separation.Regular

open Set Topology

namespace Erdos909.MazurkiewiczComponents

universe u

variable {X : Type u} [TopologicalSpace X]

/-- In a compact Hausdorff space, points in distinct connected components
are separated by a clopen set. -/
theorem exists_isClopen_of_not_mem_connectedComponent
    [T2Space X] [CompactSpace X] {x y : X}
    (hy : y ∉ connectedComponent x) :
    ∃ A : Set X, IsClopen A ∧ x ∈ A ∧ y ∉ A := by
  rw [connectedComponent_eq_iInter_isClopen x, mem_iInter] at hy
  push Not at hy
  obtain ⟨A, hA⟩ := hy
  exact ⟨A, A.2.1, A.2.2, hA⟩

/-- If no compact connected subset of `Gᶜ` contains `x` and `y`, the two
points are separated by a clopen subset of the complement. -/
theorem exists_relative_isClopen_of_no_continuum
    [T2Space X] [CompactSpace X] {G : Set X} (hG : IsOpen G)
    {x y : X} (hx : x ∉ G) (hy : y ∉ G)
    (hno : ¬ ∃ K : Set X,
      IsCompact K ∧ IsConnected K ∧ K ⊆ Gᶜ ∧ x ∈ K ∧ y ∈ K) :
    ∃ A : Set ↑(Gᶜ), IsClopen A ∧ (⟨x, hx⟩ : ↑(Gᶜ)) ∈ A ∧
      (⟨y, hy⟩ : ↑(Gᶜ)) ∉ A := by
  let C : Set X := Gᶜ
  let xC : C := ⟨x, hx⟩
  let yC : C := ⟨y, hy⟩
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hG.isClosed_compl.isCompact
  have hycomp : yC ∉ connectedComponent xC := by
    intro hycomp
    apply hno
    refine ⟨((↑) : C → X) '' connectedComponent xC, ?_, ?_, ?_, ?_, ?_⟩
    · exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
    · exact isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn
    · rintro _ ⟨z, -, rfl⟩
      exact z.property
    · exact ⟨xC, mem_connectedComponent, rfl⟩
    · exact ⟨yC, hycomp, rfl⟩
  simpa [C, xC, yC] using
    (exists_isClopen_of_not_mem_connectedComponent (X := C) hycomp)

/-- The compact-component step in Mazurkiewicz's argument.  If `G` meets
every compact connected set containing `x` and `y`, a closed separator of
the two points is supported inside `G`. -/
theorem exists_open_frontier_subset_of_no_continuum
    [T2Space X] [CompactSpace X] {G : Set X} (hG : IsOpen G)
    {x y : X} (hx : x ∉ G) (hy : y ∉ G)
    (hno : ¬ ∃ K : Set X,
      IsCompact K ∧ IsConnected K ∧ K ⊆ Gᶜ ∧ x ∈ K ∧ y ∈ K) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ y ∉ closure U ∧ frontier U ⊆ G := by
  obtain ⟨A, hA, hxA, hyA⟩ :=
    exists_relative_isClopen_of_no_continuum hG hx hy hno
  let C : Set X := Gᶜ
  let A₀ : Set X := ((↑) : C → X) '' A
  let B₀ : Set X := ((↑) : C → X) '' Aᶜ
  have hC : IsClosed C := hG.isClosed_compl
  have hA₀ : IsClosed A₀ := hC.isClosedMap_subtype_val A hA.isClosed
  have hB₀ : IsClosed B₀ := hC.isClosedMap_subtype_val Aᶜ hA.compl.isClosed
  have hAB : Disjoint A₀ B₀ := by
    rw [Set.disjoint_left]
    rintro z ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    exact hb (Subtype.ext hab.symm ▸ ha)
  obtain ⟨U, V, hU, hV, hA₀U, hB₀V, hUV⟩ := normal_separation hA₀ hB₀ hAB
  refine ⟨U, hU, ?_, ?_, ?_⟩
  · exact hA₀U ⟨⟨x, hx⟩, hxA, rfl⟩
  · have hyV : y ∈ V := hB₀V ⟨⟨y, hy⟩, hyA, rfl⟩
    exact fun hycl ↦ Set.disjoint_left.mp (hUV.closure_left hV) hycl hyV
  · intro z hz
    by_contra hzG
    have hzC : (z : X) ∈ C := hzG
    by_cases hzA : (⟨z, hzC⟩ : C) ∈ A
    · have hzU : z ∈ U := hA₀U ⟨⟨z, hzC⟩, hzA, rfl⟩
      exact Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hU) hz hzU
    · have hzV : z ∈ V := hB₀V ⟨⟨z, hzC⟩, hzA, rfl⟩
      exact Set.disjoint_left.mp (hUV.frontier_left hV) hz hzV

/-- Family-cover version of the compact-component separator. -/
theorem exists_closed_separator_subset_iUnion_of_no_continuum
    [T2Space X] [CompactSpace X] {I : Type*} {W : I → Set X}
    (hW : ∀ i, IsOpen (W i)) {x y : X}
    (hx : x ∉ ⋃ i, W i) (hy : y ∉ ⋃ i, W i)
    (hno : ¬ ∃ K : Set X, IsCompact K ∧ IsConnected K ∧
      K ⊆ (⋃ i, W i)ᶜ ∧ x ∈ K ∧ y ∈ K) :
    ∃ S U : Set X, IsClosed S ∧ IsOpen U ∧ x ∈ U ∧
      y ∉ closure U ∧ S = frontier U ∧ S ⊆ ⋃ i, W i := by
  obtain ⟨U, hU, hxU, hyU, hfront⟩ :=
    exists_open_frontier_subset_of_no_continuum (isOpen_iUnion hW) hx hy hno
  exact ⟨frontier U, U, isClosed_frontier, hU, hxU, hyU, rfl, hfront⟩

/-- Explicit disjoint-open decomposition of the separator complement. -/
theorem exists_closed_separator_decomposition_of_no_continuum
    [T2Space X] [CompactSpace X] {G : Set X} (hG : IsOpen G)
    {x y : X} (hx : x ∉ G) (hy : y ∉ G)
    (hno : ¬ ∃ K : Set X,
      IsCompact K ∧ IsConnected K ∧ K ⊆ Gᶜ ∧ x ∈ K ∧ y ∈ K) :
    ∃ S P Q : Set X, IsClosed S ∧ IsOpen P ∧ IsOpen Q ∧ Disjoint P Q ∧
      Sᶜ = P ∪ Q ∧ x ∈ P ∧ y ∈ Q ∧ S ⊆ G := by
  obtain ⟨U, hU, hxU, hyU, hfront⟩ :=
    exists_open_frontier_subset_of_no_continuum hG hx hy hno
  refine ⟨frontier U, U, (closure U)ᶜ, isClosed_frontier, hU,
    isClosed_closure.isOpen_compl, ?_, ?_, hxU, hyU, hfront⟩
  · exact Set.disjoint_left.mpr fun _ hzU hzclosure ↦ hzclosure (subset_closure hzU)
  · rw [compl_frontier_eq_union_interior, hU.interior_eq, interior_compl]

/-- Indexed-family form of the explicit separator decomposition. -/
theorem exists_closed_separator_decomposition_subset_iUnion_of_no_continuum
    [T2Space X] [CompactSpace X] {I : Type*} {W : I → Set X}
    (hW : ∀ i, IsOpen (W i)) {x y : X}
    (hx : x ∉ ⋃ i, W i) (hy : y ∉ ⋃ i, W i)
    (hno : ¬ ∃ K : Set X, IsCompact K ∧ IsConnected K ∧
      K ⊆ (⋃ i, W i)ᶜ ∧ x ∈ K ∧ y ∈ K) :
    ∃ S P Q : Set X, IsClosed S ∧ IsOpen P ∧ IsOpen Q ∧ Disjoint P Q ∧
      Sᶜ = P ∪ Q ∧ x ∈ P ∧ y ∈ Q ∧ S ⊆ ⋃ i, W i := by
  exact exists_closed_separator_decomposition_of_no_continuum
    (isOpen_iUnion hW) hx hy hno

end Erdos909.MazurkiewiczComponents
