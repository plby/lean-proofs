import Mathlib.Topology.Separation.Hausdorff

/-!
# Control of coincidences near two compact sets

An open relation containing all coincidences on two compact sets also contains
all coincidences on sufficiently small open neighborhoods. Continuity is needed
only at the original compact sets, not globally for the two maps.
-/

open Set Filter Topology

namespace Wikipedia.SmoothSixDPoincare

variable {X Y M : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace M] [T2Space M]

/-- Thicken compact domains without introducing coincidences outside a given open relation. -/
theorem exists_open_neighborhoods_with_coincidences_in
    {K : Set X} {L : Set Y} (hK : IsCompact K) (hL : IsCompact L)
    {f : X → M} {g : Y → M}
    (hf : ∀ x ∈ K, ContinuousAt f x) (hg : ∀ y ∈ L, ContinuousAt g y)
    {O : Set (X × Y)} (hO : IsOpen O)
    (hcoinc : ∀ x ∈ K, ∀ y ∈ L, f x = g y → (x, y) ∈ O) :
    ∃ U : Set X, ∃ V : Set Y, IsOpen U ∧ IsOpen V ∧ K ⊆ U ∧ L ⊆ V ∧
      ∀ x ∈ U, ∀ y ∈ V, f x = g y → (x, y) ∈ O := by
  let R : Set (X × Y) := {p | f p.1 ≠ g p.2} ∪ O
  have hKR : K ×ˢ L ⊆ interior R := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    apply mem_interior_iff_mem_nhds.mpr
    by_cases hxy : f x = g y
    · exact mem_of_superset (hO.mem_nhds (hcoinc x hx y hy hxy))
        (fun _ hp => Or.inr hp)
    · have hfc : ContinuousAt (fun p : X × Y => f p.1) (x, y) :=
        (hf x hx).comp continuousAt_fst
      have hgc : ContinuousAt (fun p : X × Y => g p.2) (x, y) :=
        (hg y hy).comp continuousAt_snd
      have hne : ∀ᶠ p : X × Y in 𝓝 (x, y), f p.1 ≠ g p.2 :=
        (hfc.ne_iff_eventually_ne hgc).mp hxy
      exact mem_of_superset hne (fun _ hp => Or.inl hp)
  obtain ⟨U, V, hU, hV, hKU, hLV, hUV⟩ :=
    generalized_tube_lemma hK hL isOpen_interior hKR
  refine ⟨U, V, hU, hV, hKU, hLV, ?_⟩
  intro x hx y hy hxy
  exact (interior_subset (hUV ⟨hx, hy⟩)).resolve_left (fun hne => hne hxy)

end Wikipedia.SmoothSixDPoincare
