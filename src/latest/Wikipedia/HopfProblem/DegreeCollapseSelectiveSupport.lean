import Wikipedia.HopfProblem.DegreeCollapseSelectiveSheetMotion
import Mathlib.Topology.Separation.Regular

/-!
# Compact source support from separation of the two branches

If an ambient support sees only two disjoint open source patches, its
pullback to the closure of the selected patch lies strictly inside that
patch. This constructs the closed inner support needed by the selective
smooth-motion theorem; it is not an extra support certificate.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SelectiveSheet

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A target neighborhood contains the specified locus and sees no unselected source branch. -/
theorem exists_target_neighborhood_of_preimage_subset [CompactSpace X] [T2Space Y]
    {f : X → Y} (hf : Continuous f) {B : Set Y} {W : Set X}
    (hW : IsOpen W) (hB : f ⁻¹' B ⊆ W) :
    ∃ O : Set Y, IsOpen O ∧ B ⊆ O ∧ f ⁻¹' O ⊆ W := by
  let O : Set Y := (f '' Wᶜ)ᶜ
  have hO : IsOpen O := ((hW.isClosed_compl.isCompact).image hf).isClosed.isOpen_compl
  refine ⟨O, hO, ?_, ?_⟩
  · intro y hy
    rintro ⟨x, hx, hxy⟩
    apply hx
    apply hB
    change f x ∈ B
    rwa [hxy]
  · intro x hx
    by_contra hxW
    exact hx ⟨x, hxW, rfl⟩

/-- The actual selected source support has compact closure inside the selected open patch. -/
theorem selected_support_isCompact [T2Space Y] {f : X → Y} (hf : Continuous f)
    {U V : Set X} {K : Set Y} (hUc : IsCompact (closure U)) (hV : IsOpen V)
    (hUV : Disjoint U V) (hK : IsCompact K) (hpre : f ⁻¹' K ⊆ U ∪ V) :
    IsCompact (closure U ∩ f ⁻¹' K) ∧ closure U ∩ f ⁻¹' K ⊆ U := by
  refine ⟨hUc.inter_right (hK.isClosed.preimage hf), ?_⟩
  intro x hx
  rcases hpre hx.2 with hxU | hxV
  · exact hxU
  · exact ((Set.disjoint_left.mp (hUV.closure_left hV)) hx.1 hxV).elim

variable {E F H H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [ChartedSpace H X] [ChartedSpace H' Y] [T2Space X] [T2Space Y]

theorem exists_selective_endpoint_of_two_source_patches (f : C(X, Y))
    {A : ℝ × Y → Y} {U V : Set X} {K : Set Y}
    (hU : IsOpen U) (hUc : IsCompact (closure U)) (hV : IsOpen V)
    (hUV : Disjoint U V) (hK : IsCompact K) (hpre : f ⁻¹' K ⊆ U ∪ V)
    (hf : ContMDiff I J ∞ f) (hi : ∀ x, Injective (mfderiv I J f x))
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A) (hA0 : ∀ y, A (0, y) = y)
    (hslice : ∀ t, ∃ D : Diffeomorph J J Y Y ∞, ∀ y, A (t, y) = D y)
    (hfix : ∀ t y, y ∉ K → A (t, y) = y) :
    ∃ L : Set X, IsCompact L ∧ L ⊆ U ∧ ∃ g : C(X, Y),
      ContMDiff I J ∞ g ∧ f.Homotopic g ∧
      (∀ x, Injective (mfderiv I J g x)) ∧
      (∀ x, g x = family f A U (1, x)) ∧ (∀ x ∉ L, g x = f x) := by
  let L : Set X := closure U ∩ f ⁻¹' K
  obtain ⟨hL, hLU⟩ := selected_support_isCompact f.continuous hUc hV hUV hK hpre
  refine ⟨L, hL, hLU, ?_⟩
  apply exists_immersed_endpoint_homotopic f hU hL.isClosed hLU hf hi hA hA0 hslice
  intro t x hx hxL
  exact hfix t (f x) (fun hxK => hxL ⟨subset_closure hx, hxK⟩)

end Wikipedia.HopfProblem.DegreeCollapse.SelectiveSheet
