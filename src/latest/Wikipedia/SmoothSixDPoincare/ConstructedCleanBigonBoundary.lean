import Wikipedia.SmoothSixDPoincare.SmoothBigonBoundary
import Wikipedia.SmoothSixDPoincare.BigonBoundaryImmersion
import Wikipedia.SmoothSixDPoincare.BigonBoundaryClean

/-!
# A constructed clean compact neighborhood of the entire native bigon boundary

Starting with the actual shared-corner strips and their checked overlap
control, construct a compact closed boundary neighborhood whose image is a
closed embedding, whose native derivative is injective, and whose interior
bigon points avoid both full sheets. The full strip germs are retained along
both arcs. Extension to the disk interior and Whitney framing remain separate.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

open WhitneyPairModel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- Actual clean boundary-neighborhood data, including the original strip germs. -/
structure CleanBigonBoundary (S T : Set M) (a b : ℝ → M)
    (k l : (ℝ × ℝ) → M) (h : ℝ) where
  height_pos : 0 < h
  map : (ℝ × ℝ) → M
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  smooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ map domain
  injective : InjOn map domain
  derivative_injective : ∀ p ∈ domain, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) map p)
  interior_avoids : ∀ p ∈ domain ∩ interior (bigon h), map p ∉ S ∪ T
  closed_neighborhood : Set (ℝ × ℝ)
  compact_neighborhood : IsCompact closed_neighborhood
  closed_closed_neighborhood : IsClosed closed_neighborhood
  boundary_covered : frontier (bigon h) ⊆ interior closed_neighborhood
  neighborhood_subset : closed_neighborhood ⊆ domain
  closed_embedding : IsClosedEmbedding (fun p : closed_neighborhood => map p)
  clean : ∀ p ∈ bigon h ∩ closed_neighborhood, p ∉ frontier (bigon h) → map p ∉ S ∪ T
  lower : ∀ t ∈ Icc (0 : ℝ) 1, map (2 * t - 1, 0) = a t
  upper : ∀ t ∈ Icc (0 : ℝ) 1, map (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t
  lower_germ : ∀ t ∈ Icc (0 : ℝ) 1,
    map =ᶠ[𝓝 (2 * t - 1, 0)] k ∘ lowerStripCoordinates h
  upper_germ : ∀ t ∈ Icc (0 : ℝ) 1,
    map =ᶠ[𝓝 (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))] l ∘ upperStripCoordinates h

/-- Construct the full clean closed boundary neighborhood,
retaining the actual arc and strip germs. -/
theorem exists_clean_bigon_boundary_neighborhood {h : ℝ} (hh : 0 < h)
    {S T : Set M} {a b a₀ b₀ a₁ b₁ : ℝ → M}
    (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁)
    (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map)
    (hover : ∀ p ∈ k.domain, ∀ q ∈ l.domain, k.map p = l.map q →
      p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap) :
    ∃ f : (ℝ × ℝ) → M, ∃ W : Set (ℝ × ℝ), IsOpen W ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f W ∧ InjOn f W ∧
      (∀ p ∈ W, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p)) ∧
      (∀ p ∈ W ∩ interior (bigon h), f p ∉ S ∪ T) ∧
      ∃ C : Set (ℝ × ℝ), IsCompact C ∧ IsClosed C ∧ frontier (bigon h) ⊆ interior C ∧
        C ⊆ W ∧ IsClosedEmbedding (fun p : C => f p) ∧
        (∀ p ∈ bigon h ∩ C, p ∉ frontier (bigon h) → f p ∉ S ∪ T) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, f (2 * t - 1, 0) = a t) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, f (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          f =ᶠ[𝓝 (2 * t - 1, 0)] k.map ∘ lowerStripCoordinates h) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          f =ᶠ[𝓝 (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))]
            l.map ∘ upperStripCoordinates h) := by
  obtain ⟨U, V, hU, hV, hfront, hlowU, huppV, hmapU, hmapV, f, hf, hflo, hfhi,
      hlow, hupp⟩ := exists_smooth_bigon_boundary_neighborhood hh c₀ c₁ k l
  obtain ⟨W, hW, hfrontW, hWUV, hinj, hi⟩ :=
    exists_embedded_bigon_boundary_neighborhood hh k l hover hU hV hfront
      hlowU huppV hmapU hmapV hf hflo hfhi
  have hclean : ∀ p ∈ W ∩ interior (bigon h), f p ∉ S ∪ T := fun p hp =>
    bigon_boundary_map_avoids_sheets hh k l hmapU hmapV hflo hfhi (hWUV hp.1) hp.2
  have hcompact : IsCompact (frontier (bigon h)) :=
    (isCompact_bigon hh).of_isClosed_subset isClosed_frontier
      (fun p hp => ((mem_frontier_bigon_iff h p).mp hp).1)
  obtain ⟨C, hC, hCclosed, hfrontC, hCW⟩ := exists_compact_closed_between hcompact hW hfrontW
  have hemb : IsClosedEmbedding (fun p : C => f p) := by
    let : CompactSpace C := isCompact_iff_compactSpace.mp hC
    have hc : Continuous (fun p : C => f p) :=
      continuousOn_iff_continuous_domRestrict.mp (hf.continuousOn.mono (hCW.trans hWUV))
    apply hc.isClosedEmbedding
    intro p q hpq
    exact Subtype.ext (hinj (hCW p.property) (hCW q.property) hpq)
  refine ⟨f, W, hW, hf.mono hWUV, hinj, hi, hclean,
    C, hC, hCclosed, hfrontC, hCW, hemb, ?_, hlow, hupp, ?_, ?_⟩
  · intro p hp hnot
    apply hclean p ⟨hCW hp.2, ?_⟩
    by_contra hni
    apply hnot
    rw [frontier, (isClosed_bigon h).closure_eq]
    exact ⟨hp.1, hni⟩
  · intro t ht
    exact mem_of_superset (hU.mem_nhds (hlowU ht)) (fun _ hp => hflo hp)
  · intro t ht
    exact mem_of_superset (hV.mem_nhds (huppV ht)) (fun _ hp => hfhi hp)

/-- Package the fully constructed clean neighborhood without losing its actual maps or germs. -/
theorem nonempty_cleanBigonBoundary {h : ℝ} (hh : 0 < h)
    {S T : Set M} {a b a₀ b₀ a₁ b₁ : ℝ → M}
    (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁)
    (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map)
    (hover : ∀ p ∈ k.domain, ∀ q ∈ l.domain, k.map p = l.map q →
      p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap) :
    Nonempty (CleanBigonBoundary (E := E) S T a b k.map l.map h) := by
  obtain ⟨f, W, hW, hf, hinj, hi, havoid, C, hC, hCc, hfront, hCW, hemb, hclean,
      hlow, hupp, hlowg, huppg⟩ := exists_clean_bigon_boundary_neighborhood hh c₀ c₁ k l hover
  exact ⟨{
    height_pos := hh
    map := f
    domain := W
    open_domain := hW
    smooth := hf
    injective := hinj
    derivative_injective := hi
    interior_avoids := havoid
    closed_neighborhood := C
    compact_neighborhood := hC
    closed_closed_neighborhood := hCc
    boundary_covered := hfront
    neighborhood_subset := hCW
    closed_embedding := hemb
    clean := hclean
    lower := hlow
    upper := hupp
    lower_germ := hlowg
    upper_germ := huppg }⟩

end Wikipedia.SmoothSixDPoincare
