import Wikipedia.SmoothSixDPoincare.SmoothCleanBigonBoundary
import Wikipedia.SmoothSixDPoincare.CleanWhitneyBigon
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# A clean embedded tubular bigon avoiding both actual compact sheets

The two native sheets share a finite-dimensional model. Their disjoint union
is an actual compact smooth obstacle, with image exactly the union of their
full images. The relative filling fixes the constructed clean neighborhood,
retains both whole strip germs, and gives a genuine positive-radius tube.
The normal frame is not asserted to be the required Whitney boundary frame.
-/

noncomputable section

open Set Function Filter Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

open WhitneyPairModel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- An actual clean embedded bigon and its tubular chart, with the complete boundary strip germs. -/
structure TubularBigon (S T : Set M) (a b : ℝ → M) (k l : (ℝ × ℝ) → M) (h : ℝ)
    (n : ℕ := 4) where
  height_pos : 0 < h
  map : C(ℝ × ℝ, M)
  smooth : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ map
  closed_embedding : IsClosedEmbedding (fun p : bigon h => map p)
  derivative_injective : ∀ p ∈ bigon h, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) map p)
  interior_avoids : ∀ p ∈ interior (bigon h), map p ∉ S ∪ T
  lower : ∀ t ∈ Icc (0 : ℝ) 1, map (2 * t - 1, 0) = a t
  upper : ∀ t ∈ Icc (0 : ℝ) 1, map (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t
  lower_germ : ∀ t ∈ Icc (0 : ℝ) 1,
    map =ᶠ[𝓝 (2 * t - 1, 0)] k ∘ lowerStripCoordinates h
  upper_germ : ∀ t ∈ Icc (0 : ℝ) 1,
    map =ᶠ[𝓝 (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))] l ∘ upperStripCoordinates h
  radius : ℝ
  radius_pos : 0 < radius
  chart : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
    ((ℝ × ℝ) × EuclideanSpace ℝ (Fin n)) M ∞
  source_contains : bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = map p

variable {D N P : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N] [CompactSpace N]
  [TopologicalSpace P] [ChartedSpace D P] [IsManifold 𝓘(ℝ, D) ∞ P] [CompactSpace P]

/-- Construct the entire embedded tubular bigon, simultaneously avoiding both full sheet images. -/
theorem nonempty_tubularBigon_of_smoothCleanBoundary {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ G)
    (hdim : Module.finrank ℝ E = 6) (hobs : Module.finrank ℝ D ≤ 3)
    {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : SmoothCleanBigonBoundary (E := E) (range F) (range G) a b k l h) :
    Nonempty (TubularBigon (E := E) (range F) (range G) a b k l h) := by
  let obstacle : C(N ⊕ P, M) := ⟨Sum.elim F G, hF.continuous.sumElim hG.continuous⟩
  have hobsSmooth : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ obstacle := hF.sumElim hG
  have hobsRange : range obstacle = range F ∪ range G := by
    ext z
    constructor
    · rintro ⟨x | y, heq⟩
      · exact Or.inl ⟨x, heq⟩
      · exact Or.inr ⟨y, heq⟩
    · rintro (⟨x, heq⟩ | ⟨y, heq⟩)
      · exact ⟨Sum.inl x, heq⟩
      · exact ⟨Sum.inr y, heq⟩
  have hclean : ∀ p ∈ bigon h ∩ d.neighborhood,
      p ∉ frontier (bigon h) → d.map p ∉ range obstacle := by
    rw [hobsRange]
    exact d.clean
  obtain ⟨f, hf, hrel, hemb, hi, havoid, ε, hε, Φ, hsource, hzero, _⟩ :=
    exists_tubular_bigon_of_clean_neighborhood d.map obstacle d.smooth hobsSmooth
      hdim hobs d.height_pos d.closed_neighborhood d.boundary_covered
      (d.injective.mono inter_subset_right) (fun p hp => d.derivative_injective p hp.2) hclean
  have hfixed : ∀ p ∈ frontier (bigon h), f p = d.map p := fun p hp =>
    (hrel.fst_eq_snd (interior_subset (d.boundary_covered hp))).symm
  have hgerm : ∀ p ∈ frontier (bigon h), (f : (ℝ × ℝ) → M) =ᶠ[𝓝 p] d.map := by
    intro p hp
    filter_upwards [isOpen_interior.mem_nhds (d.boundary_covered hp)] with q hq
    exact (hrel.fst_eq_snd (interior_subset hq)).symm
  have hlow : ∀ t ∈ Icc (0 : ℝ) 1, (2 * t - 1, 0) ∈ frontier (bigon h) :=
    fun t ht => (mem_frontier_bigon_iff_exists_time d.height_pos _).mpr ⟨t, ht, Or.inl rfl⟩
  have hupp : ∀ t ∈ Icc (0 : ℝ) 1,
      (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ frontier (bigon h) :=
    fun t ht => (mem_frontier_bigon_iff_exists_time d.height_pos _).mpr ⟨t, ht, Or.inr rfl⟩
  refine ⟨{
    height_pos := d.height_pos
    map := f
    smooth := hf
    closed_embedding := hemb
    derivative_injective := hi
    interior_avoids := ?_
    lower := fun t ht => (hfixed _ (hlow t ht)).trans (d.lower t ht)
    upper := fun t ht => (hfixed _ (hupp t ht)).trans (d.upper t ht)
    lower_germ := fun t ht => (hgerm _ (hlow t ht)).trans (d.lower_germ t ht)
    upper_germ := fun t ht => (hgerm _ (hupp t ht)).trans (d.upper_germ t ht)
    radius := ε
    radius_pos := hε
    chart := Φ
    source_contains := hsource
    zero_section := hzero }⟩
  intro p hp
  rw [← hobsRange]
  exact havoid p hp

end Wikipedia.SmoothSixDPoincare
