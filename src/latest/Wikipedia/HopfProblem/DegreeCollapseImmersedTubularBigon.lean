import Wikipedia.HopfProblem.DegreeCollapseSmoothBigonFromLoops
import Wikipedia.HopfProblem.DegreeCollapseImmersedBigonCleanNeighborhood
import Wikipedia.SmoothSixDPoincare.TwoSheetTubularBigon

/-!
# Embedded tubular bigons avoiding the entire original obstacle

Shrink the fixed clean boundary neighborhood using branch isolation and
apply relative general position to the original compact smooth obstacle.
The full bigon is embedded and immersive, its interior misses the entire
obstacle image, and it has an actual positive-radius normal tube. Both
original strip germs are retained. The tube is not yet asserted to carry
the required Whitney boundary framing.
-/

noncomputable section

open Set Function Filter Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open Wikipedia.SmoothSixDPoincare WhitneyPairModel

variable {E M F H Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold J ∞ Y]
  [CompactSpace Y] [LindelofSpace ((ℝ × ℝ) × Y)]

/-- An actual embedded tubular filling, clean against the whole original obstacle image. -/
theorem exists_tubularBigon_avoiding_whole_obstacle
    (g : C(Y, M)) (hg : ContMDiff J 𝓘(ℝ, E) ∞ g)
    (hdim : Module.finrank ℝ E = 6) (hobstacle : Module.finrank ℝ F ≤ 3)
    {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : SmoothCleanBigonBoundary (E := E) S T a b k l h)
    {O : Set M} (hO : IsOpen O)
    (haO : MapsTo a (Icc (0 : ℝ) 1) O) (hbO : MapsTo b (Icc (0 : ℝ) 1) O)
    (hcover : range g ∩ O ⊆ S ∪ T) (hS : S ⊆ range g) (hT : T ⊆ range g) :
    ∃ d' : TubularBigon (E := E) S T a b k l h,
      ∀ p ∈ interior (bigon h), d'.map p ∉ range g := by
  obtain ⟨C, _, hCc, hfrontC, hCD, _, hclean⟩ :=
    exists_whole_image_clean_boundary_neighborhood d hO haO hbO hcover
  obtain ⟨f, hf, hrel, hemb, hi, havoid, ε, hε, Φ, hsource, hzero, _⟩ :=
    exists_tubular_bigon_of_clean_neighborhood d.map g d.smooth hg hdim hobstacle
      d.height_pos hCc hfrontC (d.injective.mono (inter_subset_right.trans hCD))
      (fun p hp => d.derivative_injective p (hCD hp.2)) hclean
  have hfixed : ∀ p ∈ frontier (bigon h), f p = d.map p := fun p hp =>
    (hrel.fst_eq_snd (interior_subset (hfrontC hp))).symm
  have hgerm : ∀ p ∈ frontier (bigon h), (f : (ℝ × ℝ) → M) =ᶠ[𝓝 p] d.map := by
    intro p hp
    filter_upwards [isOpen_interior.mem_nhds (hfrontC hp)] with q hq
    exact (hrel.fst_eq_snd (interior_subset hq)).symm
  have hlow : ∀ t ∈ Icc (0 : ℝ) 1, (2 * t - 1, 0) ∈ frontier (bigon h) :=
    fun t ht => (mem_frontier_bigon_iff_exists_time d.height_pos _).mpr ⟨t, ht, Or.inl rfl⟩
  have hupp : ∀ t ∈ Icc (0 : ℝ) 1,
      (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ frontier (bigon h) :=
    fun t ht => (mem_frontier_bigon_iff_exists_time d.height_pos _).mpr ⟨t, ht, Or.inr rfl⟩
  let tube : TubularBigon (E := E) S T a b k l h := {
    height_pos := d.height_pos
    map := f
    smooth := hf
    closed_embedding := hemb
    derivative_injective := hi
    interior_avoids := fun p hp hmem => havoid p hp (hmem.elim (fun hs => hS hs) (fun ht => hT ht))
    lower := fun t ht => (hfixed _ (hlow t ht)).trans (d.lower t ht)
    upper := fun t ht => (hfixed _ (hupp t ht)).trans (d.upper t ht)
    lower_germ := fun t ht => (hgerm _ (hlow t ht)).trans (d.lower_germ t ht)
    upper_germ := fun t ht => (hgerm _ (hupp t ht)).trans (d.upper_germ t ht)
    radius := ε
    radius_pos := hε
    chart := Φ
    source_contains := hsource
    zero_section := hzero }
  exact ⟨tube, havoid⟩

/-- Simple connectivity and the actual local clean boundary suffice for the full filling. -/
theorem exists_tubularBigon_of_simplyConnected [SimplyConnectedSpace M]
    (g : C(Y, M)) (hg : ContMDiff J 𝓘(ℝ, E) ∞ g)
    (hdim : Module.finrank ℝ E = 6) (hobstacle : Module.finrank ℝ F ≤ 3)
    {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) S T a b k l h)
    {O : Set M} (hO : IsOpen O)
    (haO : MapsTo a (Icc (0 : ℝ) 1) O) (hbO : MapsTo b (Icc (0 : ℝ) 1) O)
    (hcover : range g ∩ O ⊆ S ∪ T) (hS : S ⊆ range g) (hT : T ⊆ range g) :
    ∃ d' : TubularBigon (E := E) S T a b k l h,
      ∀ p ∈ interior (bigon h), d'.map p ∉ range g := by
  obtain ⟨d₀⟩ := nonempty_smoothCleanBigonBoundary_of_simplyConnected d
  exact exists_tubularBigon_avoiding_whole_obstacle g hg hdim hobstacle d₀ hO haO hbO hcover hS hT

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
