import Wikipedia.SmoothSixDPoincare.ComplementFilledBigon
import Wikipedia.SmoothSixDPoincare.TwoSheetTubularBigon

/-!
# Actual tubular bigons of the required normal rank in the complement-controlled case

The full complement-filled bigon gives a genuine positive-radius native tubular
chart with its global zero section. This includes normal rank three in a
five-dimensional regular level. The frame is constructed but is not yet asserted
to be the required sheet-compatible Whitney framing.
-/

noncomputable section

open Set Function Filter Topology ContinuousMap TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

open WhitneyPairModel

variable {E M D Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [TopologicalSpace Y] [ChartedSpace D Y] [IsManifold 𝓘(ℝ, D) ∞ Y] [CompactSpace Y]

/-- Construct the native tube, full original arc values, and whole strip germs from the clean
boundary and contractions in the actual complement of the second sheet. -/
theorem CleanBigonBoundary.nonempty_tubularBigon_of_complement_contractions
    (g : C(Y, M)) (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    {T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) (range g) T a b k l h)
    (hT : IsClosed T)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, (⟨Tᶜ, hT.isOpen_compl⟩ : Opens M)),
      ∃ c, f.Homotopic (ContinuousMap.const _ c))
    (hdim : 5 ≤ Module.finrank ℝ E)
    (hobstacle : 2 + Module.finrank ℝ D < Module.finrank ℝ E)
    (n : ℕ) (hcodim : 2 + n = Module.finrank ℝ E) :
    Nonempty (TubularBigon (E := E) (range g) T a b k l h n) := by
  obtain ⟨f, hf, hemb, hi, havoid, V, hV, hfrontV, hEq⟩ :=
    d.exists_filled_bigon_of_complement_contractions g hg hT hnull hdim hobstacle
  have hinj : InjOn f (bigon h) := by
    intro p hp z hz heq
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨p, hp⟩) (a₂ := ⟨z, hz⟩) heq)
  obtain ⟨ε, hε, Φ, hsource, hzero, -⟩ :=
    exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero hf
      (isCompact_bigon d.height_pos) (zero_mem_bigon d.height_pos.le)
      (starConvex_bigon d.height_pos.le) hinj hi n
      (by simpa only [Module.finrank_prod, Module.finrank_self] using hcodim)
      isOpen_univ (mapsTo_univ _ _)
  have hgerm : ∀ p ∈ frontier (bigon h), (f : (ℝ × ℝ) → M) =ᶠ[𝓝 p] d.map :=
    fun _ hp => mem_of_superset (hV.mem_nhds (hfrontV hp)) (fun _ hx => hEq hx)
  have hlow : ∀ t ∈ Icc (0 : ℝ) 1, (2 * t - 1, 0) ∈ frontier (bigon h) :=
    fun t ht => (mem_frontier_bigon_iff_exists_time d.height_pos _).mpr ⟨t, ht, Or.inl rfl⟩
  have hupp : ∀ t ∈ Icc (0 : ℝ) 1,
      (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ frontier (bigon h) :=
    fun t ht => (mem_frontier_bigon_iff_exists_time d.height_pos _).mpr ⟨t, ht, Or.inr rfl⟩
  exact ⟨{
    height_pos := d.height_pos
    map := f
    smooth := hf
    closed_embedding := hemb
    derivative_injective := hi
    interior_avoids := havoid
    lower := fun t ht => (hEq (hfrontV (hlow t ht))).trans (d.lower t ht)
    upper := fun t ht => (hEq (hfrontV (hupp t ht))).trans (d.upper t ht)
    lower_germ := fun t ht => (hgerm _ (hlow t ht)).trans (d.lower_germ t ht)
    upper_germ := fun t ht => (hgerm _ (hupp t ht)).trans (d.upper_germ t ht)
    radius := ε
    radius_pos := hε
    chart := Φ
    source_contains := hsource
    zero_section := hzero }⟩

end Wikipedia.SmoothSixDPoincare
