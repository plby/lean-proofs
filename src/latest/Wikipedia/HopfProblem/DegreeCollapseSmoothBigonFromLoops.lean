import Wikipedia.HopfProblem.DegreeCollapseSphereCube
import Wikipedia.SmoothSixDPoincare.SmoothCleanBigonBoundary
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Smooth clean bigon boundaries from simple connectivity

Native first homotopy groups give actual nullhomotopies of maps from the
literal circle. Relative smoothing then extends the constructed local
bigon boundary while preserving a compact embedded immersive boundary
neighborhood and both entire strip germs. No homotopy-sphere equivalence
is required for this extension.
-/

noncomputable section

open Set Function Filter Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open Wikipedia.SmoothSixDPoincare WhitneyPairModel

theorem circle_nullhomotopic_of_simplyConnected {X : Type*} [TopologicalSpace X]
    [SimplyConnectedSpace X] (f : C(Hemisphere.Sphere 1, X)) :
    ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  let : Subsingleton (π_ 1 X (f (SphereCube.point 1))) :=
    HomotopyGroup.pi1EquivFundamentalGroup.injective.subsingleton
  obtain ⟨H⟩ := SphereCube.homotopicRel_const_of_subsingleton (by norm_num : 0 < 1) f
  exact ⟨f (SphereCube.point 1), ⟨H.toHomotopy⟩⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- Circle contractions suffice to extend the local clean boundary data. -/
theorem nonempty_smoothCleanBigonBoundary_of_circle_nullhomotopies
    (hnull : ∀ f : C(Hemisphere.Sphere 1, M),
      ∃ c, f.Homotopic (ContinuousMap.const _ c))
    {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) S T a b k l h) :
    Nonempty (SmoothCleanBigonBoundary (E := E) S T a b k l h) := by
  have hfrontD : frontier (bigon h) ⊆ d.domain :=
    d.boundary_covered.trans (interior_subset.trans d.neighborhood_subset)
  obtain ⟨F, hF, U, hU, hfrontU, hUD, hEq⟩ :=
    exists_smooth_bigon_neighborhood_extension_of_circle_nullhomotopies hnull
      d.height_pos d.open_domain d.smooth hfrontD
  have hcompact : IsCompact (frontier (bigon h)) :=
    (isCompact_bigon d.height_pos).of_isClosed_subset isClosed_frontier
      (fun p hp => ((mem_frontier_bigon_iff h p).mp hp).1)
  obtain ⟨C, hC, hCc, hfrontC, hCU⟩ := exists_compact_closed_between hcompact hU hfrontU
  have hgerm : ∀ p ∈ U, (F : (ℝ × ℝ) → M) =ᶠ[𝓝 p] d.map :=
    fun p hp => mem_of_superset (hU.mem_nhds hp) (fun _ hx => hEq hx)
  have hinj : InjOn F C := by
    intro p hp q hq hpq
    apply d.injective (hUD (hCU hp)) (hUD (hCU hq))
    rw [← hEq (hCU hp), ← hEq (hCU hq)]
    exact hpq
  have hemb : IsClosedEmbedding (fun p : C => F p) := by
    let : CompactSpace C := isCompact_iff_compactSpace.mp hC
    apply (F.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro p q hpq
    exact Subtype.ext (hinj p.property q.property hpq)
  have hi : ∀ p ∈ C, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) F p) := by
    intro p hp
    rw [(hgerm p (hCU hp)).mfderiv_eq]
    exact d.derivative_injective p (hUD (hCU hp))
  have hlowU : ∀ t ∈ Icc (0 : ℝ) 1, (2 * t - 1, 0) ∈ U := by
    intro t ht
    apply hfrontU
    exact (mem_frontier_bigon_iff_exists_time d.height_pos _).mpr ⟨t, ht, Or.inl rfl⟩
  have huppU : ∀ t ∈ Icc (0 : ℝ) 1, (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ U := by
    intro t ht
    apply hfrontU
    exact (mem_frontier_bigon_iff_exists_time d.height_pos _).mpr ⟨t, ht, Or.inr rfl⟩
  refine ⟨{
    height_pos := d.height_pos
    map := F
    smooth := hF
    neighborhood := C
    compact_neighborhood := hC
    closed_neighborhood := hCc
    boundary_covered := hfrontC
    injective := hinj
    closed_embedding := hemb
    derivative_injective := hi
    clean := ?_
    lower := fun t ht => (hEq (hlowU t ht)).trans (d.lower t ht)
    upper := fun t ht => (hEq (huppU t ht)).trans (d.upper t ht)
    lower_germ := fun t ht => (hgerm _ (hlowU t ht)).trans (d.lower_germ t ht)
    upper_germ := fun t ht => (hgerm _ (huppU t ht)).trans (d.upper_germ t ht) }⟩
  intro p hp hnot
  have hpi : p ∈ interior (bigon h) := by
    by_contra hni
    apply hnot
    rw [frontier, (isClosed_bigon h).closure_eq]
    exact ⟨hp.1, hni⟩
  rw [hEq (hCU hp.2)]
  exact d.interior_avoids p ⟨hUD (hCU hp.2), hpi⟩

/-- Simple connectivity supplies the actual circle contractions used by smoothing. -/
theorem nonempty_smoothCleanBigonBoundary_of_simplyConnected [SimplyConnectedSpace M]
    {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) S T a b k l h) :
    Nonempty (SmoothCleanBigonBoundary (E := E) S T a b k l h) :=
  nonempty_smoothCleanBigonBoundary_of_circle_nullhomotopies
    circle_nullhomotopic_of_simplyConnected d

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
