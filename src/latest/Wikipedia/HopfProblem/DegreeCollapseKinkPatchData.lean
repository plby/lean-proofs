import Wikipedia.HopfProblem.DegreeCollapseGloballyCleanKinkChart
import Wikipedia.HopfProblem.DegreeCollapseCompactKinkFit

/-!
# Constructed native data fitting the complete compact modification

The original immersion supplies the chart, the unique branch, and the
positive scale. The full bounded-time trace lies inside the target chart;
the compact source support lies strictly inside the source patch.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization SupportedCusp

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]

structure KinkPatchData (F : Sphere 3 → M) where
  center : Vector 3
  chart : PartialDiffeomorph (𝓡 6) (𝓡 6) (Vector 6) M ∞
  radius : ℝ
  radius_pos : 0 < radius
  plane_source : ∀ x ∈ closedBall (0 : Vector 3) radius, plane x ∈ chart.source
  cutoff : Cutoff
  scale : ℝ
  scale_pos : 0 < scale
  support_subset : scaledSupport cutoff scale ⊆ ball (0 : Vector 3) radius
  trace_source : ∀ t ∈ Icc (-1 : ℝ) 1, ∀ x ∈ scaledSupport cutoff scale,
    scaledMap cutoff scale t x ∈ chart.source
  plane_formula : ∀ x, plane x ∈ chart.source →
    chart (plane x) = F (shiftedSourceChart center x)
  full_fibers : ∀ q ∈ chart.source, ∀ z : Sphere 3,
    F z = chart q ↔ ∃ v : Vector 3, q = plane v ∧ z = shiftedSourceChart center v

theorem nonempty_kinkPatchData [T2Space M] [CompactSpace M] [IsManifold (𝓡 6) ∞ M]
    (F : C(Sphere 3, M)) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) F x))
    (ht : ∀ x y, x ≠ y → F x = F y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) F x).coprod (mfderiv (𝓡 3) (𝓡 6) F y))) :
    Nonempty (KinkPatchData F) := by
  obtain ⟨a, δ, hδ, Φ, hδΦ, hplane, hfibers⟩ := exists_globally_clean_kink_chart F hf hi ht
  have h0Φ : (0 : Vector 6) ∈ Φ.source := hδΦ (mem_closedBall_self hδ.le)
  have hopen : IsOpen (plane ⁻¹' Φ.source) := Φ.open_source.preimage contDiff_plane.continuous
  have h0 : (0 : Vector 3) ∈ plane ⁻¹' Φ.source := by
    change plane 0 ∈ Φ.source
    rwa [plane_zero]
  obtain ⟨r, hr, hrΦ⟩ := nhds_basis_closedBall.mem_iff.mp (hopen.mem_nhds h0)
  obtain ⟨β⟩ := nonempty_cutoff
  obtain ⟨ε, hε, hsupport, htrace⟩ := exists_scaled_kink_fit β hr Φ.open_source h0Φ
  exact ⟨⟨a, Φ, r, hr, hrΦ, β, ε, hε, hsupport, htrace, hplane, hfibers⟩⟩

namespace KinkPatchData

variable {F : Sphere 3 → M} (P : KinkPatchData F)

def sourcePatch : Set (Sphere 3) :=
  shiftedSourceChart P.center '' ball (0 : Vector 3) P.radius

def sourceSupport : Set (Sphere 3) :=
  shiftedSourceChart P.center '' scaledSupport P.cutoff P.scale

def localFamily (z : ℝ × Sphere 3) : M :=
  P.chart (scaledMap P.cutoff P.scale z.1 ((shiftedSourceChart P.center).symm z.2))

theorem isOpen_sourcePatch : IsOpen P.sourcePatch :=
  ((shiftedSourceChart P.center).toOpenPartialHomeomorph.isOpenEmbedding
    (shiftedSourceChart_source P.center)).isOpenMap _ isOpen_ball

theorem isCompact_sourceSupport : IsCompact P.sourceSupport :=
  (isCompact_scaledSupport P.cutoff P.scale).image
    (contMDiff_shiftedSourceChart P.center).continuous

theorem sourceSupport_subset : P.sourceSupport ⊆ P.sourcePatch :=
  image_mono P.support_subset

theorem sourcePatch_subset_target : P.sourcePatch ⊆ (shiftedSourceChart P.center).target := by
  rintro _ ⟨x, _, rfl⟩
  exact (shiftedSourceChart P.center).map_source (by rw [shiftedSourceChart_source]; trivial)

theorem localFamily_source (t : ℝ) (x : Vector 3) :
    P.localFamily (t, shiftedSourceChart P.center x) =
      P.chart (scaledMap P.cutoff P.scale t x) := by
  have h := (shiftedSourceChart P.center).left_inv
    (by rw [shiftedSourceChart_source]; exact mem_univ x)
  exact congrArg (fun u ↦ P.chart (scaledMap P.cutoff P.scale t u)) h

theorem map_source {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    {x : Vector 3} (hx : x ∈ ball (0 : Vector 3) P.radius) :
    scaledMap P.cutoff P.scale t x ∈ P.chart.source := by
  by_cases hK : x ∈ scaledSupport P.cutoff P.scale
  · exact P.trace_source t ht x hK
  · rw [scaledMap_eq_plane_off_support P.cutoff P.scale_pos.ne' t hK]
    exact P.plane_source x (ball_subset_closedBall hx)

theorem localFamily_start (x : Sphere 3) (hx : x ∈ P.sourcePatch) :
    P.localFamily (-1, x) = F x := by
  obtain ⟨u, hu, rfl⟩ := hx
  rw [P.localFamily_source, scaledMap_neg_one P.cutoff P.scale_pos.ne']
  exact P.plane_formula u (P.plane_source u (ball_subset_closedBall hu))

theorem localFamily_fixed (t : ℝ) (x : Sphere 3)
    (hx : x ∈ P.sourcePatch) (hxK : x ∉ P.sourceSupport) :
    P.localFamily (t, x) = F x := by
  obtain ⟨u, hu, rfl⟩ := hx
  have huK : u ∉ scaledSupport P.cutoff P.scale := fun h ↦ hxK ⟨u, h, rfl⟩
  rw [P.localFamily_source, scaledMap_eq_plane_off_support P.cutoff P.scale_pos.ne' t huK]
  exact P.plane_formula u (P.plane_source u (ball_subset_closedBall hu))

end KinkPatchData
end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
