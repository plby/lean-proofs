import Wikipedia.NoExoticSixSphere.SmoothFramedCollapse
import Wikipedia.NoExoticSixSphere.UniformNormalRemainder

/-!
# Comparing actual defining equations for the same framed compact core

Positive radius normalization makes both normal differentials the identity.
The actual coordinates then have a uniform relative error estimate in one
common normal disk. Every convex interpolation has exactly the original
zero section there; equality of the coordinate germs is not assumed.
-/

noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a)

def normalizedCoordinates (y : EuclideanSpace ℝ (Fin e.ambientDimension)) : e.NormalModel :=
  d.radius • d.coordinates y

theorem coordinates_core (x : M) : d.coordinates (e.toFun x) = 0 := by
  have h := (d.local_formula (e.toFun x) (d.range_subset ⟨x, rfl⟩)).symm.trans
    ((d.zero_fiber (e.toFun x)).mpr ⟨x, rfl⟩)
  exact OnePoint.coe_injective h

theorem normalizedCoordinates_core (x : M) : d.normalizedCoordinates (e.toFun x) = 0 := by
  rw [normalizedCoordinates, d.coordinates_core, smul_zero]

theorem contDiffOn_normalizedCoordinates :
    ContDiffOn ℝ ∞ d.normalizedCoordinates d.neighborhood := by
  change ContDiffOn ℝ ∞ (fun y ↦ d.radius • d.coordinates y) d.neighborhood
  exact d.smooth_coordinates.const_smul d.radius

theorem normalizedCoordinates_differential_frame (x : M) :
    (fderiv ℝ d.normalizedCoordinates (e.toFun x)).comp (a.ambient x) =
      ContinuousLinearMap.id ℝ e.NormalModel := by
  have hd := ((d.smooth_coordinates.contDiffAt
    (d.open_neighborhood.mem_nhds (d.range_subset ⟨x, rfl⟩))).differentiableAt
      (by simp)).hasFDerivAt
  have hscaled := hd.const_smul d.radius
  change HasFDerivAt d.normalizedCoordinates
    (d.radius • fderiv ℝ d.coordinates (e.toFun x)) (e.toFun x) at hscaled
  rw [hscaled.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  change d.radius • fderiv ℝ d.coordinates (e.toFun x) (a.ambient x v) = v
  rw [← map_smul]
  exact d.differential_frame x v

variable [CompactSpace M]

theorem exists_uniform_normalizedCoordinates_estimate {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ x v, ‖v‖ ≤ r →
      e.toFun x + a.ambient x v ∈ d.neighborhood ∧
        ‖d.normalizedCoordinates (e.toFun x + a.ambient x v) - v‖ ≤ ε * ‖v‖ :=
  exists_uniform_normal_remainder_bound e.smooth.continuous a.contMDiff_ambient.continuous
    d.open_neighborhood (fun x ↦ d.range_subset ⟨x, rfl⟩)
    d.contDiffOn_normalizedCoordinates d.normalizedCoordinates_core
    d.normalizedCoordinates_differential_frame hε

theorem exists_uniform_convex_normal_comparison (d' : e.FramedCollapseData a) :
    ∃ r : ℝ, 0 < r ∧ ∀ x v, ‖v‖ ≤ r →
      e.toFun x + a.ambient x v ∈ d.neighborhood ∩ d'.neighborhood ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        (1 - t) • d.normalizedCoordinates (e.toFun x + a.ambient x v) +
          t • d'.normalizedCoordinates (e.toFun x + a.ambient x v) = 0 ↔ v = 0 := by
  obtain ⟨r, hr, h⟩ := d.exists_uniform_normalizedCoordinates_estimate
    (show (0 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨r', hr', h'⟩ := d'.exists_uniform_normalizedCoordinates_estimate
    (show (0 : ℝ) < 1 / 2 by norm_num)
  refine ⟨min r r', lt_min hr hr', fun x v hv ↦ ?_⟩
  have h₀ := h x v (hv.trans (min_le_left _ _))
  have h₁ := h' x v (hv.trans (min_le_right _ _))
  exact ⟨⟨h₀.1, h₁.1⟩, fun t ht ↦
    convex_blend_eq_zero_iff_of_relative_error (by norm_num) h₀.2 h₁.2 ht⟩

variable [IsManifold (𝓡 n) ∞ M] [Nonempty M]

/-- The comparison holds on an actual ambient open neighborhood of the whole core. -/
theorem exists_open_convex_coordinate_comparison (d' : e.FramedCollapseData a) :
    ∃ V : Set (EuclideanSpace ℝ (Fin e.ambientDimension)), IsOpen V ∧
      range e.toFun ⊆ V ∧ V ⊆ d.neighborhood ∩ d'.neighborhood ∧
      ∀ y ∈ V, ∀ t ∈ Icc (0 : ℝ) 1,
        (1 - t) • d.normalizedCoordinates y + t • d'.normalizedCoordinates y = 0 ↔
          y ∈ range e.toFun := by
  obtain ⟨r, hr, h⟩ := d.exists_uniform_convex_normal_comparison d'
  obtain ⟨Φ, hzero, hformula, -⟩ := e.exists_framedTubularNeighborhood a
  let W := Φ.source ∩ Prod.snd ⁻¹' Metric.ball (0 : e.NormalModel) r
  have hW : IsOpen W := Φ.open_source.inter (Metric.isOpen_ball.preimage continuous_snd)
  let V := Φ '' W
  have hV : IsOpen V :=
    Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hW inter_subset_left
  have hcore : range e.toFun ⊆ V := by
    rintro _ ⟨x, rfl⟩
    refine ⟨(x, 0), ⟨hzero x, Metric.mem_ball_self hr⟩, ?_⟩
    rw [hformula, map_zero, add_zero]
  refine ⟨V, hV, hcore, ?_, ?_⟩
  · rintro y ⟨p, hp, rfl⟩
    rw [hformula]
    exact (h p.1 p.2 (mem_ball_zero_iff.mp hp.2).le).1
  · rintro y ⟨p, hp, rfl⟩ t ht
    rw [hformula]
    constructor
    · intro hz
      have hv := ((h p.1 p.2 (mem_ball_zero_iff.mp hp.2).le).2 t ht).mp hz
      exact ⟨p.1, by rw [hv, map_zero, add_zero]⟩
    · rintro ⟨x, hx⟩
      rw [← hx, d.normalizedCoordinates_core, d'.normalizedCoordinates_core,
        smul_zero, smul_zero, add_zero]

/-- The same neighborhood also compares the original, unnormalized coordinates. -/
theorem exists_open_coordinate_comparison (d' : e.FramedCollapseData a) :
    ∃ V : Set (EuclideanSpace ℝ (Fin e.ambientDimension)), IsOpen V ∧
      range e.toFun ⊆ V ∧ V ⊆ d.neighborhood ∩ d'.neighborhood ∧
      ∀ y ∈ V, ∀ t ∈ Icc (0 : ℝ) 1,
        (1 - t) • d.coordinates y + t • d'.coordinates y = 0 ↔
          y ∈ range e.toFun := by
  obtain ⟨V, hV, hcore, hsub, h⟩ := d.exists_open_convex_coordinate_comparison d'
  refine ⟨V, hV, hcore, hsub, fun y hy t ht ↦ ?_⟩
  obtain ⟨s, hs, c, hc, heq⟩ := exists_convex_blend_positive_rescaling
    (F := e.NormalModel) d.radius_pos d'.radius_pos ht
  have hh := h y hy s hs
  change (1 - s) • (d.radius • d.coordinates y) +
    s • (d'.radius • d'.coordinates y) = 0 ↔ y ∈ range e.toFun at hh
  rw [heq] at hh
  simpa only [smul_eq_zero, ne_of_gt hc, false_or] using hh

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
