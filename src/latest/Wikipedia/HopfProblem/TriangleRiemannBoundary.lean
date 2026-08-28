import Wikipedia.HopfProblem.TriangleBoundaryCoordinates
import Wikipedia.HopfProblem.RiemannMappingTriangle
import Wikipedia.HopfProblem.RiemannBoundaryExtension
import Wikipedia.HopfProblem.RiemannBoundaryNoncritical

/-!
# Boundary extension of the actual triangle Riemann map

The genuine Riemann map of the half-Ford triangle extends in every verified
analytic straight-side coordinate.  The extension's boundary derivative is
nonzero.  Both assertions follow from the actual disc homeomorphism and
the proved boundary-side equations; no boundary values are presupposed.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology ComplexConjugate

namespace Wikipedia.HopfProblem.RiemannMapping

open SpecialPeriods.Triangle RiemannBoundary

/-- The ambient complex function underlying the actual triangle biholomorphism. -/
def triangleMap : ℂ → ℂ :=
  riemannMap triangleDomain triangleInterior_isSimplyConnected
    triangleInterior_ne_univ trianglePoint

theorem triangleMap_differentiable : DifferentiableOn ℂ triangleMap triangleInterior :=
  (riemannMap_spec triangleDomain triangleInterior_isSimplyConnected
    triangleInterior_ne_univ trianglePoint).1

theorem triangleMap_bijOn : BijOn triangleMap triangleInterior (ball (0 : ℂ) 1) :=
  (riemannMap_spec triangleDomain triangleInterior_isSimplyConnected
    triangleInterior_ne_univ trianglePoint).2.1

theorem triangleMap_biholomorph (z : triangleDomain) :
    triangleMap z = (triangleBiholomorph z : ℂ) := rfl

theorem triangleMap_norm_lt_one {z : ℂ} (hz : z ∈ triangleInterior) :
    ‖triangleMap z‖ < 1 := by
  simpa using triangleMap_bijOn.mapsTo hz

/-- A target ball whose inverse coordinates stay inside a prescribed
source neighborhood, obtained from the actual chart topology. -/
theorem exists_boundary_chart_target_ball (e : OpenPartialHomeomorph ℂ ℂ)
    {a : ℂ} (ha : a ∈ e.source) {r : ℝ} (hr : 0 < r) :
    ∃ δ > 0, ∀ w ∈ ball (e a) δ, w ∈ e.target ∧ e.symm w ∈ ball a r := by
  have hat := e.map_source ha
  have hinv : Tendsto e.symm (𝓝 (e a)) (𝓝 a) := by
    have h := (e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hat)).tendsto
    rwa [e.left_inv ha] at h
  have hnear : ∀ᶠ w in 𝓝 (e a), w ∈ e.target ∧ e.symm w ∈ ball a r := by
    filter_upwards [e.open_target.mem_nhds hat, hinv.eventually (ball_mem_nhds a hr)] with w hw hb
    exact ⟨hw, hb⟩
  exact Metric.mem_nhds_iff.mp hnear

/-- The actual Riemann map extends analytically and noncritically in a
verified local straight-side chart. -/
theorem exists_triangleMap_extension_in_side_chart
    (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ} (ha : a ∈ e.source)
    (he : AnalyticOnNhd ℂ e.symm e.target) (hreal : (e a).im = 0)
    {r : ℝ} (hr : 0 < r)
    (hside : ∀ z ∈ ball a r, z ∈ triangleInterior ↔ 0 < (e z).im) :
    ∃ ε > 0, ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (ball (e a) ε) ∧
      EqOn H (triangleMap ∘ e.symm) (ball (e a) ε ∩ {z | 0 < z.im}) ∧
      (∀ z ∈ ball (e a) ε, z.im = 0 → ‖H z‖ = 1) ∧
      deriv H (e a) ≠ 0 := by
  obtain ⟨δ, hδ, hδball⟩ := exists_boundary_chart_target_ball e ha hr
  have hinverse : DifferentiableOn ℂ e.symm (ball (e a) δ) :=
    he.differentiableOn.mono (fun z hz => (hδball z hz).1)
  have hmaps : MapsTo e.symm (ball (e a) δ ∩ {z | 0 < z.im}) triangleInterior := by
    intro z hz
    apply (hside _ (hδball z hz.1).2).mpr
    rw [e.right_inv (hδball z hz.1).1]
    exact hz.2
  have hout : ∀ t : ℝ, (t : ℂ) ∈ ball (e a) δ → e.symm (t : ℂ) ∉ triangleInterior := by
    intro t ht hin
    have hi := (hside _ (hδball t ht).2).mp hin
    rw [e.right_inv (hδball t ht).1, ofReal_im] at hi
    exact lt_irrefl _ hi
  have hae : ((e a).re : ℂ) = e a := by
    apply Complex.ext <;> simp [hreal]
  have hx : ((e a).re : ℂ) ∈ ball (e a) δ := hae.symm ▸ mem_ball_self hδ
  obtain ⟨ε, hε, H, hH, hHe, _, hHcircle⟩ :=
    exists_analytic_extension_discHomeomorph_in_boundary_chart
      triangleBiholomorph.toHomeomorph triangleMap_biholomorph isOpen_ball
      triangleMap_differentiable hinverse hmaps hout hx
  rw [hae] at hH hHe hHcircle
  let s := min ε δ
  have hs : 0 < s := lt_min hε hδ
  have hsε : ball (e a) s ⊆ ball (e a) ε := ball_subset_ball (min_le_left _ _)
  have hsδ : ball (e a) s ⊆ ball (e a) δ := ball_subset_ball (min_le_right _ _)
  have hnorm : ∀ z ∈ ball (e a) s, 0 < z.im → ‖H z‖ < 1 := by
    intro z hz hi
    rw [hHe ⟨hsε hz, hi⟩]
    exact triangleMap_norm_lt_one (hmaps ⟨hsδ hz, hi⟩)
  have hcircle : ∀ z ∈ ball (e a) s, z.im = 0 → ‖H z‖ = 1 := by
    intro z hz hi
    have hzre : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hi]
    simpa only [hzre] using hHcircle z.re (hzre.symm ▸ hsε hz)
  refine ⟨s, hs, H, hH.mono hsε, hHe.mono (inter_subset_inter_left _ hsε), hcircle, ?_⟩
  apply deriv_ne_zero_of_upper_halfPlane_to_unitDisc (hH _ (mem_ball_self hε))
    hreal (hcircle _ (mem_ball_self hs) hreal)
  filter_upwards [ball_mem_nhds (e a) hs] with z hz
  exact hnorm z hz

/-- Analytic noncritical extension at every point of the open circular
side, with the actual rational circle coordinate. -/
theorem exists_triangleMap_extension_circle_side {a : ℂ}
    (haL : stripLeft < a.re) (haR : a.re < -1 / 2)
    (hai : 0 < a.im) (haC : ‖a + 1‖ = 1) :
    ∃ ε > 0, ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (ball (circleBoundaryChart a) ε) ∧
      EqOn H (triangleMap ∘ circleBoundaryChart.symm)
        (ball (circleBoundaryChart a) ε ∩ {z | 0 < z.im}) ∧
      (∀ z ∈ ball (circleBoundaryChart a) ε, z.im = 0 → ‖H z‖ = 1) ∧
      deriv H (circleBoundaryChart a) ≠ 0 := by
  obtain ⟨r, hr, hb⟩ := exists_circle_side_neighborhood haL haR hai
  have ha : a ∈ circleBoundaryChart.source := (hb a (mem_ball_self hr)).1
  apply exists_triangleMap_extension_in_side_chart circleBoundaryChart ha
    circleUnstraighten_analyticOnNhd
  · exact (circleStraighten_im_eq_zero_iff ha).mpr haC
  · exact hr
  · exact fun z hz => (hb z hz).2

end Wikipedia.HopfProblem.RiemannMapping
