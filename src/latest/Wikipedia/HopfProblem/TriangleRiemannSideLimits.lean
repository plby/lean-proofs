import Wikipedia.HopfProblem.TriangleRiemannCorners
import Wikipedia.HopfProblem.TriangleRiemannSides

/-!
# Forward and inverse limits on the actual open triangle sides

The boundary germs in the explicit side coordinates give limits along
every interior approach to a side point.  The inverse disc limit is the
original geometric point, proved using the actual local inverse theorem.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace Wikipedia.HopfProblem.RiemannMapping

open SpecialPeriods.Triangle RiemannBoundary

def triangleSideParameter (e : OpenPartialHomeomorph ℂ ℂ) (a w : ℂ) : ℂ :=
  e.symm (w + e a)

theorem triangleSideParameter_zero (e : OpenPartialHomeomorph ℂ ℂ)
    {a : ℂ} (ha : a ∈ e.source) : triangleSideParameter e a 0 = a := by
  simp only [triangleSideParameter, zero_add, e.left_inv ha]

theorem continuousAt_triangleSideParameter_zero (e : OpenPartialHomeomorph ℂ ℂ)
    {a : ℂ} (ha : a ∈ e.source) : ContinuousAt (triangleSideParameter e a) 0 := by
  have hi := e.continuousOn_symm.continuousAt (e.open_target.mem_nhds (e.map_source ha))
  exact ContinuousAt.comp (g := e.symm) (f := fun w : ℂ => w + e a) (x := 0)
    (by simpa only [zero_add] using hi) (continuousAt_id.add_const (e a))

theorem exists_triangleSideBoundaryGerm
    (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ} (ha : a ∈ e.source)
    (he : AnalyticOnNhd ℂ e.symm e.target) (hreal : (e a).im = 0)
    {r : ℝ} (hr : 0 < r)
    (hside : ∀ z ∈ ball a r, z ∈ triangleInterior ↔ 0 < (e z).im) :
    Nonempty (TriangleBoundaryGerm (triangleSideParameter e a)) := by
  obtain ⟨δ, hδ, hδball⟩ := exists_boundary_chart_target_ball e ha hr
  have hadd : ∀ w ∈ ball (0 : ℂ) δ, w + e a ∈ ball (e a) δ := by
    intro w hw
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hw
  have hφ : AnalyticOnNhd ℂ (triangleSideParameter e a) (ball 0 δ) := by
    intro w hw
    exact (he (w + e a) (hδball _ (hadd w hw)).1).comp (f := fun z : ℂ => z + e a)
      (analyticAt_id.add analyticAt_const)
  apply exists_triangleBoundaryGerm hδ (hφ.mono inter_subset_left)
    (hφ.continuousOn.mono inter_subset_left)
  · intro w hw
    apply (hside _ (hδball _ (hadd w hw.1)).2).mpr
    rw [e.right_inv (hδball _ (hadd w hw.1)).1, add_im, hreal, add_zero]
    exact hw.2
  · intro t ht hin
    have hi := (hside _ (hδball _ (hadd t ht)).2).mp hin
    change 0 < (e (e.symm ((t : ℂ) + e a))).im at hi
    rw [e.right_inv (hδball _ (hadd t ht)).1, add_im, ofReal_im, hreal, add_zero] at hi
    exact lt_irrefl _ hi

theorem triangleSideBoundaryGerm_forward_limit
    (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ} (ha : a ∈ e.source)
    (hreal : (e a).im = 0) {r : ℝ} (hr : 0 < r)
    (hside : ∀ z ∈ ball a r, z ∈ triangleInterior ↔ 0 < (e z).im)
    (g : TriangleBoundaryGerm (triangleSideParameter e a)) :
    Tendsto triangleMap (𝓝[triangleInterior] a) (𝓝 (g.function 0)) := by
  have hec : ContinuousAt e a := e.continuousOn.continuousAt (e.open_source.mem_nhds ha)
  have ht : Tendsto (fun z => e z - e a) (𝓝 a) (𝓝 (0 : ℂ)) := by
    have hsub : Tendsto (fun z => e z - e a) (𝓝 a) (𝓝 (e a - e a)) :=
      hec.tendsto.sub_const (e a)
    simpa only [sub_self] using hsub
  have hlim : Tendsto (fun z => g.function (e z - e a))
      (𝓝[triangleInterior] a) (𝓝 (g.function 0)) :=
    ((g.analytic 0 (mem_ball_self g.radius_pos)).continuousAt.tendsto.comp ht).mono_left
      nhdsWithin_le_nhds
  have heq : triangleMap =ᶠ[𝓝[triangleInterior] a] (fun z => g.function (e z - e a)) := by
    have hs : ∀ᶠ z in 𝓝[triangleInterior] a, z ∈ e.source :=
      mem_nhdsWithin_of_mem_nhds (e.open_source.mem_nhds ha)
    have hb : ∀ᶠ z in 𝓝[triangleInterior] a, z ∈ ball a r :=
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds a hr)
    have hp : ∀ᶠ z in 𝓝[triangleInterior] a, e z - e a ∈ ball (0 : ℂ) g.radius :=
      (ht.eventually (ball_mem_nhds (0 : ℂ) g.radius_pos)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hs, hb, hp, self_mem_nhdsWithin] with z hz hbz hpz hzT
    have hi : 0 < (e z - e a).im := by
      rw [sub_im, hreal, sub_zero]
      exact (hside z hbz).mp hzT
    have hg := g.agrees ⟨hpz, hi⟩
    simpa only [Function.comp_apply, triangleSideParameter, sub_add_cancel,
      e.left_inv hz] using hg.symm
  exact hlim.congr' heq.symm

theorem triangleSideBoundaryGerm_inverse_limit
    (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ} (ha : a ∈ e.source)
    (g : TriangleBoundaryGerm (triangleSideParameter e a)) :
    Tendsto (discHomeomorphInverse triangleBiholomorph.toHomeomorph)
      (𝓝[ball (0 : ℂ) 1] (g.function 0)) (𝓝 a) := by
  simpa only [triangleSideParameter_zero e ha] using
    tendsto_discHomeomorphInverse_of_boundary_chart triangleBiholomorph.toHomeomorph
      triangleMap_biholomorph (continuousAt_triangleSideParameter_zero e ha)
      g.strictDeriv g.deriv_ne_zero g.sourceCorrespondence

/-- Both actual one-sided limits at an open side point. -/
theorem exists_triangleMap_side_limits
    (e : OpenPartialHomeomorph ℂ ℂ) {a : ℂ} (ha : a ∈ e.source)
    (he : AnalyticOnNhd ℂ e.symm e.target) (hreal : (e a).im = 0)
    {r : ℝ} (hr : 0 < r)
    (hside : ∀ z ∈ ball a r, z ∈ triangleInterior ↔ 0 < (e z).im) :
    ∃ w : ℂ, ‖w‖ = 1 ∧
      Tendsto triangleMap (𝓝[triangleInterior] a) (𝓝 w) ∧
      Tendsto (discHomeomorphInverse triangleBiholomorph.toHomeomorph)
        (𝓝[ball (0 : ℂ) 1] w) (𝓝 a) := by
  obtain ⟨g⟩ := exists_triangleSideBoundaryGerm e ha he hreal hr hside
  exact ⟨g.function 0, g.unit,
    triangleSideBoundaryGerm_forward_limit e ha hreal hr hside g,
    triangleSideBoundaryGerm_inverse_limit e ha g⟩

theorem exists_triangleMap_circle_side_limits {a : ℂ}
    (haL : stripLeft < a.re) (haR : a.re < -1 / 2)
    (hai : 0 < a.im) (haC : ‖a + 1‖ = 1) :
    ∃ w : ℂ, ‖w‖ = 1 ∧
      Tendsto triangleMap (𝓝[triangleInterior] a) (𝓝 w) ∧
      Tendsto (discHomeomorphInverse triangleBiholomorph.toHomeomorph)
        (𝓝[ball (0 : ℂ) 1] w) (𝓝 a) := by
  obtain ⟨r, hr, hside⟩ := exists_circle_side_neighborhood haL haR hai
  have ha : a ∈ circleBoundaryChart.source := (hside a (mem_ball_self hr)).1
  exact exists_triangleMap_side_limits circleBoundaryChart ha
    circleUnstraighten_analyticOnNhd ((circleStraighten_im_eq_zero_iff ha).mpr haC)
    hr (fun z hz => (hside z hz).2)

theorem exists_triangleMap_left_side_limits {a : ℂ} (ha : a.re = stripLeft)
    (hai : 0 < a.im) (haC : 1 < ‖a + 1‖) :
    ∃ w : ℂ, ‖w‖ = 1 ∧
      Tendsto triangleMap (𝓝[triangleInterior] a) (𝓝 w) ∧
      Tendsto (discHomeomorphInverse triangleBiholomorph.toHomeomorph)
        (𝓝[ball (0 : ℂ) 1] w) (𝓝 a) := by
  obtain ⟨r, hr, hside⟩ := exists_left_side_neighborhood ha hai haC
  apply exists_triangleMap_side_limits leftBoundaryChart.toOpenPartialHomeomorph
    (mem_univ a) (fun z _ => leftBoundaryChart_symm_analyticAt z)
  · change (leftBoundaryChart a).im = 0
    simp [ha]
  · exact hr
  · exact hside

theorem exists_triangleMap_right_side_limits {a : ℂ} (ha : a.re = -1 / 2)
    (hai : 0 < a.im) (haC : 1 < ‖a + 1‖) :
    ∃ w : ℂ, ‖w‖ = 1 ∧
      Tendsto triangleMap (𝓝[triangleInterior] a) (𝓝 w) ∧
      Tendsto (discHomeomorphInverse triangleBiholomorph.toHomeomorph)
        (𝓝[ball (0 : ℂ) 1] w) (𝓝 a) := by
  obtain ⟨r, hr, hside⟩ := exists_right_side_neighborhood ha hai haC
  apply exists_triangleMap_side_limits rightBoundaryChart.toOpenPartialHomeomorph
    (mem_univ a) (fun z _ => rightBoundaryChart_symm_analyticAt z)
  · change (rightBoundaryChart a).im = 0
    norm_num [rightBoundaryChart_im, ha]
  · exact hr
  · exact hside

end Wikipedia.HopfProblem.RiemannMapping
