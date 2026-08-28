import Wikipedia.HopfProblem.TriangleRiemannCorners
import Wikipedia.HopfProblem.TriangleCornerCoverage

/-!
# Ambient analytic patches at the actual elliptic triangle corners

The constructed noncritical boundary germs are composed with the literal
cubic and oriented quartic Cayley powers.  Complete inverse-parameter
coverage proves agreement with the actual Riemann map at every nearby
triangle point.  Consequently these are full analytic corner patches and
give the forward boundary limits, with exact orders three and four.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace Wikipedia.HopfProblem.RiemannMapping

open SpecialPeriods.Triangle

/-- The actual ambient patch at the order-three corner. -/
def triangleCornerThreePatch : ℂ → ℂ :=
  triangleCornerThreeGerm.function ∘ cornerPowerThree

/-- The actual ambient patch at the order-four corner.  The negative sign
in the power coordinate is part of `cornerPowerFour`. -/
def triangleCornerFourPatch : ℂ → ℂ :=
  triangleCornerFourGerm.function ∘ cornerPowerFour

@[simp] theorem triangleCornerThreePatch_center :
    triangleCornerThreePatch centerOne = triangleCornerThreeGerm.function 0 := by
  simp only [triangleCornerThreePatch, Function.comp_apply, cornerPowerThree_center]

@[simp] theorem triangleCornerFourPatch_center :
    triangleCornerFourPatch centerTwo = triangleCornerFourGerm.function 0 := by
  simp only [triangleCornerFourPatch, Function.comp_apply, cornerPowerFour_center]

theorem triangleCornerThreePatch_analyticAt :
    AnalyticAt ℂ triangleCornerThreePatch (centerOne : ℂ) := by
  have hH : AnalyticAt ℂ triangleCornerThreeGerm.function (cornerPowerThree centerOne) := by
    rw [cornerPowerThree_center]
    exact triangleCornerThreeGerm.analytic 0 (mem_ball_self triangleCornerThreeGerm.radius_pos)
  exact hH.comp cornerPowerThree_analyticAt_center

theorem triangleCornerFourPatch_analyticAt :
    AnalyticAt ℂ triangleCornerFourPatch (centerTwo : ℂ) := by
  have hH : AnalyticAt ℂ triangleCornerFourGerm.function (cornerPowerFour centerTwo) := by
    rw [cornerPowerFour_center]
    exact triangleCornerFourGerm.analytic 0 (mem_ball_self triangleCornerFourGerm.radius_pos)
  exact hH.comp cornerPowerFour_analyticAt_center

/-- The cubic ambient patch agrees with the actual Riemann map on a full
one-sided neighborhood of the actual center. -/
theorem exists_triangleCornerThreePatch_agrees :
    ∃ ε : ℝ, 0 < ε ∧
      EqOn triangleCornerThreePatch triangleMap (ball (centerOne : ℂ) ε ∩ triangleInterior) := by
  obtain ⟨ε, hε, hcover⟩ :=
    exists_cornerParameterThree_coverage triangleCornerThreeGerm.radius_pos
  refine ⟨ε, hε, ?_⟩
  intro z hz
  have hc := hcover z hz.1 hz.2
  have he := triangleCornerThreeGerm.agrees hc.1
  change triangleCornerThreeGerm.function (cornerPowerThree z) = triangleMap z
  simpa only [Function.comp_apply, hc.2] using he

/-- The corresponding full one-sided agreement at the quartic corner. -/
theorem exists_triangleCornerFourPatch_agrees :
    ∃ ε : ℝ, 0 < ε ∧
      EqOn triangleCornerFourPatch triangleMap (ball (centerTwo : ℂ) ε ∩ triangleInterior) := by
  obtain ⟨ε, hε, hcover⟩ :=
    exists_cornerParameterFour_coverage triangleCornerFourGerm.radius_pos
  refine ⟨ε, hε, ?_⟩
  intro z hz
  have hc := hcover z hz.1 hz.2
  have he := triangleCornerFourGerm.agrees hc.1
  change triangleCornerFourGerm.function (cornerPowerFour z) = triangleMap z
  simpa only [Function.comp_apply, hc.2] using he

theorem triangleCornerThreePatch_eventuallyEq :
    triangleCornerThreePatch =ᶠ[𝓝[triangleInterior] (centerOne : ℂ)] triangleMap := by
  obtain ⟨ε, hε, he⟩ := exists_triangleCornerThreePatch_agrees
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (centerOne : ℂ) hε)] with z hz hb
  exact he ⟨hb, hz⟩

theorem triangleCornerFourPatch_eventuallyEq :
    triangleCornerFourPatch =ᶠ[𝓝[triangleInterior] (centerTwo : ℂ)] triangleMap := by
  obtain ⟨ε, hε, he⟩ := exists_triangleCornerFourPatch_agrees
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (centerTwo : ℂ) hε)] with z hz hb
  exact he ⟨hb, hz⟩

/-- The actual Riemann map has the claimed forward limit along the whole
triangle at the first elliptic vertex. -/
theorem triangleCornerThree_forward_limit :
    Tendsto triangleMap (𝓝[triangleInterior] (centerOne : ℂ))
      (𝓝 (triangleCornerThreeGerm.function 0)) := by
  have h : Tendsto triangleCornerThreePatch (𝓝[triangleInterior] (centerOne : ℂ))
      (𝓝 (triangleCornerThreePatch centerOne)) :=
    triangleCornerThreePatch_analyticAt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [triangleCornerThreePatch_center] at h
  exact h.congr' triangleCornerThreePatch_eventuallyEq

/-- The whole-triangle forward limit at the second elliptic vertex. -/
theorem triangleCornerFour_forward_limit :
    Tendsto triangleMap (𝓝[triangleInterior] (centerTwo : ℂ))
      (𝓝 (triangleCornerFourGerm.function 0)) := by
  have h : Tendsto triangleCornerFourPatch (𝓝[triangleInterior] (centerTwo : ℂ))
      (𝓝 (triangleCornerFourPatch centerTwo)) :=
    triangleCornerFourPatch_analyticAt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [triangleCornerFourPatch_center] at h
  exact h.congr' triangleCornerFourPatch_eventuallyEq

private theorem analyticOrderAt_noncritical_comp_zero
    {H p : ℂ → ℂ} {a : ℂ} (hH : AnalyticAt ℂ H 0)
    (hHd : deriv H 0 ≠ 0) (hp : AnalyticAt ℂ p a) (hp0 : p a = 0) :
    analyticOrderAt (fun z => H (p z) - H 0) a = analyticOrderAt p a := by
  have hHsub : AnalyticAt ℂ (fun w => H w - H 0) (p a) := by
    rw [hp0]
    exact hH.sub analyticAt_const
  have horder := hH.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hHd
  have he := hHsub.analyticOrderAt_comp hp
  have hsub : (fun z => p z - p a) = p := by
    funext z
    rw [hp0, sub_zero]
  rw [hsub, hp0, horder, one_mul] at he
  simpa only [Function.comp_def] using he

/-- The ambient cubic patch has exact order three after subtracting its
unit-circle boundary value. -/
theorem triangleCornerThreePatch_order :
    analyticOrderAt
      (fun z => triangleCornerThreePatch z - triangleCornerThreeGerm.function 0)
      (centerOne : ℂ) = 3 := by
  change analyticOrderAt
    (fun z => triangleCornerThreeGerm.function (cornerPowerThree z) -
      triangleCornerThreeGerm.function 0) (centerOne : ℂ) = 3
  rw [analyticOrderAt_noncritical_comp_zero
    (triangleCornerThreeGerm.analytic 0 (mem_ball_self triangleCornerThreeGerm.radius_pos))
    triangleCornerThreeGerm.deriv_ne_zero cornerPowerThree_analyticAt_center
    cornerPowerThree_center, cornerPowerThree_order_center]

/-- The ambient quartic patch has exact order four; the negative power
coordinate does not change this vanishing order. -/
theorem triangleCornerFourPatch_order :
    analyticOrderAt
      (fun z => triangleCornerFourPatch z - triangleCornerFourGerm.function 0)
      (centerTwo : ℂ) = 4 := by
  change analyticOrderAt
    (fun z => triangleCornerFourGerm.function (cornerPowerFour z) -
      triangleCornerFourGerm.function 0) (centerTwo : ℂ) = 4
  rw [analyticOrderAt_noncritical_comp_zero
    (triangleCornerFourGerm.analytic 0 (mem_ball_self triangleCornerFourGerm.radius_pos))
    triangleCornerFourGerm.deriv_ne_zero cornerPowerFour_analyticAt_center
    cornerPowerFour_center, cornerPowerFour_order_center]

end Wikipedia.HopfProblem.RiemannMapping
