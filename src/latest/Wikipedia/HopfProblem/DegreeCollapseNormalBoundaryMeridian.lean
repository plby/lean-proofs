import Wikipedia.HopfProblem.DegreeCollapseTubeBoundaryComparison

/-!
# The normal boundary data gives the actual native meridian comparison

The derivative boundary data controls nonvanishing. Its chosen parameter
ball lies in a prescribed original chart neighborhood. The tube homotopy
therefore applies to the actual trace, and its normal map is exactly the
map whose integral coefficient was proved to be a unit.
-/

noncomputable section

open Set Function Metric ContinuousMap
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem normal_boundary_homotopic_native_meridian (d : MorseSurgeryData E f p)
    (g : A → d.UpperLevel) {L : A ≃L[ℝ] d.chart.NegativeCoordinates} {s : Set A}
    (b : LocalDegree.BoundaryData (d.beltNormal ∘ g) L s)
    (hc : ContinuousOn g s) (hdomain : ∀ z ∈ s, g z ∈ d.beltNormalDomain)
    (hsmall : ∀ z ∈ s, ‖d.radius⁻¹ • d.beltNormal (g z)‖ < 1)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ∃ J : C(sphere (0 : A) 1, ((range d.surgery.beltSphere)ᶜ : Set d.UpperLevel)),
      (∀ u, (J u).val = g (b.radius • u.val)) ∧
      ∃ v : sphere (0 : d.chart.PositiveCoordinates) 1,
        J.Homotopic ((nativeBeltTubeMeridian d v r hr hr1).comp b.normalizedMap) := by
  let F : C(closedBall (0 : A) b.radius, d.chart.beltTarget d.radius) := {
    toFun := fun z => ⟨g z.val, hdomain z.val (b.ball_subset z.property)⟩
    continuous_toFun := (hc.comp_continuous continuous_subtype_val
      (fun z => b.ball_subset z.property)).subtype_mk _ }
  have hsmallF : ∀ z, ‖(beltBallCoordinates d b.radius F z).2‖ < 1 := by
    intro z
    rw [beltBallCoordinates_normal]
    exact hsmall z.val (b.ball_subset z.property)
  have hne : ∀ u, (beltBallCoordinates d b.radius F
      (parameterBallBoundary b.radius b.radius_pos u)).2 ≠ 0 := by
    intro u
    rw [beltBallCoordinates_normal]
    exact smul_ne_zero (inv_ne_zero d.radius_pos.ne') (b.map u).property
  let J := beltBallBoundaryInComplement d b.radius b.radius_pos F hsmallF hne
  have hJ : ∀ u, (J u).val = g (b.radius • u.val) := by
    intro u
    exact beltBallBoundaryInComplement_coe d b.radius b.radius_pos F hsmallF hne u
  let v := (beltBallCoordinates d b.radius F (parameterBallCenter b.radius b.radius_pos)).1
  have hH := beltBallBoundary_homotopic_meridian d b.radius b.radius_pos F hsmallF hne r hr hr1
  have heq : (PuncturedBall.toSphere 1).comp
      (beltBallBoundaryNormal d b.radius b.radius_pos F hsmallF hne) = b.normalizedMap := by
    apply ContinuousMap.ext
    intro u
    apply Subtype.ext
    exact beltBallBoundary_normalized_coe d b.radius b.radius_pos F hsmallF hne u
  rw [heq] at hH
  exact ⟨J, hJ, v, hH⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
