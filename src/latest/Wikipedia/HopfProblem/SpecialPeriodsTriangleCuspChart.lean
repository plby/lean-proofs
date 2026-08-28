import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspImage
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspEscape
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspChartRadius
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Filling the actual cusp chart

The exponential chart on the full quotient cusp image extends over the
actual added point of its one-point compactification.  Both continuity
statements at the added point follow from the proved cusp-neighborhood
basis and the exact relation between height and exponential radius.

This file constructs a topological open partial homeomorphism.  It does
not assume a complex atlas on the compactification.
-/

noncomputable section

open Function Set Filter Topology
open scoped OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The cusp coordinate, extended by zero outside its chart source. -/
def cuspFullForward (Y : ℝ) (hY : width ≤ Y) : TriangleCompactifiedOrbitSpace → ℂ := by
  classical
  exact OnePoint.rec 0 (fun q : TriangleOrbitSpace =>
    if hq : q ∈ cuspImage Y then (cuspImageHomeomorph Y hY ⟨q, hq⟩ : ℂ) else 0)

@[simp] theorem cuspFullForward_cuspPoint (Y : ℝ) (hY : width ≤ Y) :
    cuspFullForward Y hY triangleCuspPoint = 0 := rfl

theorem cuspFullForward_openInclusion (Y : ℝ) (hY : width ≤ Y)
    (q : TriangleOrbitSpace) (hq : q ∈ cuspImage Y) :
    cuspFullForward Y hY (triangleOpenInclusion q) =
      (cuspImageHomeomorph Y hY ⟨q, hq⟩ : ℂ) := by
  classical
  change (if h : q ∈ cuspImage Y then (cuspImageHomeomorph Y hY ⟨q, h⟩ : ℂ) else 0) = _
  rw [dif_pos hq]

/-- The inverse cusp coordinate, extended by the added point outside the
punctured chart target.  In particular zero maps to the cusp point. -/
def cuspFullInverse (Y : ℝ) (hY : width ≤ Y) : ℂ → TriangleCompactifiedOrbitSpace := by
  classical
  exact fun z => if hz : z ∈ puncturedCuspBall Y then
    triangleOpenInclusion ((cuspImageHomeomorph Y hY).symm ⟨z, hz⟩ : TriangleOrbitSpace)
    else triangleCuspPoint

@[simp] theorem cuspFullInverse_zero (Y : ℝ) (hY : width ≤ Y) :
    cuspFullInverse Y hY 0 = triangleCuspPoint := by
  classical
  simp [cuspFullInverse]

theorem cuspFullInverse_of_mem (Y : ℝ) (hY : width ≤ Y)
    (z : ℂ) (hz : z ∈ puncturedCuspBall Y) :
    cuspFullInverse Y hY z =
      triangleOpenInclusion ((cuspImageHomeomorph Y hY).symm ⟨z, hz⟩ : TriangleOrbitSpace) := by
  classical
  simp [cuspFullInverse, hz]

theorem cuspFullInverse_of_not_mem (Y : ℝ) (hY : width ≤ Y)
    (z : ℂ) (hz : z ∉ puncturedCuspBall Y) :
    cuspFullInverse Y hY z = triangleCuspPoint := by
  classical
  simp [cuspFullInverse, hz]

theorem cuspFullForward_continuousAt_openInclusion (Y : ℝ) (hY : width ≤ Y)
    (q : TriangleOrbitSpace) (hq : q ∈ cuspImage Y) :
    ContinuousAt (cuspFullForward Y hY) (triangleOpenInclusion q) := by
  apply OnePoint.continuousAt_coe.mpr
  have hc : ContinuousOn
      (fun q : TriangleOrbitSpace => cuspFullForward Y hY (triangleOpenInclusion q))
      (cuspImage Y : Set TriangleOrbitSpace) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun q : cuspImage Y => cuspFullForward Y hY (triangleOpenInclusion q))
    have he : (fun q : cuspImage Y => cuspFullForward Y hY (triangleOpenInclusion q)) =
        (fun q : cuspImage Y => (cuspImageHomeomorph Y hY q : ℂ)) := by
      funext q
      exact cuspFullForward_openInclusion Y hY q q.property
    rw [he]
    exact continuous_subtype_val.comp (cuspImageHomeomorph Y hY).continuous
  exact hc.continuousAt ((cuspImage Y).isOpen.mem_nhds hq)

/-- Continuity at the added point uses genuinely arbitrarily high cusp
neighborhoods and arbitrarily small exponential radii. -/
theorem cuspFullForward_continuousAt_cuspPoint (Y : ℝ) (hY : width ≤ Y) :
    ContinuousAt (cuspFullForward Y hY) triangleCuspPoint := by
  change Tendsto (cuspFullForward Y hY) (𝓝 triangleCuspPoint) (𝓝 (0 : ℂ))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨Z, hYZ, _, hZε⟩ := exists_high_cuspRadius_lt Y hε
  filter_upwards [cuspNeighborhood_mem_nhds Z] with x hx
  induction x using OnePoint.rec
  · change dist (0 : ℂ) 0 < ε
    simpa only [dist_self] using hε
  · rename_i q
    have hqZ : q ∈ cuspImage Z := (openInclusion_mem_cuspNeighborhood Z q).mp hx
    have hqY : q ∈ cuspImage Y := cuspImage_antitone hYZ hqZ
    have hn := (cuspImageHomeomorph_norm_lt_iff Y Z hY hYZ ⟨q, hqY⟩).mpr hqZ
    change dist (cuspFullForward Y hY (triangleOpenInclusion q)) 0 < ε
    rw [cuspFullForward_openInclusion Y hY q hqY, dist_zero_right]
    exact hn.trans hZε

theorem cuspFullForward_continuousOn (Y : ℝ) (hY : width ≤ Y) :
    ContinuousOn (cuspFullForward Y hY)
      (cuspNeighborhood Y : Set TriangleCompactifiedOrbitSpace) := by
  intro x hx
  induction x using OnePoint.rec
  · exact (cuspFullForward_continuousAt_cuspPoint Y hY).continuousWithinAt
  · rename_i q
    exact (cuspFullForward_continuousAt_openInclusion Y hY q
      ((openInclusion_mem_cuspNeighborhood Y q).mp hx)).continuousWithinAt

theorem cuspFullInverse_continuousAt_of_mem (Y : ℝ) (hY : width ≤ Y)
    (z : ℂ) (hz : z ∈ puncturedCuspBall Y) : ContinuousAt (cuspFullInverse Y hY) z := by
  have hc : ContinuousOn (cuspFullInverse Y hY) (puncturedCuspBall Y : Set ℂ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun z : puncturedCuspBall Y => cuspFullInverse Y hY z)
    have he : (fun z : puncturedCuspBall Y => cuspFullInverse Y hY z) =
        (fun z : puncturedCuspBall Y =>
          triangleOpenInclusion ((cuspImageHomeomorph Y hY).symm z : TriangleOrbitSpace)) := by
      funext z
      exact cuspFullInverse_of_mem Y hY z z.property
    rw [he]
    exact triangleOpenInclusion_isOpenEmbedding.continuous.comp
      (continuous_subtype_val.comp (cuspImageHomeomorph Y hY).symm.continuous)
  exact hc.continuousAt ((puncturedCuspBall Y).isOpen.mem_nhds hz)

/-- Conversely, a sufficiently small coordinate ball lies in every
prescribed actual cusp neighborhood. -/
theorem cuspFullInverse_continuousAt_zero (Y : ℝ) (hY : width ≤ Y) :
    ContinuousAt (cuspFullInverse Y hY) 0 := by
  classical
  change Tendsto (cuspFullInverse Y hY) (𝓝 (0 : ℂ))
    (𝓝 (cuspFullInverse Y hY 0))
  rw [cuspFullInverse_zero, cuspNeighborhood_basis.tendsto_right_iff]
  intro Z _
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (cuspRadius_pos (max Y Z))] with z hz
  by_cases hp : z ∈ puncturedCuspBall Y
  · rw [cuspFullInverse_of_mem Y hY z hp]
    apply (openInclusion_mem_cuspNeighborhood Z _).mpr
    apply cuspImage_antitone (le_max_right Y Z)
    apply (cuspImageHomeomorph_norm_lt_iff Y (max Y Z) hY (le_max_left Y Z)
      ((cuspImageHomeomorph Y hY).symm ⟨z, hp⟩)).mp
    simpa using hz
  · rw [cuspFullInverse_of_not_mem Y hY z hp]
    exact cuspPoint_mem_cuspNeighborhood Z

theorem cuspFullInverse_continuousOn (Y : ℝ) (hY : width ≤ Y) :
    ContinuousOn (cuspFullInverse Y hY) (Metric.ball (0 : ℂ) (cuspRadius Y)) := by
  classical
  intro z hz
  by_cases h0 : z = 0
  · subst z
    exact (cuspFullInverse_continuousAt_zero Y hY).continuousWithinAt
  · exact (cuspFullInverse_continuousAt_of_mem Y hY z
      ⟨h0, by simpa using hz⟩).continuousWithinAt

/-- The actual filled cusp chart in the one-point compactification. -/
def cuspFullChart (Y : ℝ) (hY : width ≤ Y) :
    OpenPartialHomeomorph TriangleCompactifiedOrbitSpace ℂ := by
  classical
  exact {
    toFun := cuspFullForward Y hY
    invFun := cuspFullInverse Y hY
    source := cuspNeighborhood Y
    target := Metric.ball 0 (cuspRadius Y)
    map_source' := by
      intro x hx
      induction x using OnePoint.rec
      · change (0 : ℂ) ∈ Metric.ball 0 (cuspRadius Y)
        simpa only [Metric.mem_ball, dist_self] using cuspRadius_pos Y
      · rename_i q
        have hq : q ∈ cuspImage Y := (openInclusion_mem_cuspNeighborhood Y q).mp hx
        change cuspFullForward Y hY (triangleOpenInclusion q) ∈ Metric.ball 0 (cuspRadius Y)
        rw [cuspFullForward_openInclusion Y hY q hq]
        simpa using (cuspImageHomeomorph Y hY ⟨q, hq⟩).property.2
    map_target' := by
      intro z _
      by_cases hz : z ∈ puncturedCuspBall Y
      · rw [cuspFullInverse_of_mem Y hY z hz]
        exact (openInclusion_mem_cuspNeighborhood Y _).mpr
          ((cuspImageHomeomorph Y hY).symm ⟨z, hz⟩).property
      · rw [cuspFullInverse_of_not_mem Y hY z hz]
        exact cuspPoint_mem_cuspNeighborhood Y
    left_inv' := by
      intro x hx
      induction x using OnePoint.rec
      · exact cuspFullInverse_zero Y hY
      · rename_i q
        have hq : q ∈ cuspImage Y := (openInclusion_mem_cuspNeighborhood Y q).mp hx
        change cuspFullInverse Y hY (cuspFullForward Y hY (triangleOpenInclusion q)) =
          triangleOpenInclusion q
        rw [cuspFullForward_openInclusion Y hY q hq]
        rw [cuspFullInverse_of_mem Y hY _ (cuspImageHomeomorph Y hY ⟨q, hq⟩).property]
        change triangleOpenInclusion
          ((cuspImageHomeomorph Y hY).symm (cuspImageHomeomorph Y hY ⟨q, hq⟩)) = _
        rw [Homeomorph.symm_apply_apply]
    right_inv' := by
      intro z hz
      by_cases h0 : z = 0
      · subst z
        rw [cuspFullInverse_zero, cuspFullForward_cuspPoint]
      · have hp : z ∈ puncturedCuspBall Y := ⟨h0, by simpa using hz⟩
        rw [cuspFullInverse_of_mem Y hY z hp]
        rw [cuspFullForward_openInclusion Y hY _
          ((cuspImageHomeomorph Y hY).symm ⟨z, hp⟩).property]
        exact congrArg Subtype.val ((cuspImageHomeomorph Y hY).apply_symm_apply ⟨z, hp⟩)
    open_source := (cuspNeighborhood Y).isOpen
    open_target := Metric.isOpen_ball
    continuousOn_toFun := cuspFullForward_continuousOn Y hY
    continuousOn_invFun := cuspFullInverse_continuousOn Y hY }

@[simp] theorem cuspFullChart_source (Y : ℝ) (hY : width ≤ Y) :
    (cuspFullChart Y hY).source = (cuspNeighborhood Y : Set TriangleCompactifiedOrbitSpace) := rfl

@[simp] theorem cuspFullChart_target (Y : ℝ) (hY : width ≤ Y) :
    (cuspFullChart Y hY).target = Metric.ball 0 (cuspRadius Y) := rfl

@[simp] theorem cuspFullChart_cuspPoint (Y : ℝ) (hY : width ≤ Y) :
    cuspFullChart Y hY triangleCuspPoint = 0 := rfl

@[simp] theorem cuspFullChart_symm_zero (Y : ℝ) (hY : width ≤ Y) :
    (cuspFullChart Y hY).symm 0 = triangleCuspPoint := cuspFullInverse_zero Y hY

theorem cuspFullChart_openInclusion (Y : ℝ) (hY : width ≤ Y)
    (q : TriangleOrbitSpace) (hq : q ∈ cuspImage Y) :
    cuspFullChart Y hY (triangleOpenInclusion q) =
      (cuspImageHomeomorph Y hY ⟨q, hq⟩ : ℂ) :=
  cuspFullForward_openInclusion Y hY q hq

/-- On every actual high-horodisc representative the filled chart is
the original exponential cusp coordinate. -/
theorem cuspFullChart_mk (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    cuspFullChart Y hY (triangleOpenInclusion (triangleOrbitProjection (z : UpperHalfPlane))) =
      cuspQ (z : UpperHalfPlane) := by
  change cuspFullChart Y hY (triangleOpenInclusion (cuspImageProjection Y z)) = _
  rw [cuspFullChart_openInclusion Y hY _ (cuspImageProjection Y z).property]
  exact cuspImageHomeomorph_mk_coe Y hY z

theorem cuspFullChart_mk_exp (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    cuspFullChart Y hY (triangleOpenInclusion (triangleOrbitProjection (z : UpperHalfPlane))) =
      Complex.exp (2 * Real.pi * Complex.I * (z : UpperHalfPlane) / width) := by
  rw [cuspFullChart_mk, cuspQ_eq_exp]

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
