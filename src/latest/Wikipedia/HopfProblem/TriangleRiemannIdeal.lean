import Wikipedia.HopfProblem.TriangleRiemannBoundary
import Wikipedia.HopfProblem.RiemannBoundaryIdeal

/-!
# Conformal extension at the actual triangle's ideal vertex

The high part of the half-Ford triangle is the vertical half-strip of width
`width / 2`. Its logarithmic parameter therefore has scale `width / (2π)`.
The actual triangle Riemann map extends analytically and noncritically to
parameter zero, with no assumed cusp boundary value.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology ComplexConjugate

namespace Wikipedia.HopfProblem.RiemannMapping

open SpecialPeriods.Triangle RiemannBoundary

/-- The scale of the inverse exponential coordinate of the actual
half-Ford triangle. -/
def triangleCuspScale : ℝ := width / (2 * Real.pi)

theorem triangleCuspScale_pos : 0 < triangleCuspScale := by
  exact div_pos width_pos (mul_pos (by norm_num) Real.pi_pos)

theorem triangleCuspScale_endpoint : stripLeft + triangleCuspScale * Real.pi = -1 / 2 := by
  unfold stripLeft triangleCuspScale
  field_simp [Real.pi_ne_zero]
  ring

/-- The actual logarithmic coordinate approaching the ideal vertex. -/
def triangleCuspLog : ℂ → ℂ := logHalfStrip stripLeft triangleCuspScale

theorem triangle_high_halfStrip_mem (z : ℂ)
    (hl : stripLeft < z.re) (hr : z.re < stripLeft + triangleCuspScale * Real.pi)
    (hi : 1 < z.im) : z ∈ triangleInterior := by
  rw [mem_triangleInterior_iff_epigraph]
  exact ⟨hl, by simpa only [triangleCuspScale_endpoint] using hr,
    (boundaryHeight_le_one z.re).trans_lt hi⟩

theorem triangle_high_halfStrip_edge_notMem (z : ℂ)
    (he : z.re = stripLeft ∨ z.re = stripLeft + triangleCuspScale * Real.pi) :
    z ∉ triangleInterior := by
  intro hz
  rcases he with hl | hr
  · exact (lt_irrefl stripLeft) (hl ▸ hz.1)
  · rw [triangleCuspScale_endpoint] at hr
    exact (lt_irrefl (-1 / 2 : ℝ)) (hr ▸ hz.2.1)

/-- The genuine triangle uniformization extends conformally through its
ideal vertex in the actual logarithmic cusp parameter. All hypotheses on
the triangle and its uniformization are discharged. -/
theorem exists_triangleMap_extension_ideal_vertex :
    ∃ r > 0, ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (ball (0 : ℂ) r) ∧
      EqOn H (triangleMap ∘ triangleCuspLog)
        (ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
      EqOn H (fun z => (conj (triangleMap (triangleCuspLog (conj z))))⁻¹)
        (ball (0 : ℂ) r ∩ {z : ℂ | z.im < 0}) ∧
      (∀ t : ℝ, (t : ℂ) ∈ ball (0 : ℂ) r → ‖H (t : ℂ)‖ = 1) ∧
      HasStrictDerivAt H (deriv H 0) 0 ∧ deriv H 0 ≠ 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), ‖H z‖ < 1 ↔ 0 < z.im := by
  exact exists_conformal_extension_discHomeomorph_at_ideal_vertex
    triangleBiholomorph.toHomeomorph triangleMap_biholomorph triangleMap_differentiable
    stripLeft 1 triangleCuspScale_pos triangle_high_halfStrip_mem
    (fun z _ he => triangle_high_halfStrip_edge_notMem z he)

end Wikipedia.HopfProblem.RiemannMapping
