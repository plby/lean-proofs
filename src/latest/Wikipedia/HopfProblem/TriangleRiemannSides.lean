import Wikipedia.HopfProblem.TriangleRiemannBoundary

/-!
# The two vertical boundary extensions of the actual Riemann map

These specialize the proved straight-boundary theorem to the explicit
left and right affine coordinates of the half-Ford triangle.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace Wikipedia.HopfProblem.RiemannMapping

open SpecialPeriods.Triangle

theorem exists_triangleMap_extension_left_side {a : ℂ} (ha : a.re = stripLeft)
    (hai : 0 < a.im) (haC : 1 < ‖a + 1‖) :
    ∃ ε > 0, ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (ball (leftBoundaryChart a) ε) ∧
      EqOn H (triangleMap ∘ leftBoundaryChart.symm)
        (ball (leftBoundaryChart a) ε ∩ {z | 0 < z.im}) ∧
      (∀ z ∈ ball (leftBoundaryChart a) ε, z.im = 0 → ‖H z‖ = 1) ∧
      deriv H (leftBoundaryChart a) ≠ 0 := by
  obtain ⟨r, hr, hside⟩ := exists_left_side_neighborhood ha hai haC
  apply exists_triangleMap_extension_in_side_chart
    leftBoundaryChart.toOpenPartialHomeomorph (mem_univ a)
    (fun z _ => leftBoundaryChart_symm_analyticAt z)
  · change (leftBoundaryChart a).im = 0
    simp [ha]
  · exact hr
  · exact hside

theorem exists_triangleMap_extension_right_side {a : ℂ} (ha : a.re = -1 / 2)
    (hai : 0 < a.im) (haC : 1 < ‖a + 1‖) :
    ∃ ε > 0, ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (ball (rightBoundaryChart a) ε) ∧
      EqOn H (triangleMap ∘ rightBoundaryChart.symm)
        (ball (rightBoundaryChart a) ε ∩ {z | 0 < z.im}) ∧
      (∀ z ∈ ball (rightBoundaryChart a) ε, z.im = 0 → ‖H z‖ = 1) ∧
      deriv H (rightBoundaryChart a) ≠ 0 := by
  obtain ⟨r, hr, hside⟩ := exists_right_side_neighborhood ha hai haC
  apply exists_triangleMap_extension_in_side_chart
    rightBoundaryChart.toOpenPartialHomeomorph (mem_univ a)
    (fun z _ => rightBoundaryChart_symm_analyticAt z)
  · change (rightBoundaryChart a).im = 0
    norm_num [rightBoundaryChart_im, ha]
  · exact hr
  · exact hside

end Wikipedia.HopfProblem.RiemannMapping
