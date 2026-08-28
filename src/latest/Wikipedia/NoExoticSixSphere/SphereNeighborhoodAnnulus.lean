import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

/-!
# A uniform inner annulus in a neighborhood of the unit sphere

Compactness of the closed ball turns an arbitrary open neighborhood of its
boundary into a single radial collar. The argument also covers an empty
complement of that neighborhood.
-/

open Set Metric

namespace NoExoticSixSphere

theorem exists_annulus_subset_sphere_neighborhood {E : Type*} [NormedAddCommGroup E]
    [ProperSpace E] {U : Set E} (hU : IsOpen U) (hS : sphere (0 : E) 1 ⊆ U) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ closedBall (0 : E) 1 ∩ {x | r ≤ ‖x‖} ⊆ U := by
  let K := closedBall (0 : E) 1 \ U
  have hK : IsCompact K := (isCompact_closedBall (0 : E) 1).diff hU
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
    have hxle : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx.1
    have hxlt : ‖x‖ < 1 := lt_of_le_of_ne hxle (by
      intro heq
      exact hx.2 (hS (by simpa only [mem_sphere, dist_zero_right] using heq)))
    refine ⟨(‖x‖ + 1) / 2, by positivity, by linarith, ?_⟩
    intro y hy
    by_contra hyU
    have hle : ‖y‖ ≤ ‖x‖ := hmax ⟨hy.1, hyU⟩
    have hyr : (‖x‖ + 1) / 2 ≤ ‖y‖ := hy.2
    linarith
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    intro y hy
    by_contra hyU
    exact hne ⟨y, hy.1, hyU⟩

end NoExoticSixSphere
