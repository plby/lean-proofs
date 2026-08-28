import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-! # Radial compression commutes with a linear isometry -/

namespace NoExoticSixSphere

variable {K J : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup J] [NormedSpace ℝ J]

theorem map_univBall_linearIsometry (e : K →ₗᵢ[ℝ] J) (r : ℝ) (hr : 0 < r) (v : K) :
    e (OpenPartialHomeomorph.univBall (0 : K) r v) =
      OpenPartialHomeomorph.univBall (0 : J) r (e v) := by
  rw [OpenPartialHomeomorph.univBall, dif_pos hr,
    OpenPartialHomeomorph.univBall, dif_pos hr]
  change e (r • ((Real.sqrt (1 + ‖v‖ ^ 2))⁻¹ • v) + 0) =
    r • ((Real.sqrt (1 + ‖e v‖ ^ 2))⁻¹ • e v) + 0
  rw [map_add, map_zero, map_smul, map_smul, e.norm_map]

end NoExoticSixSphere
