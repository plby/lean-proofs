import Wikipedia.HopfProblem.PeriodFamily
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Restricting scalars in the original holomorphic charts

Complex differentiability of the actual transition maps implies real
differentiability in precisely the same charted-space structure. The
period-family applications use the original varying-period quotient atlas;
no real-coordinate product atlas is introduced.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Geometry

section SameAtlas

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  (M : Type*) [TopologicalSpace M] [ChartedSpace E M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace F N]

/-- Scalar restriction of the actual complex transition derivatives equips
the unchanged atlas with its real differentiability property. -/
theorem realManifold_of_complex (n : ℕ∞ω) [IsManifold 𝓘(ℂ, E) n M] :
    IsManifold 𝓘(ℝ, E) n M := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  have h := ((contDiffGroupoid n 𝓘(ℂ, E)).compatible he he').1
  simpa only [mfld_simps] using h.restrict_scalars ℝ

/-- Complex differentiability of a map implies real differentiability to
the same order in both original source and target atlases. -/
theorem contMDiffAt_real_of_complex {n : ℕ∞ω} {f : M → N} {x : M}
    (hf : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, F) n f x) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) n f x := by
  obtain ⟨hc, hd⟩ := contMDiffAt_iff.mp hf
  apply contMDiffAt_iff.mpr
  refine ⟨hc, ?_⟩
  simpa only [mfld_simps] using hd.restrict_scalars ℝ

/-- The same scalar restriction for maps on their whole original domains. -/
theorem contMDiff_real_of_complex {n : ℕ∞ω} {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) n f) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) n f :=
  fun _ => contMDiffAt_real_of_complex M (hf _)

end SameAtlas

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

local notation "IR₃" => modelWithCornersSelf ℝ (ℂ × ComplexPlane₂)
local notation "IC₃" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The original varying-period quotient atlas is real differentiable to
every order because its actual transitions are holomorphic. -/
theorem totalSpace_realManifold_of_order (n : ℕ∞ω) :
    letI := P.totalChartedSpace
    IsManifold IR₃ n P.TotalSpace := by
  let := P.totalChartedSpace
  let : IsManifold IC₃ ω P.TotalSpace := P.totalSpace_isManifold
  exact realManifold_of_complex P.TotalSpace n

/-- Real smoothness of the unchanged original total-space atlas. -/
theorem totalSpace_realManifold :
    letI := P.totalChartedSpace
    IsManifold IR₃ ∞ P.TotalSpace :=
  totalSpace_realManifold_of_order P ∞

/-- Every actual total-space open inherits the same real smooth charts. -/
theorem open_realManifold (Ω : Opens P.TotalSpace) :
    letI := P.totalChartedSpace
    IsManifold IR₃ ∞ Ω := by
  let := P.totalChartedSpace
  let : IsManifold IR₃ ∞ P.TotalSpace := totalSpace_realManifold P
  infer_instance

/-- The literal original projection is real smooth in the unchanged atlas. -/
theorem projection_real_smooth :
    letI := P.totalChartedSpace
    ContMDiff IR₃ 𝓘(ℝ, ℂ) ∞ P.projection := by
  let := P.totalChartedSpace
  exact (contMDiff_real_of_complex P.TotalSpace P.projection_holomorphic).of_le
    (show ∞ ≤ ω by simp)

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Geometry
