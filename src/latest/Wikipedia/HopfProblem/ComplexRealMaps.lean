import Wikipedia.HopfProblem.ComplexRealManifold
import Mathlib.Geometry.Manifold.Diffeomorph

/-! # Restriction of scalars for maps between complex manifolds -/

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem

variable {E F M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]

/-- A complex differentiable map is real differentiable in the unchanged charts. -/
theorem complexContMDiff_restrict_real {f : M → N} {n : ℕ∞ω}
    (h : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) n f) : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) n f := by
  intro x
  obtain ⟨hc, hd⟩ := contMDiffAt_iff.mp (h x)
  apply contMDiffAt_iff.mpr
  refine ⟨hc, ?_⟩
  simpa only [mfld_simps] using hd.restrict_scalars ℝ

end Wikipedia.HopfProblem
