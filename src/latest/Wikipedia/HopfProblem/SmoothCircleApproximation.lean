import Mathlib.Geometry.Manifold.SmoothApprox
import Wikipedia.HopfProblem.StandardSixSphereCircleModelSmoothFunctions

/-!
# Relative smoothing of genuine circle-valued phases

A continuous unit-complex-valued function can be smoothed without changing
it on a closed set near which it is already smooth. The intermediate complex
approximation never vanishes, and literal radial normalization gives the
smooth unit-valued map. The atlas on the source is unchanged.

This generic statement does not assert equivariance of the approximation.
In particular, it does not by itself preserve a prescribed circle action.
-/

noncomputable section

open Set
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.SmoothCircleApproximation

/-- Literal radial normalization in the original complex plane. -/
def normalize (z : ℂ) : ℂ := ‖z‖⁻¹ • z

theorem norm_normalize {z : ℂ} (hz : z ≠ 0) : ‖normalize z‖ = 1 := by
  rw [normalize, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg z),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]

theorem normalize_eq_self {z : ℂ} (hz : ‖z‖ = 1) : normalize z = z := by
  simp only [normalize, hz, inv_one, one_smul]

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- A relative smooth approximation stays inside the nonzero complex plane at every point. -/
theorem exists_nonzero_smooth_approx_and_eqOn {f : M → ℂ}
    (hf : Continuous f) (hunit : ∀ x, ‖f x‖ = 1)
    {S U : Set M} (hS : IsClosed S) (hU : U ∈ 𝓝ˢ S)
    (hfs : ContMDiffOn I 𝓘(ℝ, ℂ) ∞ f U) :
    ∃ g : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯,
      (∀ x, dist (g x) (f x) < (1 / 2 : ℝ)) ∧
        (∀ x, g x ≠ 0) ∧ EqOn g f S := by
  obtain ⟨g, hg, heq, _⟩ := hf.exists_contMDiff_approx_and_eqOn I (⊤ : ℕ∞)
    (ε := fun _ => (1 / 2 : ℝ)) continuous_const (fun _ => by norm_num) hS hU hfs
  refine ⟨g, hg, ?_, heq⟩
  intro x hx
  have h := hg x
  rw [hx, dist_zero_left, hunit x] at h
  norm_num at h

/-- Relative smoothing into the actual unit complex circle, expressed by its ambient map. -/
theorem exists_smooth_unit_and_eqOn {f : M → ℂ}
    (hf : Continuous f) (hunit : ∀ x, ‖f x‖ = 1)
    {S U : Set M} (hS : IsClosed S) (hU : U ∈ 𝓝ˢ S)
    (hfs : ContMDiffOn I 𝓘(ℝ, ℂ) ∞ f U) :
    ∃ g : M → ℂ, ContMDiff I 𝓘(ℝ, ℂ) ∞ g ∧
      (∀ x, ‖g x‖ = 1) ∧ EqOn g f S := by
  obtain ⟨g, _, hne, heq⟩ := exists_nonzero_smooth_approx_and_eqOn I hf hunit hS hU hfs
  refine ⟨fun x => normalize (g x), ?_, fun x => norm_normalize (hne x), ?_⟩
  · exact StandardSixSphereCircleModel.contMDiff_normalize_of_ne_zero g.contMDiff hne
  · intro x hx
    change normalize (g x) = f x
    rw [heq hx]
    exact normalize_eq_self (hunit x)

end Wikipedia.HopfProblem.SmoothCircleApproximation
