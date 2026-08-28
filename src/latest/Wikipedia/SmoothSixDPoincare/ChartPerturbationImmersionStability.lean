import Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
import Wikipedia.SmoothSixDPoincare.ManifoldImmersionStability

/-!
# Compact immersion stability for the original chart-translation family
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ChartMapPerturbation

variable {E G F H N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]

/-- Small chart translations retain injective native derivatives on a compact source set. -/
theorem eventually_perturb_injective_derivative (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)
    {f : E → N} {β : E → ℝ} (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hβ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) {K : Set E} (hK : IsCompact K)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∀ᶠ a : F in 𝓝 0, ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J (perturb c f β a) x) := by
  obtain ⟨δ, hδ, hvalid⟩ := exists_radius_valid c hf hβ hcompact hsupport
  let W : Set (F × E) := {q | ‖q.1‖ < δ}
  have hW : IsOpen W := isOpen_lt continuous_fst.norm continuous_const
  have hfamily : ContMDiffOn (𝓘(ℝ, F).prod 𝓘(ℝ, E)) J ∞
      (fun q : F × E => perturb c f β q.1 q.2) W := by
    intro q hq
    exact (contMDiffAt_perturb c hf hβ hsupport q (hvalid q.1 hq)).contMDiffWithinAt
  apply ManifoldImmersion.eventually_injective_nativeDerivative hW hfamily hK
  · intro x _
    change ‖(0 : F)‖ < δ
    simpa only [norm_zero] using hδ
  · intro x hx
    have heq : perturb c f β (0 : F) = f := funext (perturb_zero c f β)
    change Function.Injective (mfderiv 𝓘(ℝ, E) J (perturb c f β (0 : F)) x)
    rw [heq]
    exact hinj x hx

end Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
