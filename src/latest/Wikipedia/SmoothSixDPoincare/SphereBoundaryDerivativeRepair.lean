import Wikipedia.SmoothSixDPoincare.SphereBoundaryKernel
import Wikipedia.SmoothSixDPoincare.CompactBoundaryDerivativeRepair

/-!
# Repairing an actual sphere extension without changing its boundary values

The sphere tangent-range theorem supplies the common-kernel hypothesis from
the immersive boundary map. Compact weighted chart repair then makes the
ambient extension immersive at every sphere point, with those values fixed.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SphereBoundary

variable {E G H N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]

/-- Any smooth ambient extension of an immersive sphere map can have all its boundary
derivatives repaired, with the original sphere map fixed pointwise. -/
theorem exists_extension_immersive_on_sphere {f : E → N}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {γ : Metric.sphere (0 : E) 1 → N}
    (hext : ∀ x : Metric.sphere (0 : E) 1, f x.1 = γ x)
    (hγ : ∀ x, Function.Injective (mfderiv (𝓡 n) J γ x))
    (hdim : n + Module.finrank ℝ E < Module.finrank ℝ G) :
    ∃ g : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ g ∧
      (∀ x : Metric.sphere (0 : E) 1, g x.1 = γ x) ∧
      ∀ x : Metric.sphere (0 : E) 1, Function.Injective (mfderiv 𝓘(ℝ, E) J g x.1) := by
  have hb : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ (Subtype.val : Metric.sphere (0 : E) 1 → E) :=
    contMDiff_coe_sphere
  have hzero (x : Metric.sphere (0 : E) 1) : definingFunction x.1 = 0 :=
    (definingFunction_eq_zero_iff x.1).mpr x.property
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) + Module.finrank ℝ E <
      Module.finrank ℝ G := by
    simpa only [finrank_euclideanSpace_fin] using hdim
  obtain ⟨g, hg, hhom, hderiv⟩ := ManifoldImmersion.exists_compact_boundary_derivative_repair
    (⟨f, hf.continuous⟩ : C(E, N)) hf hb contDiff_definingFunction hzero hd
      (common_kernel_of_immersive_sphere_extension hf hext hγ)
  refine ⟨g, hg, ?_, ?_⟩
  · intro x
    exact (hhom.fst_eq_snd (hzero x)).symm.trans (hext x)
  · intro x
    exact hderiv x.1 ⟨x, rfl⟩

end Wikipedia.SmoothSixDPoincare.SphereBoundary
