import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Detecting smoothness through a local diffeomorphism

Precomposition with a local diffeomorphism reflects smoothness at the point.
The proof uses its actual local inverse and the verified local inverse identities.
-/

open scoped Manifold ContDiff Topology
open Filter

namespace NoExoticSixSphere

variable {B H X C H' Y D H'' Z : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace X] [ChartedSpace H X]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace Y] [ChartedSpace H' Y]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ D H''} [TopologicalSpace Z] [ChartedSpace H'' Z]

theorem contMDiffAt_comp_localDiffeomorph_iff {f : X → Y} {x : X}
    (hf : IsLocalDiffeomorphAt I J ∞ f x) (g : Y → Z) :
    ContMDiffAt I K ∞ (g ∘ f) x ↔ ContMDiffAt J K ∞ g (f x) := by
  constructor
  · intro hgf
    have h := hgf.comp_of_eq hf.localInverse_contMDiffAt
      (hf.localInverse_left_inv hf.localInverse_mem_target)
    have heq : g =ᶠ[𝓝 (f x)] ((g ∘ f) ∘ hf.localInverse) := by
      filter_upwards [hf.localInverse_eventuallyEq_right] with y hy
      exact (congrArg g hy).symm
    exact h.congr_of_eventuallyEq heq
  · intro hg
    exact hg.comp x hf.contMDiffAt

theorem contMDiffAt_localDiffeomorph_comp_iff {f : Y → Z} {g : X → Y} {x : X}
    (hf : IsLocalDiffeomorphAt J K ∞ f (g x)) (hg : ContinuousAt g x) :
    ContMDiffAt I K ∞ (f ∘ g) x ↔ ContMDiffAt I J ∞ g x := by
  constructor
  · intro hfg
    have h := hf.localInverse_contMDiffAt.comp x hfg
    apply h.congr_of_eventuallyEq
    filter_upwards [hf.localInverse_eventuallyEq_left.comp_tendsto hg] with y hy
    exact hy.symm
  · intro h
    exact hf.contMDiffAt.comp x h

end NoExoticSixSphere
