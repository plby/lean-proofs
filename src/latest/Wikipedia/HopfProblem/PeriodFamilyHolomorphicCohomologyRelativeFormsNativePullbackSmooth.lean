import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsNativePullbackCoordinates
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smoothness of genuine native cotangent pullback

Smoothness is proved in the actual Hom-bundle coordinates, using the
genuine manifold derivative theorem and the original tangent transition
maps. No smoothness of the untrivialized covector values is assumed.
-/

noncomputable section

open Bundle TopologicalSpace Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native

open HolomorphicDolbeaultThree

variable (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (M N : Type) [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
/-- The actual full-open lift of a smooth map is smooth in the inherited charts. -/
theorem toTop_contMDiff (f : M → N) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (toTop f) :=
  (ContMDiff.subtypeVal_comp_iff (⊤ : Opens N) (toTop f)).mp hf

/-- Pullback by a genuinely smooth map preserves actual smooth native
cotangent sections. The target is the unchanged source Hom bundle. -/
theorem realPullback_smooth (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (a : ∀ y : (⊤ : Opens N), Forms.Covector F N (y : N))
    (ha : ContMDiff 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F →L[ℝ] ℂ)) ∞
      (Forms.sectionMap F N a)) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (Forms.sectionMap E M (realPullback E F M N f a)) := by
  intro x
  apply (Forms.smoothSectionAt_iff E M (realPullback E F M N f a) x).mpr
  let g : (⊤ : Opens M) → (⊤ : Opens N) := fun y => toTop f (y : M)
  have hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g :=
    (toTop_contMDiff E F M N f hf).comp contMDiff_subtype_val
  have hS : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F →L[ℝ] ℂ) ∞
      (fun y => Forms.inCoordinates F N a (f (x : M)) (g y)) x :=
    ((Forms.smoothSectionAt_iff F N a (g x)).mp (ha (g x))).comp x (hg x)
  have hD₀ := (hf (x : M)).mfderiv_const (m := ∞) (by simp)
  have hD := hD₀.comp x (contMDiff_subtype_val x)
  apply (hS.clm_comp hD).congr_of_eventuallyEq
  have hc : ContinuousAt (fun y : (⊤ : Opens M) => f (y : M)) x :=
    (hf.continuous.comp continuous_subtype_val).continuousAt
  have htarget : ∀ᶠ y : (⊤ : Opens M) in 𝓝 x,
      f (y : M) ∈ (chartAt F (f (x : M))).source :=
    hc.preimage_mem_nhds ((chartAt F (f (x : M))).open_source.mem_nhds
      (mem_chart_source F (f (x : M))))
  filter_upwards [htarget] with y hy
  exact realPullback_inCoordinates E F M N f a (x : M) y hy

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Native
