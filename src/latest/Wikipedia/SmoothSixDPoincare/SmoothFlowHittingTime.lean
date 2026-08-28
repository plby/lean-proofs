import Wikipedia.SmoothSixDPoincare.ManifoldImplicitSelection
import Wikipedia.SmoothSixDPoincare.SmoothCompactFlow
import Wikipedia.SmoothSixDPoincare.RegularBandFlow

/-!
# Smoothness of the original transverse level-hitting times

The initial point can be a smooth map from another native manifold, such as
an actual regular level. A continuous hitting-time function is smooth where
the height derivative at the hit is nonzero. The resulting endpoint map
uses the same time function and the same original flow.
-/

noncomputable section

open Set Manifold Filter Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  {D X : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
  [TopologicalSpace X] [ChartedSpace D X] [IsManifold 𝓘(ℝ, D) ∞ X]
  {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  (hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
    (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
  (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) v)
  {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

include hv hcurve hf

theorem contMDiffWithinAt_flowHittingTime {a : X → M} {τ : X → ℝ} {S : Set X} {x : X}
    (ha : ContMDiffAt 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ a x) (hτ : ContinuousWithinAt τ S x)
    (heq : ∀ᶠ y in 𝓝[S] x, f (F (τ y) (a y)) = f (F (τ x) (a x)))
    (htrans : mvfderiv 𝓘(ℝ, E) f (F (τ x) (a x)) (v (F (τ x) (a x))) ≠ 0) :
    ContMDiffWithinAt 𝓘(ℝ, D) 𝓘(ℝ, ℝ) ∞ τ S x := by
  have hparam : ContMDiffAt (𝓘(ℝ, D).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
      (fun q : X × ℝ => (q.2, a q.1)) (x, τ x) :=
    contMDiffAt_snd.prodMk (ha.comp (x, τ x) contMDiffAt_fst)
  have hheight : ContMDiffAt (𝓘(ℝ, D).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun q : X × ℝ => f (F q.2 (a q.1))) (x, τ x) :=
    hf.contMDiffAt.comp (x, τ x)
      ((contMDiff_of_isMIntegralCurves hv F hcurve).contMDiffAt.comp (x, τ x) hparam)
  exact FunctionSpaceCalculus.contMDiffWithinAt_scalarImplicitSelection hheight
    (hasDerivAt_comp_integralCurve hf (hcurve (a x)) (τ x)) htrans hτ heq

theorem contMDiffOn_flowHittingTime {a : X → M} {τ : X → ℝ} {S : Set X} {b : ℝ}
    (ha : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ a) (hτ : ContinuousOn τ S)
    (hroot : ∀ x ∈ S, f (F (τ x) (a x)) = b)
    (htrans : ∀ x ∈ S, mvfderiv 𝓘(ℝ, E) f (F (τ x) (a x)) (v (F (τ x) (a x))) ≠ 0) :
    ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, ℝ) ∞ τ S := by
  intro x hx
  apply contMDiffWithinAt_flowHittingTime hv F hcurve hf (ha x) (hτ x hx) _ (htrans x hx)
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (hroot y hy).trans (hroot x hx).symm

theorem contMDiffOn_flowHittingPoint {a : X → M} {τ : X → ℝ} {S : Set X} {b : ℝ}
    (ha : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ a) (hτ : ContinuousOn τ S)
    (hroot : ∀ x ∈ S, f (F (τ x) (a x)) = b)
    (htrans : ∀ x ∈ S, mvfderiv 𝓘(ℝ, E) f (F (τ x) (a x)) (v (F (τ x) (a x))) ≠ 0) :
    ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ (fun x => F (τ x) (a x)) S :=
  (contMDiff_of_isMIntegralCurves hv F hcurve).comp_contMDiffOn
    ((contMDiffOn_flowHittingTime hv F hcurve hf ha hτ hroot htrans).prodMk ha.contMDiffOn)

end Wikipedia.SmoothSixDPoincare.FlowConstruction
