import Wikipedia.HopfProblem.DegreeCollapseSmoothBasinWeightBand
import Wikipedia.HopfProblem.DegreeCollapseMorseConstantShift

/-!
# Global native height from the extended stationary weight

Smoothness of the weight is required only in the pair band: full exterior
identity germs of the scalar profiles make the blended function equal to
the original function near every exterior point, including boundary
levels. Exact stationarity supplies the directional derivative globally.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem blended_height_exterior_germ {f θ : M → ℝ} {P Q : ℝ → ℝ} {l u : ℝ}
    (hf : Continuous f)
    (hP : ∀ s ∉ Ioo l u, P =ᶠ[𝓝 s] id)
    (hQ : ∀ s ∉ Ioo l u, Q =ᶠ[𝓝 s] id)
    {x : M} (hx : f x ∉ Ioo l u) :
    (fun y => blendHeight (θ y) P Q (f y)) =ᶠ[𝓝 x] f := by
  filter_upwards [hf.continuousAt.tendsto.eventually (hP _ hx),
    hf.continuousAt.tendsto.eventually (hQ _ hx)] with y hyP hyQ
  exact blendHeight_fixed hyP hyQ _

theorem contMDiff_globally_blended_height {f θ : M → ℝ} {P Q : ℝ → ℝ} {l u : ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hθ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ θ (f ⁻¹' Icc l u))
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q)
    (hPfix : ∀ s ∉ Ioo l u, P =ᶠ[𝓝 s] id)
    (hQfix : ∀ s ∉ Ioo l u, Q =ᶠ[𝓝 s] id) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => blendHeight (θ x) P Q (f x)) := by
  intro x
  by_cases hx : f x ∈ Ioo l u
  · have hnhds : f ⁻¹' Icc l u ∈ 𝓝 x := mem_of_superset
      ((isOpen_Ioo.preimage hf.continuous).mem_nhds hx) (fun _ hy => ⟨hy.1.le, hy.2.le⟩)
    have hw := (hθ x ⟨hx.1.le, hx.2.le⟩).contMDiffAt hnhds
    exact (hw.mul (hP.contMDiff.contMDiffAt.comp x (hf x))).add
      ((contMDiffAt_const.sub hw).mul (hQ.contMDiff.contMDiffAt.comp x (hf x)))
  · exact (hf x).congr_of_eventuallyEq (blended_height_exterior_germ hf.continuous hPfix hQfix hx)

theorem blended_height_one_translation_germ {f θ : M → ℝ} {P Q : ℝ → ℝ} {p : M} {k : ℝ}
    (hf : ContinuousAt f p) (hθ : θ =ᶠ[𝓝 p] fun _ => 1)
    (hP : P =ᶠ[𝓝 (f p)] fun s => s + k) :
    (fun x => blendHeight (θ x) P Q (f x)) =ᶠ[𝓝 p] fun x => f x + k := by
  filter_upwards [hθ, hf.tendsto.eventually hP] with x hx hPx
  rw [hx, blendHeight_one]
  exact hPx

theorem blended_height_zero_translation_germ {f θ : M → ℝ} {P Q : ℝ → ℝ} {p : M} {k : ℝ}
    (hf : ContinuousAt f p) (hθ : θ =ᶠ[𝓝 p] fun _ => 0)
    (hQ : Q =ᶠ[𝓝 (f p)] fun s => s + k) :
    (fun x => blendHeight (θ x) P Q (f x)) =ᶠ[𝓝 p] fun x => f x + k := by
  filter_upwards [hθ, hf.tendsto.eventually hQ] with x hx hQx
  rw [hx, blendHeight_zero]
  exact hQx

theorem blended_height_directional_derivative {f θ : M → ℝ} {P Q : ℝ → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => blendHeight (θ x) P Q (f x)))
    (hP : Differentiable ℝ P) (hQ : Differentiable ℝ Q)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hθ : ∀ x t, θ (F t x) = θ x) (x : M) :
    mvfderiv 𝓘(ℝ, E) (fun y => blendHeight (θ y) P Q (f y)) x (V x) =
      (θ x * deriv P (f x) + (1 - θ x) * deriv Q (f x)) * mvfderiv 𝓘(ℝ, E) f x (V x) := by
  have hw : HasDerivAt (fun t => θ (F t x)) 0 0 := by
    have heq : (fun t => θ (F t x)) = fun _ => θ x := funext (hθ x)
    rw [heq]
    exact hasDerivAt_const _ _
  have hdf := FlowConstruction.hasDerivAt_comp_integralCurve hf (hF x) 0
  have hdg := FlowConstruction.hasDerivAt_comp_integralCurve hg (hF x) 0
  have hh := hasDerivAt_blended_height hdf hw (hP _).hasDerivAt (hQ _).hasDerivAt
  have heq := hdg.unique hh
  have hdf0 := congrArg (fun y : M => mvfderiv 𝓘(ℝ, E) f y (V y)) (F.map_zero_apply x)
  have hdg0 := congrArg (fun y : M =>
    mvfderiv 𝓘(ℝ, E) (fun z => blendHeight (θ z) P Q (f z)) y (V y)) (F.map_zero_apply x)
  change mvfderiv 𝓘(ℝ, E) (fun z => blendHeight (θ z) P Q (f z)) (F 0 x) (V (F 0 x)) =
    (θ (F 0 x) * deriv P (f (F 0 x)) + (1 - θ (F 0 x)) * deriv Q (f (F 0 x))) *
      mvfderiv 𝓘(ℝ, E) f (F 0 x) (V (F 0 x)) at heq
  rw [hdg0, hdf0, F.map_zero_apply] at heq
  exact heq

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
