import Wikipedia.HopfProblem.OrbitPairSupportedFlow

/-!
# Differentiating scalar functions along the supported native flow

The actual integral-curve equation and native chain rule give the ordinary
real derivative of any smooth scalar function along the constructed flow.
This will identify the original clock along trajectories.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.SupportedFlow.Field

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  (v : SupportedFlow.Field (E := E) (M := M))

theorem hasDerivAt_comp (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (x : M) (t : ℝ) :
    HasDerivAt (fun s => f (v.flow s x))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f (v.flow t x) (v.vector (v.flow t x)) : ℝ) t := by
  let p := v.flow t x
  let L : E →L[ℝ] ℝ := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p
  let w : E := v.vector p
  let A : ℝ →L[ℝ] E := (1 : ℝ →L[ℝ] ℝ).smulRight w
  have hdf : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p L :=
    (hf.contMDiffAt.mdifferentiableAt (by simp)).hasMFDerivAt
  have hdγ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s => v.flow s x) t A :=
    (v.integralCurve x).isMIntegralCurveAt t |>.hasMFDerivAt
  have hm : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => f (v.flow s x)) t (L.comp A) :=
    hdf.comp t hdγ
  have hfder : HasFDerivAt (fun s => f (v.flow s x)) (L.comp A) t := hm.hasFDerivAt
  have hd : HasDerivAt (fun s => f (v.flow s x)) ((L.comp A) 1) t :=
    hfder.hasDerivAt
  have he : (L.comp A) 1 = L w := by simp [A]
  rw [he] at hd
  exact hd

end Wikipedia.HopfProblem.OrbitPair.SupportedFlow.Field
