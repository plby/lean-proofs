import Wikipedia.SmoothSixDPoincare.MorsePerturbation
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Genuine smooth perturbations supported in a manifold chart

The localized coordinate vector is globally smooth by Mathlib's bump-function
theorem. Pairing it with a parameter yields the actual manifold function
family to which the local Morse perturbation argument will be applied.
-/

noncomputable section

open Set
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldPerturbation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

variable {p : M} (φ : SmoothBumpFunction 𝓘(ℝ, E) p)

def coordinateVector (x : M) : E := φ x • extChartAt 𝓘(ℝ, E) p x

theorem contMDiff_coordinateVector :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (coordinateVector φ) :=
  φ.contMDiff_smul contMDiffOn_extChartAt

def perturb (f : M → ℝ) (a : E) (x : M) : ℝ :=
  f x - MorsePerturbation.dualEquiv a (coordinateVector φ x)

/-- Smooth dependence on both the perturbation parameter and the original manifold point. -/
theorem contMDiff_perturb {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun q : E × M => perturb φ f q.1 q.2) :=
  (hf.comp contMDiff_snd).sub
    ((MorsePerturbation.dualEquiv.contDiff.contMDiff.comp contMDiff_fst).clm_apply
      ((contMDiff_coordinateVector φ).comp contMDiff_snd))

omit [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
@[simp] theorem perturb_zero (f : M → ℝ) : perturb φ f 0 = f := by
  funext x
  simp [perturb]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
theorem perturb_eq_of_zero (f : M → ℝ) (a : E) {x : M} (hx : φ x = 0) :
    perturb φ f a x = f x := by
  simp [perturb, coordinateVector, hx]

omit [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
/-- Near the chart center this is exactly the linear perturbation in actual chart coordinates. -/
theorem perturb_eventuallyEq (f : M → ℝ) (a : E) :
    perturb φ f a =ᶠ[𝓝 p]
      (fun x => f x - MorsePerturbation.dualEquiv a (extChartAt 𝓘(ℝ, E) p x)) := by
  filter_upwards [φ.eventuallyEq_one] with x hx
  change φ x = 1 at hx
  simp [perturb, coordinateVector, hx]

end Wikipedia.SmoothSixDPoincare.ManifoldPerturbation
