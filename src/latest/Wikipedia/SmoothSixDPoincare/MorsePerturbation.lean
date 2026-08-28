import Wikipedia.SmoothSixDPoincare.RegularValues
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Small linear perturbations with nondegenerate critical points

For a smooth real-valued function on a finite-dimensional real normed
space, regular values of the coordinate gradient give arbitrarily small linear
perturbations whose critical points all have bijective actual Hessians.
This is a local analytic prerequisite for constructing Morse functions;
it is not a handle cancellation theorem.
-/

noncomputable section

open Set MeasureTheory MeasureTheory.Measure
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.MorsePerturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A basis identifies the space with its continuous dual; no inner product is required. -/
def dualEquiv : E ≃L[ℝ] (E →L[ℝ] ℝ) := by
  classical
  exact ((Module.Basis.ofVectorSpace ℝ E).toDualEquiv.trans
    LinearMap.toContinuousLinearMap).toContinuousLinearEquiv

def coordinateGradient (f : E → ℝ) (x : E) : E := dualEquiv.symm (fderiv ℝ f x)

def linearPerturbation (f : E → ℝ) (a : E) (x : E) : ℝ := f x - dualEquiv a x

/-- Every critical point has a nondegenerate genuine Hessian. -/
def IsMorse (f : E → ℝ) : Prop :=
  ∀ x, fderiv ℝ f x = 0 → Function.Bijective (fderiv ℝ (fderiv ℝ f) x)

omit [FiniteDimensional ℝ E] in
theorem contDiff_fderiv {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)

theorem contDiff_coordinateGradient {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (coordinateGradient f) :=
  dualEquiv.symm.contDiff.comp (contDiff_fderiv hf)

theorem contDiff_linearPerturbation {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (a : E) :
    ContDiff ℝ ∞ (linearPerturbation f a) := hf.sub (dualEquiv a).contDiff

theorem fderiv_linearPerturbation {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (a x : E) :
    fderiv ℝ (linearPerturbation f a) x = fderiv ℝ f x - dualEquiv a := by
  unfold linearPerturbation
  rw [fderiv_fun_sub (hf.differentiable (by simp) x) (dualEquiv a).differentiableAt,
    ContinuousLinearMap.fderiv]

theorem hessian_linearPerturbation {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (a x : E) :
    fderiv ℝ (fderiv ℝ (linearPerturbation f a)) x = fderiv ℝ (fderiv ℝ f) x := by
  have heq : fderiv ℝ (linearPerturbation f a) = fun y => fderiv ℝ f y - dualEquiv a :=
    funext (fderiv_linearPerturbation hf a)
  rw [heq, fderiv_sub_const]

theorem fderiv_coordinateGradient {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) :
    fderiv ℝ (coordinateGradient f) x =
      dualEquiv.symm.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) x) := by
  exact (dualEquiv.symm.hasFDerivAt.comp x
    ((contDiff_fderiv hf).differentiable (by simp) x).hasFDerivAt).fderiv

/-- A regular gradient value produces a Morse linear perturbation. -/
theorem isMorse_of_regularValue {f : E → ℝ} (hf : ContDiff ℝ ∞ f) {a : E}
    (ha : a ∈ RegularValues.regularValues (coordinateGradient f)) :
    IsMorse (linearPerturbation f a) := by
  intro x hx
  rw [fderiv_linearPerturbation hf a x, sub_eq_zero] at hx
  have hxa : coordinateGradient f x = a := by
    simp [coordinateGradient, hx]
  have hbij := RegularValues.bijective_fderiv_of_mem_regularValues ha hxa
  rw [hessian_linearPerturbation hf a x]
  have heq : (fun v : E => dualEquiv (fderiv ℝ (coordinateGradient f) x v)) =
      fderiv ℝ (fderiv ℝ f) x := by
    funext v
    rw [fderiv_coordinateGradient hf x]
    exact dualEquiv.apply_symm_apply _
  rw [← heq]
  exact dualEquiv.bijective.comp hbij

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ]

include μ in
/-- Linear perturbations with nondegenerate critical points can be arbitrarily small. -/
theorem exists_small_morse_perturbation {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : E, ‖a‖ < ε ∧ ContDiff ℝ ∞ (linearPerturbation f a) ∧
      IsMorse (linearPerturbation f a) := by
  have hd := RegularValues.dense_regularValues μ
    ((contDiff_coordinateGradient hf).differentiable (by simp))
  obtain ⟨a, ha, haε⟩ := hd.exists_dist_lt 0 hε
  exact ⟨a, by simpa only [dist_zero_left] using haε,
    contDiff_linearPerturbation hf a, isMorse_of_regularValue hf ha⟩

end Wikipedia.SmoothSixDPoincare.MorsePerturbation
