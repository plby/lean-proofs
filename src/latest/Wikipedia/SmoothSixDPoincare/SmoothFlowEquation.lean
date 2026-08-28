import Wikipedia.SmoothSixDPoincare.ContinuousCurveIntegral
import Wikipedia.SmoothSixDPoincare.SmoothFunctionComposition
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# The rescaled smooth flow equation on a fixed curve space

The parameters are an initial point and elapsed time. At elapsed time zero,
the partial derivative in the whole-curve variable is the identity, so the
Banach implicit-function theorem applies without any operator-norm inversion
estimate.
-/

noncomputable section

open Set ContinuousMap
open scoped unitInterval ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.FunctionSpaceCalculus

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def flowEquation (v : C(E, E)) (p : (E × ℝ) × C(I, E)) : C(I, E) :=
  p.2 - ContinuousMap.const I p.1.1 - p.1.2 • curveIntegral (v.comp p.2)

theorem flowEquation_zero_time (v : C(E, E)) (x : E) (a : C(I, E)) :
    flowEquation v ((x, 0), a) = a - ContinuousMap.const I x := by
  simp [flowEquation]

theorem flowEquation_base (v : C(E, E)) (x : E) :
    flowEquation v ((x, 0), ContinuousMap.const I x) = 0 := by
  simp [flowEquation_zero_time]

theorem contDiff_flowEquation (v : C(E, E)) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (flowEquation v) := by
  have hconst : ContDiff ℝ ∞
      (fun p : (E × ℝ) × C(I, E) => ContinuousMap.const I p.1.1) :=
    (ContinuousLinearMap.const ℝ I : E →L[ℝ] C(I, E)).contDiff.comp (contDiff_fst.fst)
  have hcomp : ContDiff ℝ ∞
      (fun p : (E × ℝ) × C(I, E) => v.comp p.2) :=
    (contDiff_infty_composition v hv).comp contDiff_snd
  exact (contDiff_snd.sub hconst).sub
    (contDiff_fst.snd.smul ((curveIntegral (E := E)).contDiff.comp hcomp))

theorem flowEquation_partial_derivative (v : C(E, E))
    (hv : ContDiff ℝ ∞ v) (x : E) :
    fderiv ℝ (flowEquation v) ((x, 0), ContinuousMap.const I x) ∘L
      ContinuousLinearMap.inr ℝ (E × ℝ) C(I, E) =
      ContinuousLinearMap.id ℝ C(I, E) := by
  let a : C(I, E) := ContinuousMap.const I x
  have hF := ((contDiff_flowEquation v hv).differentiable (by simp)
    ((x, 0), a)).hasFDerivAt
  have hpair : HasFDerivAt (fun b : C(I, E) => ((x, (0 : ℝ)), b))
      (ContinuousLinearMap.inr ℝ (E × ℝ) C(I, E)) a :=
    (hasFDerivAt_const (x, (0 : ℝ)) a).prodMk (hasFDerivAt_id a)
  have h := hF.comp a hpair
  have hsimple : HasFDerivAt (fun b : C(I, E) => flowEquation v ((x, 0), b))
      (ContinuousLinearMap.id ℝ C(I, E)) a := by
    simpa only [flowEquation_zero_time, a, id_eq] using (hasFDerivAt_id a).sub_const a
  exact h.unique hsimple

theorem flowEquation_partial_invertible (v : C(E, E))
    (hv : ContDiff ℝ ∞ v) (x : E) :
    (fderiv ℝ (flowEquation v) ((x, 0), ContinuousMap.const I x) ∘L
      ContinuousLinearMap.inr ℝ (E × ℝ) C(I, E)).IsInvertible := by
  rw [flowEquation_partial_derivative v hv x]
  exact ⟨ContinuousLinearEquiv.refl ℝ C(I, E), rfl⟩

end Wikipedia.SmoothSixDPoincare.FunctionSpaceCalculus
