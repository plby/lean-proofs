import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransportCurve
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransportRadialSmooth
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Smooth endpoint dependence of radial transport in a fixed chart

A smooth cutoff extends the actual connection coefficient near the compact
radial segment. The resulting globally smooth parameter integral is locally
equal to the original transport, by the tube lemma. Thus the endpoint parameter
is genuinely `C∞`; no global frame or global choice of chart sequence is used.
-/

noncomputable section

open Set Topology MeasureTheory
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport

open HolomorphicCharacterBundle PeriodTorusLineBundleClassificationConnection

local notation "Iℂ" => modelWithCornersSelf ℂ ComplexPlane₂

def radialCurve (x : ComplexPlane₂) (t : ℝ) : ComplexPlane₂ := t • x

theorem radialCurve_contDiff (x : ComplexPlane₂) : ContDiff ℝ ∞ (radialCurve x) :=
  contDiff_id.smul contDiff_const

@[simp] theorem radialCurve_deriv (x : ComplexPlane₂) (t : ℝ) :
    deriv (radialCurve x) t = x := by
  change deriv (fun y : ℝ => y • x) t = x
  have hd (j : Fin 2) : DifferentiableAt ℝ (fun y : ℝ => y • x j) t :=
    ((hasDerivAt_id t).smul_const (x j)).differentiableAt
  calc
    deriv (fun y : ℝ => y • x) t = (fun j => deriv (fun y : ℝ => y • x j) t) :=
      deriv_pi hd
    _ = x := by
      funext j
      simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const (x j)).deriv

variable {ι : Type*} (A : TransitionData ComplexPlane₂ ι)

theorem curveCoefficient_radial (i : ι) (x : ComplexPlane₂) (t : ℝ) :
    curveCoefficient A i (radialCurve x) t = connectionForm A i (t • x) x := by
  simp only [curveCoefficient, radialCurve_deriv, radialCurve]

/-- Exponential transport along `t ↦ t • x`, with the endpoint as parameter. -/
def radialTransport (i : ι) (a b : ℝ) (x : ComplexPlane₂) : ℂ :=
  connectionTransport A i (radialCurve x) a b

theorem radialTransport_eq_exp_integral (i : ι) (a b : ℝ) (x : ComplexPlane₂) :
    radialTransport A i a b x =
      Complex.exp (-(∫ t in a..b, connectionForm A i (t • x) x)) := by
  simp only [radialTransport, connectionTransport, scalarTransport, curveCoefficient_radial]

variable [A.IsHolomorphic Iℂ]

/-- On a fixed interval whose radial image lies in one actual chart, scalar
transport depends smoothly on the radial endpoint in a full neighborhood. -/
theorem radialTransport_contDiffAt (i : ι) (a b : ℝ) (x₀ : ComplexPlane₂)
    (hchart : MapsTo (radialCurve x₀) (uIcc a b) (A.baseSet i)) :
    ContDiffAt ℝ ∞ (radialTransport A i a b) x₀ := by
  have h := contDiffAt_radial_integral (connectionForm A i)
    (A.isOpen_baseSet i) (connectionForm_contDiffOn A i) a b x₀ hchart
  have heq : radialTransport A i a b =
      (fun x => Complex.exp (-(∫ t in a..b, connectionForm A i (t • x) x))) :=
    funext (radialTransport_eq_exp_integral A i a b)
  rw [heq]
  exact h.neg.cexp

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport
