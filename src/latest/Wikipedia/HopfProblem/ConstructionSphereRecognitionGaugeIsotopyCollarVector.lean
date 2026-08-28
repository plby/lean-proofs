import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyAngular
import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyNative
import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyGaugeSmooth
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusPolar

/-!
# The actual smooth vector on the elliptic collar

The full native logarithmic correction is extended radially, without
changing its angular monodromy.  At every original radius-and-phase
boundary representative it agrees with the exact boundary translation.
It vanishes identically near the actual cap core and outside an explicit
outer radius.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy

open Elliptic SpecialPeriods CuspUniformization ThreefoldOverlapMappingTorus

local notation "AC" => ThreefoldOverlapMappingTorus.Circle

private theorem logarithm_positive_re {a : ℝ} (ha : 0 < a) :
    (logarithm (a : ℂ)).re = 0 := by
  rw [logarithm, ← Complex.ofReal_log ha.le]
  simp [Complex.div_re, Complex.mul_re, Complex.mul_im]

/-- A literal logarithm of the original radius-and-phase root. -/
theorem polarRoot_exponential (n : ℕ) (r : ℝ) (a : Radius n r) (t : ℝ) :
    exponential (logarithm ((a : ℝ) : ℂ) + (t : ℂ)) =
      (root n r a (t : AC) : ℂ) := by
  have ha : (((a : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast a.property.1.ne'
  rw [exponential_add, exponential_logarithm ha]
  change ((a : ℝ) : ℂ) * exponential (t : ℂ) = (a : ℝ) • (phase (t : AC) : ℂ)
  rw [phase_real, Complex.real_smul]

/-- The angular correction retains the exact real time of every original boundary point. -/
theorem angularValue_root (j : Kind) (h : ℝ → RealCoordinates)
    (hp : Function.Periodic h (j.order : ℝ)) (θ r : ℝ)
    (a : Radius j.order r) (t : ℝ) :
    angularValue j h θ (root j.order r a (((t + θ) / j.order : ℝ) : AC)) = h t := by
  rw [← polarRoot_exponential, angularValue_exponential j h hp]
  simp only [Complex.add_re, logarithm_positive_re a.property.1, Complex.ofReal_re, zero_add]
  apply congrArg h
  have hm : (j.order : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt j.order_pos)
  field_simp [hm]
  ring

/-- On an entire radius circle the radial correction is exactly the cutoff
times the original time vector. -/
theorem discCorrection_root (j : Kind) (h : ℝ → RealCoordinates)
    (hp : Function.Periodic h (j.order : ℝ)) (θ r a : ℝ)
    (b : Radius j.order r) (t : ℝ) :
    discCorrection j h θ a (root j.order r b (((t + θ) / j.order : ℝ) : AC)) =
      radialCutoff a ((b : ℝ) ^ 2) • h t := by
  change radialCutoff a (‖(root j.order r b _ : ℂ)‖ ^ 2) • angularValue j h θ _ = _
  rw [root_norm, angularValue_root j h hp]

/-- The original boundary radius lies in the plateau, without rescaling its time coordinate. -/
theorem discCorrection_boundary (j : Kind) (h : ℝ → RealCoordinates)
    (hp : Function.Periodic h (j.order : ℝ)) (θ r : ℝ)
    (a : Radius j.order r) (t : ℝ) :
    discCorrection j h θ a (root j.order r a (((t + θ) / j.order : ℝ) : AC)) = h t := by
  rw [discCorrection_root j h hp, radialCutoff_at_radius_sq a.property.1 a.property.2.1,
    one_smul]

/-- The discrepancy is a genuinely smooth real vector-valued periodic function. -/
theorem correction_contDiff (j : Kind) (τ : ℝ) : ContDiff ℝ ∞ (correction j τ) :=
  (linearGauge_contDiff j j.twist).sub (nativeGaugeRealLift_contDiff j τ)

/-- The concrete collar vector retaining the entire original logarithmic gauge. -/
def collarVector (j : Kind) (τ θ a : ℝ) (z : Disc) : RealCoordinates :=
  discCorrection j (correction j τ) θ a z

/-- Smoothness uses the original open-disc atlas, including the actual centre. -/
theorem collarVector_contMDiff (j : Kind) (τ θ : ℝ) {a : ℝ} (ha : 0 < a) :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ RealCoordinates) ∞
      (collarVector j τ θ a) :=
  discCorrection_contMDiff j (correction j τ) (correction_periodic j τ)
    (correction_contDiff j τ) θ ha

/-- The vector satisfies exactly the native finite-action covariance. -/
theorem collarVector_rotation (j : Kind) (τ θ a : ℝ) (z : Disc) :
    collarVector j τ θ a (familyRotation j z) = flatLinear j (collarVector j τ θ a z) :=
  discCorrection_rotation j (correction j τ) (correction_periodic j τ)
    (correction_forward j τ) θ a z

/-- The actual inner neighborhood of the cap core is fixed by the extension. -/
theorem collarVector_eq_zero_inner (j : Kind) (τ θ a : ℝ) (z : Disc)
    (hz : ‖(z : ℂ)‖ ^ 2 ≤ a ^ 2 / 4) : collarVector j τ θ a z = 0 :=
  radialCorrection_eq_zero j (correction j τ) θ a hz

/-- The extension also vanishes past the explicit outer cutoff radius. -/
theorem collarVector_eq_zero_outer (j : Kind) (τ θ : ℝ) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (z : Disc)
    (hz : (3 + a ^ 2) / 4 ≤ ‖(z : ℂ)‖ ^ 2) : collarVector j τ θ a z = 0 := by
  change radialCutoff a (‖(z : ℂ)‖ ^ 2) • angularValue j (correction j τ) θ z = 0
  rw [radialCutoff_eq_zero_of_ge ha ha1 hz, zero_smul]

/-- Exact equality along every original boundary cylinder, not only up to homotopy. -/
theorem collarVector_boundary (j : Kind) (τ θ r : ℝ)
    (a : Radius j.order r) (t : ℝ) :
    collarVector j τ θ a (root j.order r a (((t + θ) / j.order : ℝ) : AC)) =
      correction j τ t :=
  discCorrection_boundary j (correction j τ) (correction_periodic j τ) θ r a t

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy
