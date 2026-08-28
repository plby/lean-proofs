import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Centered corrections with zero first derivative

Subtract the difference of two sheet maps at their common center. The
correction then vanishes on the entire center line, including outside the
chosen geometric domain. Equal actual first derivatives give a zero first
derivative of this correction.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.SheetCorrection

variable {A F : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def centerProjection : (ℝ × A) →L[ℝ] (ℝ × A) :=
  (ContinuousLinearMap.fst ℝ ℝ A).prod (0 : (ℝ × A) →L[ℝ] A)

theorem centerProjection_apply (p : ℝ × A) : centerProjection p = (p.1, 0) := rfl

def centeredCorrection (R G : (ℝ × A) → F) (p : ℝ × A) : F :=
  (R p - G p) - (R (centerProjection p) - G (centerProjection p))

omit [NormedSpace ℝ F] in
theorem centeredCorrection_zero (R G : (ℝ × A) → F) (s : ℝ) :
    centeredCorrection R G (s, 0) = 0 := by
  simp only [centeredCorrection, centerProjection_apply, sub_self]

omit [NormedSpace ℝ F] in
theorem centeredCorrection_eq_sub {R G : (ℝ × A) → F} {p : ℝ × A}
    (hcenter : R (p.1, 0) = G (p.1, 0)) :
    centeredCorrection R G p = R p - G p := by
  simp only [centeredCorrection, centerProjection_apply, hcenter, sub_self, sub_zero]

theorem contDiffOn_centeredCorrection {R G : (ℝ × A) → F} {D : Set (ℝ × A)}
    (hR : ContDiffOn ℝ ∞ R D) (hG : ContDiffOn ℝ ∞ G D) :
    ContDiffOn ℝ ∞ (centeredCorrection R G) (D ∩ centerProjection ⁻¹' D) :=
  ((hR.sub hG).mono inter_subset_left).sub
    ((hR.sub hG).comp (centerProjection (A := A)).contDiff.contDiffOn (fun _ hp => hp.2))

/-- Matching actual first derivatives give a correction with zero first derivative. -/
theorem hasFDerivAt_centeredCorrection_zero {R G : (ℝ × A) → F}
    {L : (ℝ × A) →L[ℝ] F} {s : ℝ}
    (hR : HasFDerivAt R L (s, 0)) (hG : HasFDerivAt G L (s, 0)) :
    HasFDerivAt (centeredCorrection R G) (0 : (ℝ × A) →L[ℝ] F) (s, 0) := by
  have hdiff : HasFDerivAt (fun p => R p - G p) (0 : (ℝ × A) →L[ℝ] F) (s, (0 : A)) := by
    convert hR.sub hG using 1 <;> first | rfl | simp only [sub_self]
  have hcenter := hdiff.comp (s, (0 : A)) (centerProjection (A := A)).hasFDerivAt
  convert hdiff.sub hcenter using 1 <;> first
    | rfl
    | simp only [ContinuousLinearMap.zero_comp, sub_self]

end Wikipedia.SmoothSixDPoincare.SheetCorrection
