import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticNativeCurve
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusPolar

/-!
# The original polar boundary at the native logarithmic root

The chosen attaching parameter supplies an allowed root radius and a
literal real phase.  At these values the polar root used by the actual
mapping-torus boundary agrees, for every real time, with the original
positive logarithmic root.  This is an equality of the native disc
points, not merely a homotopy or an endpoint calculation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods Elliptic CuspUniformization
open SpecialPeriods.Threefold SpecialPeriods.Threefold.EllipticGeometry
open SpecialPeriods.EllipticFilling ThreefoldOverlapMappingTorus

local notation "PolarCircle" => ThreefoldOverlapMappingTorus.Circle

/-- Polar decomposition of the normalized complex exponential, with the
real part giving its actual phase without an argument-branch choice. -/
theorem exponential_eq_norm_mul_real (s : ℂ) :
    exponential s = (‖exponential s‖ : ℂ) * exponential (s.re : ℂ) := by
  simp only [exponential]
  rw [Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- The positive native root radius satisfies the original small filling's
power-radius bound. -/
def nativeBoundaryRootRadius (j : Kind) :
    Radius j.order (specialBaseCover.radius (some j)) :=
  ⟨‖exponential (chosenAttachingParameter j)‖,
    norm_pos_iff.mpr (exponential_ne_zero _),
    TauCusp.exponential_norm_lt_one_of_upperHalfPlane (chosenAttachingParameter_im_pos j),
    chosenAttachingParameter_filling_bound j⟩

@[simp] theorem nativeBoundaryRootRadius_coe (j : Kind) :
    (nativeBoundaryRootRadius j : ℝ) = ‖exponential (chosenAttachingParameter j)‖ := rfl

/-- The real phase used by the mapping-torus time coordinate, retaining
the original logarithmic parameter and ramification order. -/
def nativeBoundaryRootPhase (j : Kind) : ℝ :=
  (j.order : ℝ) * (chosenAttachingParameter j).re

/-- Exact complex-coordinate equality at every real time. -/
theorem nativeBoundaryRoot_coe (j : Kind) (t : ℝ) :
    (root j.order (specialBaseCover.radius (some j)) (nativeBoundaryRootRadius j)
      (((t + nativeBoundaryRootPhase j) / j.order : ℝ) : PolarCircle) : ℂ) =
        exponential (chosenAttachingParameter j + (t : ℂ) / (j.order : ℂ)) := by
  have hm : (j.order : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt j.order_pos)
  have ht : (t + nativeBoundaryRootPhase j) / (j.order : ℝ) =
      (chosenAttachingParameter j).re + t / (j.order : ℝ) := by
    dsimp [nativeBoundaryRootPhase]
    field_simp
    ring
  change ‖exponential (chosenAttachingParameter j)‖ •
    (phase (((t + nativeBoundaryRootPhase j) / j.order : ℝ) : PolarCircle) : ℂ) = _
  rw [phase_real, Complex.real_smul, ht]
  simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [exponential_add, ← mul_assoc, ← exponential_eq_norm_mul_real,
    ← exponential_add]

/-- The original disc point is exactly the positive native logarithmic root. -/
theorem nativeBoundaryRoot_eq (j : Kind) (t : ℝ) :
    root j.order (specialBaseCover.radius (some j)) (nativeBoundaryRootRadius j)
      (((t + nativeBoundaryRootPhase j) / j.order : ℝ) : PolarCircle) =
        nativeClockwiseRoot j (-t) := by
  apply Subtype.ext
  rw [nativeBoundaryRoot_coe, nativeClockwiseRoot_coe]
  simp only [nativeClockwiseParameter, Complex.ofReal_neg, neg_div, sub_neg_eq_add]

/-- The inverse-Cayley point is the whole native positive covering curve,
so the original root marking is preserved pointwise. -/
theorem nativeBoundaryRoot_localBase (j : Kind) (t : ℝ) :
    localBase j
      ⟨root j.order (specialBaseCover.radius (some j)) (nativeBoundaryRootRadius j)
        (((t + nativeBoundaryRootPhase j) / j.order : ℝ) : PolarCircle),
        root_ne_zero _ _ _ _⟩ = nativePositiveBase j t := by
  change localBase j _ =
    localBase j ⟨nativeClockwiseRoot j (-t), nativeClockwiseRoot_ne_zero j (-t)⟩
  apply congrArg (localBase j)
  exact Subtype.ext (nativeBoundaryRoot_eq j t)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
