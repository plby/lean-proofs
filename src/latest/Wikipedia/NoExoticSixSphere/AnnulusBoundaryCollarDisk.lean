import Wikipedia.NoExoticSixSphere.AnnulusClockCollarImmersion
import Wikipedia.NoExoticSixSphere.RegularCylinderDiskCollar

/-!
# The original annulus collars as smooth unit-disk boundary data

Translate the actual endpoint times to zero and put height last. At the
outer end, precompose by the literal radius-two dilation. The resulting
globally smooth ambient disks retain the original spatial sphere maps
and the actual collar derivatives. Both radial height derivatives are
positive: the outer clock derivative and its original cut coefficient
are both negative. No replacement of the clock or endpoint frame occurs.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereAnnulus

open GLOrthonormalization
open Wikipedia.SmoothSixDPoincare.SphereBoundary

theorem ambientClock_unit {p : ℕ} (q : Sphere p) : ambientClock q.val = 0 := by
  simp only [ambientClock, ambientTime, ClosedHemisphere.unit_norm]
  norm_num

theorem ambientClock_two_unit {p : ℕ} (q : Sphere p) :
    ambientClock ((2 : ℝ) • q.val) = 0 := by
  simp only [ambientClock, ambientTime, norm_smul, ClosedHemisphere.unit_norm]
  norm_num

theorem fderiv_ambientClock_radial {p : ℕ} (x : Vector (p + 1)) :
    fderiv ℝ ambientClock x x = ((20 - 8 * ‖x‖ ^ 2) / 9) * (2 * ‖x‖ ^ 2) := by
  have hρ : fderiv ℝ (definingFunction (E := Vector (p + 1))) x x = 2 * ‖x‖ ^ 2 := by
    rw [fderiv_definingFunction, two_smul, add_apply]
    change inner ℝ x x + inner ℝ x x = 2 * ‖x‖ ^ 2
    rw [real_inner_self_eq_norm_sq]
    ring
  rw [fderiv_ambientClock]
  change ((20 - 8 * ‖x‖ ^ 2) / 9) * fderiv ℝ definingFunction x x = _
  rw [hρ]

theorem fderiv_ambientClock_unit_radial {p : ℕ} (q : Sphere p) :
    fderiv ℝ ambientClock q.val q.val = 8 / 3 := by
  rw [fderiv_ambientClock_radial, ClosedHemisphere.unit_norm]
  norm_num

theorem fderiv_ambientClock_two_unit_radial {p : ℕ} (q : Sphere p) :
    fderiv ℝ ambientClock ((2 : ℝ) • q.val) ((2 : ℝ) • q.val) = -32 / 3 := by
  rw [fderiv_ambientClock_radial, norm_smul, ClosedHemisphere.unit_norm]
  norm_num

end NoExoticSixSphere.SphereAnnulus

namespace NoExoticSixSphere.RegularSlabCylinderCollar

open GLOrthonormalization CylinderFiberSlab RegularSlabDiskCollar RegularCylinderFiber
open Wikipedia.HopfProblem.DegreeCollapse

def outerRadiusCoordinates : Vector 4 ≃L[ℝ] Vector 4 :=
  (LinearEquiv.smulOfNeZero ℝ (Vector 4) 2 (by norm_num)).toContinuousLinearEquiv

theorem outerRadiusCoordinates_apply (x : Vector 4) :
    outerRadiusCoordinates x = (2 : ℝ) • x := rfl

theorem fderiv_shiftedCollar_coordinates {m : ℕ} (c : ℝ)
    (H : Vector 4 → ℝ × Vector (m + 1)) {x : Vector 4} (hH : DifferentiableAt ℝ H x) :
    fderiv ℝ (shiftedCollar c H) x = (collarTargetCoordinates m).toContinuousLinearMap.comp
      (fderiv ℝ (EuclideanProduct.coordinates (m + 1) ∘ H) x) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [fderiv_shiftedCollar c H hH]
  rw [((EuclideanProduct.coordinates (m + 1)).hasFDerivAt.comp x hH.hasFDerivAt).fderiv]
  change (fderiv ℝ H x v).swap =
    collarTargetCoordinates m (EuclideanProduct.coordinates (m + 1) (fderiv ℝ H x v))
  exact (collarTargetCoordinates_coordinates m _).symm

variable {m n : ℕ} {z : NoExoticSixSphere.Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := NoExoticSixSphere.Sphere m) (𝓡 m) (𝓡 n) z s t}
  {f₀ f₁ : C(NoExoticSixSphere.Sphere 3, slab d.map z s t)}
  (D : d.CollaredCylinderExtension 3 f₀ f₁) (b : NoExoticSixSphere.Sphere 3)

def leftBoundaryDisk : Vector 4 → Vector (m + 1) × ℝ :=
  shiftedCollar s (leftCollar D b)

def rightBoundaryDisk : Vector 4 → Vector (m + 1) × ℝ :=
  shiftedCollar t (rightCollar D b) ∘ outerRadiusCoordinates

theorem contDiff_leftBoundaryDisk
    (hf₀ : ContMDiff (𝓡 3) (𝓡 (m + 1)) ∞ (spatial f₀)) :
    ContDiff ℝ ∞ (leftBoundaryDisk D b) :=
  contDiff_shiftedCollar s _ (contDiff_leftCollar D b hf₀)

theorem contDiff_rightBoundaryDisk
    (hf₁ : ContMDiff (𝓡 3) (𝓡 (m + 1)) ∞ (spatial f₁)) :
    ContDiff ℝ ∞ (rightBoundaryDisk D b) :=
  (contDiff_shiftedCollar t _ (contDiff_rightCollar D b hf₁)).comp outerRadiusCoordinates.contDiff

theorem leftBoundaryDisk_boundary (q : NoExoticSixSphere.Sphere 3) :
    leftBoundaryDisk D b q.val = (spatial f₀ q, 0) := by
  change (SmoothSphereAmbient.extension b (spatial f₀) q.val,
    s + SphereAnnulus.ambientClock q.val * (D.leftCut - s) - s) = _
  rw [SmoothSphereAmbient.extension_coe, SphereAnnulus.ambientClock_unit]
  simp only [zero_mul, add_zero, sub_self]

theorem rightBoundaryDisk_boundary (q : NoExoticSixSphere.Sphere 3) :
    rightBoundaryDisk D b q.val = (spatial f₁ q, 0) := by
  have hn : ‖(2 : ℝ) • q.val‖ = 2 := by
    rw [norm_smul, ClosedHemisphere.unit_norm]
    norm_num
  change (SmoothSphereAmbient.extension b (spatial f₁) ((2 : ℝ) • q.val),
    t + SphereAnnulus.ambientClock ((2 : ℝ) • q.val) * (D.rightCut - t) - t) = _
  rw [SmoothSphereAmbient.extension_eq_radial_of_half_le b (spatial f₁)
    (by rw [hn]; norm_num), SphereRadialRetraction.retract_pos_smul b q (by norm_num),
    SphereAnnulus.ambientClock_two_unit]
  simp only [zero_mul, add_zero, sub_self]

theorem fderiv_leftBoundaryDisk
    (hf₀ : ContMDiff (𝓡 3) (𝓡 (m + 1)) ∞ (spatial f₀)) (x : Vector 4) :
    fderiv ℝ (leftBoundaryDisk D b) x = (collarTargetCoordinates m).toContinuousLinearMap.comp
      (fderiv ℝ (EuclideanProduct.coordinates (m + 1) ∘ leftCollar D b) x) :=
  fderiv_shiftedCollar_coordinates s _ ((contDiff_leftCollar D b hf₀).differentiable (by simp) x)

theorem fderiv_rightBoundaryDisk
    (hf₁ : ContMDiff (𝓡 3) (𝓡 (m + 1)) ∞ (spatial f₁)) (x : Vector 4) :
    fderiv ℝ (rightBoundaryDisk D b) x = (collarTargetCoordinates m).toContinuousLinearMap.comp
      ((fderiv ℝ (EuclideanProduct.coordinates (m + 1) ∘ rightCollar D b)
        ((2 : ℝ) • x)).comp outerRadiusCoordinates.toContinuousLinearMap) := by
  rw [rightBoundaryDisk, fderiv_comp x
    ((contDiff_shiftedCollar t _ (contDiff_rightCollar D b hf₁)).differentiable (by simp) _)
    outerRadiusCoordinates.differentiableAt, outerRadiusCoordinates.fderiv,
    fderiv_shiftedCollar_coordinates t _
      ((contDiff_rightCollar D b hf₁).differentiable (by simp) _)]
  rfl

theorem leftBoundaryDisk_height_positive
    (hf₀ : ContMDiff (𝓡 3) (𝓡 (m + 1)) ∞ (spatial f₀))
    (q : NoExoticSixSphere.Sphere 3) :
    0 < (fderiv ℝ (leftBoundaryDisk D b) q.val q.val).2 := by
  rw [leftBoundaryDisk, fderiv_shiftedCollar s _
    ((contDiff_leftCollar D b hf₀).differentiable (by simp) _), leftCollar_eq_clockMap,
    AnnulusClockCollar.fderiv_map b (spatial f₀) s (D.leftCut - s) hf₀]
  change 0 < (D.leftCut - s) * fderiv ℝ SphereAnnulus.ambientClock q.val q.val
  rw [SphereAnnulus.fderiv_ambientClock_unit_radial]
  exact mul_pos (sub_pos.mpr D.left_lt) (by norm_num)

theorem rightBoundaryDisk_height_positive
    (hf₁ : ContMDiff (𝓡 3) (𝓡 (m + 1)) ∞ (spatial f₁))
    (q : NoExoticSixSphere.Sphere 3) :
    0 < (fderiv ℝ (rightBoundaryDisk D b) q.val q.val).2 := by
  rw [rightBoundaryDisk, fderiv_comp q.val
    ((contDiff_shiftedCollar t _ (contDiff_rightCollar D b hf₁)).differentiable (by simp) _)
    outerRadiusCoordinates.differentiableAt, outerRadiusCoordinates.fderiv]
  change 0 < (fderiv ℝ (shiftedCollar t (rightCollar D b))
    ((2 : ℝ) • q.val) ((2 : ℝ) • q.val)).2
  rw [fderiv_shiftedCollar t _
    ((contDiff_rightCollar D b hf₁).differentiable (by simp) _), rightCollar_eq_clockMap,
    AnnulusClockCollar.fderiv_map b (spatial f₁) t (D.rightCut - t) hf₁]
  change 0 < (D.rightCut - t) *
    fderiv ℝ SphereAnnulus.ambientClock ((2 : ℝ) • q.val) ((2 : ℝ) • q.val)
  rw [SphereAnnulus.fderiv_ambientClock_two_unit_radial]
  exact mul_pos_of_neg_of_neg (sub_neg.mpr D.right_lt) (by norm_num)

end NoExoticSixSphere.RegularSlabCylinderCollar
