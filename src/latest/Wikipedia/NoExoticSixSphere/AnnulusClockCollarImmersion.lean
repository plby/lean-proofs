import Wikipedia.NoExoticSixSphere.AnnulusClockDerivative
import Wikipedia.NoExoticSixSphere.ScaledSphereBoundaryKernel

/-!
# Immersion of the original annulus collars at both boundary radii

The actual clock derivative detects the radial direction missing from
the original sphere derivative. The scaled tangent-kernel theorem treats
the radius-two sphere without changing its original spatial map. Applying
this calculation to the retained left and right collar formulas proves
boundary immersion with their actual nonzero signed height coefficients.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.AnnulusClockCollar

open GLOrthonormalization
open Wikipedia.SmoothSixDPoincare.SphereBoundary

variable {p : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (b : Sphere p) (f : Sphere p → F) (c slope : ℝ)

def map (x : Vector (p + 1)) : ℝ × F :=
  (c + slope * SphereAnnulus.ambientClock x, SmoothSphereAmbient.extension b f x)

theorem contDiff_map (hf : ContMDiff (𝓡 p) 𝓘(ℝ, F) ∞ f) :
    ContDiff ℝ ∞ (map b f c slope) :=
  (contDiff_const.add (contDiff_const.mul (SphereAnnulus.contDiff_ambientClock p))).prodMk
    (SmoothSphereAmbient.contDiff_extension b f hf)

theorem fderiv_map (hf : ContMDiff (𝓡 p) 𝓘(ℝ, F) ∞ f) (x : Vector (p + 1)) :
    fderiv ℝ (map b f c slope) x =
      (slope • fderiv ℝ SphereAnnulus.ambientClock x).prod
        (fderiv ℝ (SmoothSphereAmbient.extension b f) x) := by
  have hC := (SphereAnnulus.contDiff_ambientClock p).differentiable (by simp) x
  have hF := (SmoothSphereAmbient.contDiff_extension b f hf).differentiable (by simp) x
  exact (((hC.hasFDerivAt.const_mul slope).const_add c).prodMk hF.hasFDerivAt).fderiv

theorem injective_fderiv_scaled_sphere (hf : ContMDiff (𝓡 p) 𝓘(ℝ, F) ∞ f)
    (hslope : slope ≠ 0) (r : ℝ) (hr : r = 1 ∨ r = 2)
    (hi : ∀ q, Injective (mfderiv (𝓡 p) 𝓘(ℝ, F) f q)) (q : Sphere p) :
    Injective (fderiv ℝ (map b f c slope) (r • q.val)) := by
  have hrpos : 0 < r := by rcases hr with rfl | rfl <;> norm_num
  have hrhalf : (1 / 2 : ℝ) ≤ r := by rcases hr with rfl | rfl <;> norm_num
  have hn (q : Sphere p) : ‖r • q.val‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg hrpos.le, ClosedHemisphere.unit_norm, mul_one]
  have hext (q : Sphere p) : SmoothSphereAmbient.extension b f (r • q.val) = f q := by
    rw [SmoothSphereAmbient.extension_eq_radial_of_half_le b f (by rw [hn]; exact hrhalf),
      SphereRadialRetraction.retract_pos_smul b q hrpos]
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  rw [fderiv_map b f c slope hf] at hv
  have hc : slope * fderiv ℝ SphereAnnulus.ambientClock (r • q.val) v = 0 :=
    congrArg Prod.fst hv
  have hcv := (mul_eq_zero.mp hc).resolve_left hslope
  have hnv := (SphereAnnulus.fderiv_ambientClock_zero_iff (r • q.val) v (by rw [hn]; exact hr)).mp
    hcv
  exact common_kernel_of_scaled_sphere_extension (SmoothSphereAmbient.extension b f)
    (SmoothSphereAmbient.contDiff_extension b f hf) r hrpos f hext hi q v
    (congrArg Prod.snd hv) hnv

end NoExoticSixSphere.AnnulusClockCollar

namespace NoExoticSixSphere.RegularSlabCylinderCollar

open GLOrthonormalization CylinderFiberSlab RegularSlabDiskCollar

variable {m n p : ℕ} {z : NoExoticSixSphere.Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := NoExoticSixSphere.Sphere m) (𝓡 m) (𝓡 n) z s t}
  {f₀ f₁ : C(NoExoticSixSphere.Sphere p, slab d.map z s t)}
  (D : d.CollaredCylinderExtension p f₀ f₁) (b : NoExoticSixSphere.Sphere p)

theorem leftCollar_eq_clockMap :
    leftCollar D b = AnnulusClockCollar.map b (spatial f₀) s (D.leftCut - s) := by
  funext x
  apply Prod.ext
  · change s + SphereAnnulus.ambientClock x * (D.leftCut - s) =
      s + (D.leftCut - s) * SphereAnnulus.ambientClock x
    ring
  · rfl

theorem rightCollar_eq_clockMap :
    rightCollar D b = AnnulusClockCollar.map b (spatial f₁) t (D.rightCut - t) := by
  funext x
  apply Prod.ext
  · change t + SphereAnnulus.ambientClock x * (D.rightCut - t) =
      t + (D.rightCut - t) * SphereAnnulus.ambientClock x
    ring
  · rfl

theorem injective_fderiv_leftCollar
    (hf₀ : ContMDiff (𝓡 p) (𝓡 (m + 1)) ∞ (spatial f₀))
    (hi₀ : ∀ q, Injective (mfderiv (𝓡 p) (𝓡 (m + 1)) (spatial f₀) q))
    (q : NoExoticSixSphere.Sphere p) : Injective (fderiv ℝ (leftCollar D b) q.val) := by
  rw [leftCollar_eq_clockMap]
  simpa only [one_smul] using AnnulusClockCollar.injective_fderiv_scaled_sphere b (spatial f₀)
    s (D.leftCut - s) hf₀ (ne_of_gt (sub_pos.mpr D.left_lt)) 1 (Or.inl rfl) hi₀ q

theorem injective_fderiv_rightCollar
    (hf₁ : ContMDiff (𝓡 p) (𝓡 (m + 1)) ∞ (spatial f₁))
    (hi₁ : ∀ q, Injective (mfderiv (𝓡 p) (𝓡 (m + 1)) (spatial f₁) q))
    (q : NoExoticSixSphere.Sphere p) :
    Injective (fderiv ℝ (rightCollar D b) ((2 : ℝ) • q.val)) := by
  rw [rightCollar_eq_clockMap]
  exact AnnulusClockCollar.injective_fderiv_scaled_sphere b (spatial f₁)
    t (D.rightCut - t) hf₁ (ne_of_lt (sub_neg.mpr D.right_lt)) 2 (Or.inr rfl) hi₁ q

end NoExoticSixSphere.RegularSlabCylinderCollar
