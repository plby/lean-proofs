import Wikipedia.NoExoticSixSphere.RegularSlabCollaredCylinder
import Wikipedia.NoExoticSixSphere.SphereAnnulusCoordinates
import Wikipedia.NoExoticSixSphere.RegularSlabDiskCollar

/-!
# The original slab cylinder and its globally smooth ambient annulus collars

Transport the actual cylinder to the Euclidean annulus through the explicit
squared-radius coordinates. The prescribed original spatial maps have
their existing smooth ambient extensions. The collar heights are the
literal original inward-clock formulas, now polynomial in the squared
norm. Both original collar equalities and strict interior values survive.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereAnnulus

open GLOrthonormalization

def ambientTime {p : ℕ} (x : Vector (p + 1)) : ℝ := (‖x‖ ^ 2 - 1) / 3

def ambientClock {p : ℕ} (x : Vector (p + 1)) : ℝ :=
  4 * ambientTime x * (1 - ambientTime x)

theorem contDiff_ambientTime (p : ℕ) : ContDiff ℝ ∞ (ambientTime (p := p)) :=
  ((contDiff_norm_sq ℝ).sub contDiff_const).div_const 3

theorem contDiff_ambientClock (p : ℕ) : ContDiff ℝ ∞ (ambientClock (p := p)) :=
  (contDiff_const.mul (contDiff_ambientTime p)).mul
    (contDiff_const.sub (contDiff_ambientTime p))

theorem ambientClock_eq {p : ℕ} (x : domain p) :
    ambientClock x.val = (CylinderTime.interiorClock (time x) : ℝ) := rfl

end NoExoticSixSphere.SphereAnnulus

namespace NoExoticSixSphere.RegularSlabCylinderCollar

open GLOrthonormalization CylinderFiberSlab RegularSlabDiskCollar

variable {m n p : ℕ} {z : NoExoticSixSphere.Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := NoExoticSixSphere.Sphere m) (𝓡 m) (𝓡 n) z s t}
  {f₀ f₁ : C(NoExoticSixSphere.Sphere p, slab d.map z s t)}
  (D : d.CollaredCylinderExtension p f₀ f₁) (b : NoExoticSixSphere.Sphere p)

def annulusMap : C(SphereAnnulus.domain p,
    {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z}) :=
  ⟨fun x ↦ (D.map (SphereAnnulus.toCylinder b x)).val,
    continuous_subtype_val.comp (D.map.continuous.comp (SphereAnnulus.toCylinder b).continuous)⟩

def ambient : C(SphereAnnulus.domain p, ℝ × Vector (m + 1)) where
  toFun x := ((annulusMap D b x).val.1, (annulusMap D b x).val.2.val)
  continuous_toFun := by
    have h := continuous_subtype_val.comp (annulusMap D b).continuous
    exact h.fst.prodMk (continuous_subtype_val.comp h.snd)

def leftCollar (x : Vector (p + 1)) : ℝ × Vector (m + 1) :=
  (s + SphereAnnulus.ambientClock x * (D.leftCut - s),
    SmoothSphereAmbient.extension b (spatial f₀) x)

def rightCollar (x : Vector (p + 1)) : ℝ × Vector (m + 1) :=
  (t + SphereAnnulus.ambientClock x * (D.rightCut - t),
    SmoothSphereAmbient.extension b (spatial f₁) x)

theorem contDiff_leftCollar
    (hf₀ : ContMDiff (𝓡 p) (𝓡 (m + 1)) ∞ (spatial f₀)) :
    ContDiff ℝ ∞ (leftCollar D b) :=
  (contDiff_const.add ((SphereAnnulus.contDiff_ambientClock p).mul contDiff_const)).prodMk
    (SmoothSphereAmbient.contDiff_extension b (spatial f₀) hf₀)

theorem contDiff_rightCollar
    (hf₁ : ContMDiff (𝓡 p) (𝓡 (m + 1)) ∞ (spatial f₁)) :
    ContDiff ℝ ∞ (rightCollar D b) :=
  (contDiff_const.add ((SphereAnnulus.contDiff_ambientClock p).mul contDiff_const)).prodMk
    (SmoothSphereAmbient.contDiff_extension b (spatial f₁) hf₁)

theorem ambient_eq_leftCollar (h₀ : ∀ q, (f₀ q).val.val.1 = s)
    (x : SphereAnnulus.domain p) (hx : ‖x.val‖ ≤ 4 / 3) :
    ambient D b x = leftCollar D b x.val := by
  have hl := x.property.1
  have ht : (SphereAnnulus.time x : ℝ) ≤ 1 / 3 :=
    (SphereAnnulus.time_le_third_iff x).mpr (by nlinarith)
  have he := congrArg (fun v : ℝ × NoExoticSixSphere.Sphere m ↦ (v.1, v.2.val))
    (D.left_collar (SphereAnnulus.time x) ht (SphereRadialRetraction.retract b x.val)
      (h₀ (SphereRadialRetraction.retract b x.val)))
  change ambient D b x =
    (s + SphereAnnulus.ambientClock x.val * (D.leftCut - s),
      spatial f₀ (SphereRadialRetraction.retract b x.val)) at he
  rw [he, leftCollar, SmoothSphereAmbient.extension_eq_radial_of_half_le b (spatial f₀)
    (by linarith : (1 / 2 : ℝ) ≤ ‖x.val‖)]

theorem ambient_eq_rightCollar (h₁ : ∀ q, (f₁ q).val.val.1 = t)
    (x : SphereAnnulus.domain p) (hx : 7 / 4 ≤ ‖x.val‖) :
    ambient D b x = rightCollar D b x.val := by
  have hl := x.property.1
  have ht : 2 / 3 ≤ (SphereAnnulus.time x : ℝ) :=
    (SphereAnnulus.two_thirds_le_time_iff x).mpr (by nlinarith)
  have he := congrArg (fun v : ℝ × NoExoticSixSphere.Sphere m ↦ (v.1, v.2.val))
    (D.right_collar (SphereAnnulus.time x) ht (SphereRadialRetraction.retract b x.val)
      (h₁ (SphereRadialRetraction.retract b x.val)))
  change ambient D b x =
    (t + SphereAnnulus.ambientClock x.val * (D.rightCut - t),
      spatial f₁ (SphereRadialRetraction.retract b x.val)) at he
  rw [he, rightCollar, SmoothSphereAmbient.extension_eq_radial_of_half_le b (spatial f₁)
    (by linarith : (1 / 2 : ℝ) ≤ ‖x.val‖)]

theorem annulusMap_fromCylinder (u : unitInterval) (q : NoExoticSixSphere.Sphere p) :
    annulusMap D b (SphereAnnulus.fromCylinder p (u, q)) = (D.map (u, q)).val := by
  change (D.map (SphereAnnulus.toCylinder b (SphereAnnulus.fromCylinder p (u, q)))).val = _
  rw [SphereAnnulus.toCylinder_fromCylinder]

theorem annulusMap_interior (x : SphereAnnulus.domain p)
    (hx₀ : 1 < ‖x.val‖) (hx₁ : ‖x.val‖ < 2) : (annulusMap D b x).val.1 ∈ Ioo s t :=
  D.interior (SphereAnnulus.time x) ((SphereAnnulus.time_pos_iff x).mpr hx₀)
    ((SphereAnnulus.time_lt_one_iff x).mpr hx₁) (SphereRadialRetraction.retract b x.val)

end NoExoticSixSphere.RegularSlabCylinderCollar
