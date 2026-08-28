import Wikipedia.NoExoticSixSphere.CircleCylinderRegularTime

/-!
# Both original endpoint inclusions are genuine smooth immersions

Projection to the original spatial sphere recovers the original endpoint
inclusion. Its injective native differential therefore forces injectivity
of each endpoint's differential into the circle-double fiber.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

def spatial : C(Fiber d, Sphere m) :=
  ⟨fun p ↦ p.val.2, continuous_snd.comp continuous_subtype_val⟩

theorem contMDiff_spatial (k : ℕ) (hd : m = n + k) :
    letI := fiberAtlas d k hd;
    ContMDiff (𝓡 (k + 1)) (𝓡 m) ∞ (spatial d) := by
  let := fiberAtlas d k hd
  exact contMDiff_snd.comp
    (regularFiber_contMDiff_subtype_val (map d) (contMDiff_map d) b (regular_map d)
      (k + 1) (dimension_eq k hd))

theorem mfderiv_leftInclusion_injective (k : ℕ) (hd : m = n + k)
    (x : {x : Sphere m // d.leftMap x = b}) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    letI := fiberAtlas d k hd;
    Injective (mfderiv (𝓡 k) (𝓡 (k + 1)) (leftInclusion d) x) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  let := fiberAtlas d k hd
  have hc := mfderiv_comp x ((contMDiff_spatial d k hd).mdifferentiableAt (by simp))
    ((contMDiff_leftInclusion d k hd).mdifferentiableAt (by simp))
  change mfderiv (𝓡 k) (𝓡 m)
    (Subtype.val : {x : Sphere m // d.leftMap x = b} → Sphere m) x = _ at hc
  intro u v huv
  apply regularFiber_injective_mfderiv_subtype_val
    d.leftMap d.smooth_left b d.regular_left k (by simpa using hd) x
  rw [hc]
  exact congrArg (mfderiv (𝓡 (k + 1)) (𝓡 m) (spatial d) (leftInclusion d x)) huv

theorem mfderiv_rightInclusion_injective (k : ℕ) (hd : m = n + k)
    (x : {x : Sphere m // d.rightMap x = b}) :
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd);
    letI := fiberAtlas d k hd;
    Injective (mfderiv (𝓡 k) (𝓡 (k + 1)) (rightInclusion d) x) := by
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  let := fiberAtlas d k hd
  have hc := mfderiv_comp x ((contMDiff_spatial d k hd).mdifferentiableAt (by simp))
    ((contMDiff_rightInclusion d k hd).mdifferentiableAt (by simp))
  change mfderiv (𝓡 k) (𝓡 m)
    (Subtype.val : {x : Sphere m // d.rightMap x = b} → Sphere m) x = _ at hc
  intro u v huv
  apply regularFiber_injective_mfderiv_subtype_val
    d.rightMap d.smooth_right b d.regular_right k (by simpa using hd) x
  rw [hc]
  exact congrArg (mfderiv (𝓡 (k + 1)) (𝓡 m) (spatial d) (rightInclusion d x)) huv

end NoExoticSixSphere.CircleCylinder
