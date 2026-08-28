import Wikipedia.NoExoticSixSphere.CircleCylinderRegularMap

/-!
# The compact native regular fiber of the two-ended circle double

The regular circle map has its original regular-fiber atlas. Its compact
fiber contains both original endpoint fibers by their literal inclusions,
which are smooth in the independently constructed endpoint atlases.
Their images are disjoint. No connectivity or framing comparison is
assumed by this construction.
-/

noncomputable section

open Function Module
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

abbrev Fiber := {p : Sphere 1 × Sphere m // map d p = b}

theorem compactSpace_fiber : CompactSpace (Fiber d) :=
  isCompact_iff_compactSpace.mp (isClosed_eq (map d).continuous continuous_const).isCompact

theorem dimension_eq (k : ℕ) (hd : m = n + k) :
    finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin m)) =
      finrank ℝ (EuclideanSpace ℝ (Fin n)) + (k + 1) := by
  simp only [finrank_prod, finrank_euclideanSpace_fin]
  omega

@[instance_reducible]
def fiberAtlas (k : ℕ) (hd : m = n + k) :
    ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) (Fiber d) :=
  regularFiberAtlas (map d) (contMDiff_map d) b (regular_map d) (k + 1) (dimension_eq k hd)

theorem fiber_isManifold (k : ℕ) (hd : m = n + k) :
    letI := fiberAtlas d k hd;
    IsManifold (𝓡 (k + 1)) ∞ (Fiber d) :=
  regularFiber_isManifold (map d) (contMDiff_map d) b (regular_map d) (k + 1) (dimension_eq k hd)

def leftInclusion : C({x : Sphere m // d.leftMap x = b}, Fiber d) where
  toFun x := ⟨(SphereCylinder.endPole 0 true, x.val), (map_left d x.val).trans x.property⟩
  continuous_toFun := (continuous_const.prodMk continuous_subtype_val).subtype_mk _

def rightInclusion : C({x : Sphere m // d.rightMap x = b}, Fiber d) where
  toFun x := ⟨(SphereCylinder.endPole 0 false, x.val), (map_right d x.val).trans x.property⟩
  continuous_toFun := (continuous_const.prodMk continuous_subtype_val).subtype_mk _

theorem leftInclusion_val (x : {x : Sphere m // d.leftMap x = b}) :
    (leftInclusion d x).val = (SphereCylinder.endPole 0 true, x.val) := rfl

theorem rightInclusion_val (x : {x : Sphere m // d.rightMap x = b}) :
    (rightInclusion d x).val = (SphereCylinder.endPole 0 false, x.val) := rfl

theorem leftInclusion_injective : Injective (leftInclusion d) := by
  intro x y h
  exact Subtype.ext (congrArg (fun p : Fiber d ↦ p.val.2) h)

theorem rightInclusion_injective : Injective (rightInclusion d) := by
  intro x y h
  exact Subtype.ext (congrArg (fun p : Fiber d ↦ p.val.2) h)

theorem leftInclusion_ne_rightInclusion (x : {x : Sphere m // d.leftMap x = b})
    (y : {x : Sphere m // d.rightMap x = b}) : leftInclusion d x ≠ rightInclusion d y := by
  intro h
  exact SphereCylinder.endPoles_ne 0 (congrArg (fun p : Fiber d ↦ p.val.1) h).symm

theorem contMDiff_leftInclusion (k : ℕ) (hd : m = n + k) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    letI := fiberAtlas d k hd;
    ContMDiff (𝓡 k) (𝓡 (k + 1)) ∞ (leftInclusion d) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  let := fiberAtlas d k hd
  apply (regularFiber_contMDiff_iff_ambient (map d) (contMDiff_map d) b (regular_map d)
    (k + 1) (dimension_eq k hd) (leftInclusion d)).mpr
  exact contMDiff_const.prodMk
    (regularFiber_contMDiff_subtype_val d.leftMap d.smooth_left b d.regular_left k
      (by simpa using hd))

theorem contMDiff_rightInclusion (k : ℕ) (hd : m = n + k) :
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd);
    letI := fiberAtlas d k hd;
    ContMDiff (𝓡 k) (𝓡 (k + 1)) ∞ (rightInclusion d) := by
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  let := fiberAtlas d k hd
  apply (regularFiber_contMDiff_iff_ambient (map d) (contMDiff_map d) b (regular_map d)
    (k + 1) (dimension_eq k hd) (rightInclusion d)).mpr
  exact contMDiff_const.prodMk
    (regularFiber_contMDiff_subtype_val d.rightMap d.smooth_right b d.regular_right k
      (by simpa using hd))

end NoExoticSixSphere.CircleCylinder
