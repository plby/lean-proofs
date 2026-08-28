import Wikipedia.NoExoticSixSphere.CircleCylinderAmbientTime
import Wikipedia.NoExoticSixSphere.CircleCylinderEndpointFrameBlocks
import Wikipedia.NoExoticSixSphere.CircleCylinderZeroDiffeomorph
import Wikipedia.NoExoticSixSphere.AmbientLinearTimeGradient
import Wikipedia.NoExoticSixSphere.RegularTimeZeroColumns

/-!
# The actual signed time-gradient and outward normal at both circle seams

At the seam the complete original normal frame has zero time component.
The actual ambient unit time vector therefore belongs to the native
tangent image. It is the intrinsic gradient for every tubular retraction,
so the outward normal of the nonnegative half is its negative.
The tangent-vector assertion is only at time zero, not on the whole collar.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

open GLOrthonormalization

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem timeCoordinate_normalFrame_left (a : Sphere 1 × Sphere m) (k : ℕ) (hd : m = n + k)
    (x : {x : Sphere m // d.leftMap x = b})
    (v : Vector (2 + (m + 1) - (k + 1))) :
    letI := fiberAtlas d k hd;
    timeCoordinate m ((euclideanNormalFrame d a k hd).ambient (leftInclusion d x) v) = 0 := by
  let := fiberAtlas d k hd
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  rw [euclideanNormalFrame_left]
  change timeCoordinate m (ambientCoordinates m (WithLp.toLp 2
    (circleNormal (SphereCylinder.endPole 0 true) ((normalCoordinates k hd v).fst), _))) = 0
  rw [timeCoordinate_ambientCoordinates]
  exact seamLinear_circleNormal_endPole true _

theorem timeCoordinate_normalFrame_right (a : Sphere 1 × Sphere m) (k : ℕ) (hd : m = n + k)
    (x : {x : Sphere m // d.rightMap x = b})
    (v : Vector (2 + (m + 1) - (k + 1))) :
    letI := fiberAtlas d k hd;
    timeCoordinate m ((euclideanNormalFrame d a k hd).ambient (rightInclusion d x) v) = 0 := by
  let := fiberAtlas d k hd
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  rw [euclideanNormalFrame_right]
  change timeCoordinate m (ambientCoordinates m (WithLp.toLp 2
    (circleNormal (SphereCylinder.endPole 0 false) ((normalCoordinates k hd v).fst), _))) = 0
  rw [timeCoordinate_ambientCoordinates]
  exact seamLinear_circleNormal_endPole false _

theorem timeCoordinate_normalFrame_seam (a : Sphere 1 × Sphere m) (k : ℕ) (hd : m = n + k)
    (p : Fiber d) (hp : time d p = 0) (v : Vector (2 + (m + 1) - (k + 1))) :
    letI := fiberAtlas d k hd;
    timeCoordinate m ((euclideanNormalFrame d a k hd).ambient p v) = 0 := by
  let := fiberAtlas d k hd
  rcases (time_eq_zero_iff d p).mp hp with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact timeCoordinate_normalFrame_left d a k hd x v
  · exact timeCoordinate_normalFrame_right d a k hd x v

theorem timeUnit_mem_tangent (a : Sphere 1 × Sphere m) (k : ℕ) (hd : m = n + k)
    (p : Fiber d) (hp : time d p = 0) : letI := fiberAtlas d k hd;
    timeUnit m ∈ (embedding d k hd).tangentImage p := by
  let := fiberAtlas d k hd
  let e := embedding d k hd
  let A := euclideanNormalFrame d a k hd
  let F : Vector (2 + (m + 1) - (k + 1)) →L[ℝ] Vector (2 + (m + 1)) := A.ambient p
  let P : Submodule ℝ (Vector (2 + (m + 1))) := e.tangentImage p
  have hN : F.range = Pᗮ := (A.ambient_range p).trans (e.range_normalProjection p)
  have ho : timeUnit m ∈ F.rangeᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    rintro _ ⟨v, rfl⟩
    rw [real_inner_comm, inner_timeUnit]
    exact timeCoordinate_normalFrame_seam d a k hd p hp v
  rw [hN, Submodule.orthogonal_orthogonal] at ho
  exact ho

theorem gradient_seam (a : Sphere 1 × Sphere m) (k : ℕ) (hd : m = n + k)
    (p : Fiber d) (hp : time d p = 0) :
    letI := fiberAtlas d k hd;
    letI := fiber_isManifold d k hd;
    ∀ r : (embedding d k hd).TubularRetraction,
      EmbeddedTime.gradient (embedding d k hd) r (time d) p = timeUnit m := by
  let := fiberAtlas d k hd
  let := fiber_isManifold d k hd
  intro r
  exact EmbeddedTime.gradient_eq_of_ambient_linear_time (embedding d k hd) r (time d)
    (contMDiff_time d k hd) (timeCoordinate m) (timeCoordinate_embedding d k hd)
    (timeUnit m) (inner_timeUnit m) p (timeUnit_mem_tangent d a k hd p hp)

theorem outwardNormal_seam (a : Sphere 1 × Sphere m) (k : ℕ) (hd : m = n + k)
    (p : TimeZero d) :
    letI := fiberAtlas d k hd;
    letI := fiber_isManifold d k hd;
    ∀ r : (embedding d k hd).TubularRetraction,
      EmbeddedTime.outwardNormal (n := k) (embedding d k hd) r (timeMap d) p = -timeUnit m := by
  let := fiberAtlas d k hd
  let := fiber_isManifold d k hd
  intro r
  change -NormedSpace.normalize (EmbeddedTime.gradient (embedding d k hd) r (time d) p.val) = _
  rw [gradient_seam d a k hd p.val p.property r]
  change -(‖timeUnit m‖⁻¹ • timeUnit m) = -timeUnit m
  rw [timeUnit_norm, inv_one, one_smul]

end NoExoticSixSphere.CircleCylinder
