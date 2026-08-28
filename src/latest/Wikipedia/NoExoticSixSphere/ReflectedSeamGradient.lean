import Wikipedia.NoExoticSixSphere.AmbientLinearTimeGradient
import Wikipedia.NoExoticSixSphere.RegularTimeZeroColumns
import Wikipedia.HopfProblem.DegreeCollapseReflectedLowCollaredState

/-!
# The actual time-gradient and outward normal on the reflected seam

The reflected embedding has its original time as its last ambient
coordinate. On the whole seam collar every normal-frame column has zero
time component, so the positive unit time axis is tangent. It is therefore
the intrinsic gradient, for every tubular retraction. The induced boundary
normal is precisely the negative time axis, not an unsigned normal line.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.ReflectedSeam

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse
open ReflectedCylinder

def timeUnit (m : ℕ) : Vector (m + 2) :=
  ambientCoordinates m (WithLp.toLp 2 (1, (0 : Vector (m + 1))))

def timeCoordinate (m : ℕ) : Vector (m + 2) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (Vector (m + 1))).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Vector (m + 1))).toContinuousLinearMap.comp
      (ambientCoordinates m).symm.toContinuousLinearMap)

theorem inner_timeUnit (m : ℕ) (v : Vector (m + 2)) :
    inner ℝ (timeUnit m) v = timeCoordinate m v := by
  have h := (ambientCoordinates m).inner_map_map
    (WithLp.toLp 2 (1, (0 : Vector (m + 1)))) ((ambientCoordinates m).symm v)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  change inner ℝ (timeUnit m) v = ((ambientCoordinates m).symm v).fst
  exact h.trans (by simp [WithLp.prod_inner_apply])

theorem timeUnit_norm (m : ℕ) : ‖timeUnit m‖ = 1 := by
  rw [timeUnit, LinearIsometryEquiv.norm_map]
  simp

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hmiss : ∀ x, d.rightMap x ≠ b) (k : ℕ) (hd : m = n + k)

theorem timeCoordinate_embedding (p : Fiber d) : letI := fiberAtlas d k hd;
    timeCoordinate m ((embedding d hmiss k hd).toFun p) = time d p := by
  let := fiberAtlas d k hd
  change ((ambientCoordinates m).symm (ambientCoordinates m (ambientInclusion d p))).fst =
    p.val.1
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem timeUnit_mem_tangent (a : Sphere m) (s : ℝ) (hs : s ∈ seamCollarTimes d)
    (x : EndpointFiber d) : letI := fiberAtlas d k hd;
    timeUnit m ∈ (embedding d hmiss k hd).tangentImage (seamCollarPoint d s hs x) := by
  let := fiberAtlas d k hd
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  let e := embedding d hmiss k hd
  let A := euclideanNormalFraming d hmiss k hd a
  let F (p : Fiber d) : Vector ((m + 2) - (k + 1)) →L[ℝ] Vector (m + 2) := A.ambient p
  let p := seamCollarPoint d s hs x
  let P : Submodule ℝ (Vector (m + 2)) := e.tangentImage p
  have hN : (F p).range = Pᗮ :=
    (A.ambient_range p).trans (e.range_normalProjection p)
  have ho : timeUnit m ∈ (F p).rangeᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    rintro _ ⟨v, rfl⟩
    rw [real_inner_comm, inner_timeUnit]
    have he := euclideanNormalFraming_seamCollar d hmiss k hd a s hs x
    change timeCoordinate m ((euclideanNormalFraming d hmiss k hd a).ambient
      (seamCollarPoint d s hs x) v) = 0
    rw [he]
    change ((ambientCoordinates m).symm
      (ambientCoordinates m (WithLp.toLp 2 (0, _)))).fst = 0
    rw [LinearIsometryEquiv.symm_apply_apply]
    rfl
  rw [hN, Submodule.orthogonal_orthogonal] at ho
  exact ho

theorem gradient_seamCollar (a : Sphere m) (s : ℝ) (hs : s ∈ seamCollarTimes d)
    (x : EndpointFiber d) : letI := fiberAtlas d k hd; letI := fiber_isManifold d k hd;
    ∀ r : (embedding d hmiss k hd).TubularRetraction,
      EmbeddedTime.gradient (embedding d hmiss k hd) r (time d)
        (seamCollarPoint d s hs x) = timeUnit m := by
  let := fiberAtlas d k hd
  let := fiber_isManifold d k hd
  intro r
  exact EmbeddedTime.gradient_eq_of_ambient_linear_time (embedding d hmiss k hd) r (time d)
    (contMDiff_time d k hd) (timeCoordinate m) (timeCoordinate_embedding d hmiss k hd)
    (timeUnit m) (inner_timeUnit m) _ (timeUnit_mem_tangent d hmiss k hd a s hs x)

theorem outwardNormal_seam (a : Sphere m) (x : EndpointFiber d) :
    letI := fiberAtlas d k hd; letI := fiber_isManifold d k hd;
    ∀ r : (embedding d hmiss k hd).TubularRetraction,
      EmbeddedTime.outwardNormal (n := k) (embedding d hmiss k hd) r (timeZeroMap d)
        (endpointToTimeZero d x) = -timeUnit m := by
  let := fiberAtlas d k hd
  let := fiber_isManifold d k hd
  intro r
  change -NormedSpace.normalize (EmbeddedTime.gradient (embedding d hmiss k hd) r (time d)
    (seamCollarPoint d 0 (zero_mem_seamCollarTimes d) x)) = -timeUnit m
  rw [gradient_seamCollar d hmiss k hd a 0 (zero_mem_seamCollarTimes d) x r]
  change -(‖timeUnit m‖⁻¹ • timeUnit m) = -timeUnit m
  rw [timeUnit_norm, inv_one, one_smul]

end NoExoticSixSphere.ReflectedSeam
