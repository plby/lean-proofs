import Wikipedia.NoExoticSixSphere.CircleCylinderEuclideanEmbedding
import Wikipedia.NoExoticSixSphere.CircleCylinderSeam
import Wikipedia.NoExoticSixSphere.CircleCylinderRadialNormal

/-!
# The actual linear ambient time coordinate of the circle double

The second circle coordinate extends linearly to the fixed Euclidean
ambient space. Its metric-dual vector is the actual unit time axis.
At either circle pole it is orthogonal to the signed radial normal.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

def circleTimeUnit : V := WithLp.toLp 2 (Fin.cons 0 (fun _ : Fin 1 ↦ 1))

theorem inner_circleTimeUnit (v : V) : inner ℝ circleTimeUnit v = seamLinear v := by
  change inner ℝ circleTimeUnit v = v 1
  simp [circleTimeUnit, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]

def timeUnit (m : ℕ) : EuclideanSpace ℝ (Fin (2 + (m + 1))) :=
  ambientCoordinates m (WithLp.toLp 2 (circleTimeUnit, (0 : EuclideanSpace ℝ (Fin (m + 1)))))

def timeCoordinate (m : ℕ) : EuclideanSpace ℝ (Fin (2 + (m + 1))) →L[ℝ] ℝ :=
  seamLinear.comp ((ContinuousLinearMap.fst ℝ V (EuclideanSpace ℝ (Fin (m + 1)))).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ V
      (EuclideanSpace ℝ (Fin (m + 1)))).toContinuousLinearMap.comp
        (ambientCoordinates m).symm.toContinuousLinearEquiv.toContinuousLinearMap))

theorem timeCoordinate_ambientCoordinates (m : ℕ) (v : HilbertAmbient m) :
    timeCoordinate m (ambientCoordinates m v) = seamLinear v.fst := by
  change seamLinear ((ambientCoordinates m).symm (ambientCoordinates m v)).fst = _
  rw [(ambientCoordinates m).symm_apply_apply]

theorem inner_timeUnit (m : ℕ) (v : EuclideanSpace ℝ (Fin (2 + (m + 1)))) :
    inner ℝ (timeUnit m) v = timeCoordinate m v := by
  have h := (ambientCoordinates m).inner_map_map
    (WithLp.toLp 2 (circleTimeUnit, (0 : EuclideanSpace ℝ (Fin (m + 1)))))
    ((ambientCoordinates m).symm v)
  rw [(ambientCoordinates m).apply_symm_apply] at h
  change inner ℝ (timeUnit m) v = seamLinear ((ambientCoordinates m).symm v).fst
  refine h.trans ?_
  change inner ℝ circleTimeUnit ((ambientCoordinates m).symm v).fst +
    inner ℝ (0 : EuclideanSpace ℝ (Fin (m + 1))) ((ambientCoordinates m).symm v).snd = _
  rw [inner_circleTimeUnit, inner_zero_left, add_zero]

theorem timeUnit_norm (m : ℕ) : ‖timeUnit m‖ = 1 := by
  have h : inner ℝ (timeUnit m) (timeUnit m) = 1 := by
    rw [inner_timeUnit, timeUnit, timeCoordinate_ambientCoordinates]
    rfl
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (timeUnit m)]

theorem seamLinear_circleNormal_endPole (left : Bool) (t : ℝ) :
    seamLinear (circleNormal (SphereCylinder.endPole 0 left) t) = 0 := by
  rw [circleNormal_apply, map_smul]
  change (t / 2) * (0 : ℝ) = 0
  exact mul_zero _

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem timeCoordinate_euclideanInclusion (p : Fiber d) :
    timeCoordinate m (euclideanInclusion d p) = time d p := by
  change timeCoordinate m (ambientCoordinates m (ambientInclusion d p)) = _
  rw [timeCoordinate_ambientCoordinates]
  rfl

theorem timeCoordinate_embedding (k : ℕ) (hd : m = n + k) (p : Fiber d) :
    letI := fiberAtlas d k hd;
    timeCoordinate m ((embedding d k hd).toFun p) = time d p :=
  timeCoordinate_euclideanInclusion d p

end NoExoticSixSphere.CircleCylinder
