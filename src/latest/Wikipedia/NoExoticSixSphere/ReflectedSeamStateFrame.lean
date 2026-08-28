import Wikipedia.NoExoticSixSphere.ReflectedSeamColumns
import Wikipedia.NoExoticSixSphere.CollaredZeroNormalFrame

/-!
# The initial collared state's complete induced six-frame

Under the native endpoint-to-zero diffeomorphism, the actual initial
state embedding appends a zero time coordinate. Its full induced normal
frame is the ordinary one-axis stabilization of the original endpoint
columns, normalized in the explicitly retained normal-coordinate order.
The fixed comparison includes the outward last-column reflection.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.ReflectedSeam

open GLOrthonormalization Stiefel Wikipedia.HopfProblem.DegreeCollapse
open ReflectedCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hmiss : ∀ x, d.rightMap x ≠ b) (hd : m = n + 6) (a : Sphere m)

def sixColumnChange (y : Fiber d) :
    Vector ((m + 2) - 6) ≃ₗᵢ[ℝ] Vector (((m + 2) - 7) + 1) := by
  let := fiberAtlas d 6 hd
  let := fiber_isManifold d 6 hd
  exact (EmbeddedTime.normalCoordinates (n := 6) (embedding d hmiss 6 hd) y).trans
    (OrthogonalFrameAppend.lastReflection ((m + 2) - 7))

theorem referenceState_embedding (x : EndpointFiber d) :
    let S := referenceLowCollaredState d hmiss hd a;
    letI := S.zeroAtlas;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    (CollaredZero.embedding S).toFun (referenceLowStateZeroDiffeomorph d hmiss hd a x) =
      appendZeroMap (m + 1) 1 x.val.val := by
  let S := referenceLowCollaredState d hmiss hd a
  let := S.zeroAtlas
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  exact (spatialIsometry_apply m x.val.val).symm

theorem referenceState_sixFrame (y : Fiber d) (x : EndpointFiber d) :
    let S := referenceLowCollaredState d hmiss hd a;
    letI := S.zeroAtlas;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    ∀ v : Vector ((m + 2) - 6),
      (CollaredZero.normalFrame S y).ambient
        (referenceLowStateZeroDiffeomorph d hmiss hd a x) v =
      BlockSum.operator 1 (Orthonormalization.operator (endpointColumns d hmiss 6 hd a) x)
        (sixColumnChange d hmiss hd y v) := by
  let S := referenceLowCollaredState d hmiss hd a
  let := fiberAtlas d 6 hd
  let := fiber_isManifold d 6 hd
  let := S.zeroAtlas
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  change ∀ v : Vector ((m + 2) - 6),
    (CollaredZero.normalFrame S y).ambient
      (referenceLowStateZeroDiffeomorph d hmiss hd a x) v =
    BlockSum.operator 1 (Orthonormalization.operator (endpointColumns d hmiss 6 hd a) x)
      (sixColumnChange d hmiss hd y v)
  intro v
  have h := zeroColumns_seam d hmiss 6 hd a x (CollaredZero.retraction S y)
  exact congrArg (fun L : Vector (((m + 2) - 7) + 1) →L[ℝ] Vector (m + 2) ↦
    L (EmbeddedTime.normalCoordinates (n := 6) (embedding d hmiss 6 hd) y v)) h

end NoExoticSixSphere.ReflectedSeam
