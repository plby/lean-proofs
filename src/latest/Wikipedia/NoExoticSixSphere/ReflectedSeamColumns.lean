import Wikipedia.NoExoticSixSphere.ReflectedSeamGradient
import Wikipedia.NoExoticSixSphere.GramSchmidtIsometry
import Wikipedia.NoExoticSixSphere.CollaredZeroComponentFrame
import Wikipedia.NoExoticSixSphere.EuclideanBlockProjection
import Wikipedia.NoExoticSixSphere.OrthogonalFrameAppendReflection
import Wikipedia.NoExoticSixSphere.PartialFrameBlockSum
import Wikipedia.NoExoticSixSphere.RegularSphereFiberEmbedding

/-!
# The full reflected seam columns in the original endpoint coordinates

The endpoint columns are the original defining-equation normal frame,
with exactly the reflected state's fixed normal-coordinate isometry.
Ambient isometric naturality of ordered Gram--Schmidt identifies the
orthonormalized seven-frame on the whole collar. At time zero, appending
the proved negative unit time-normal gives one ordinary coordinate-block
stabilization, with an explicit last-column reflection.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.ReflectedSeam

open GLOrthonormalization Stiefel Wikipedia.HopfProblem.DegreeCollapse
open ReflectedCylinder

def spatialIsometry (m : ℕ) : Vector (m + 1) →ₗᵢ[ℝ] Vector (m + 2) where
  toLinearMap := (appendZeroMap (m + 1) 1).toLinearMap
  norm_map' := norm_appendZeroMap (m + 1) 1

theorem spatialIsometry_apply (m : ℕ) (v : Vector (m + 1)) :
    spatialIsometry m v = ambientCoordinates m (WithLp.toLp 2 (0, v)) := by
  change EuclideanSpace.finAddEquivProd.symm (v, 0) =
    EuclideanSpace.finAddEquivProd.symm (v, EuclideanTailCoordinates.scalar 0)
  rw [_root_.map_zero]

theorem append_timeUnit_eq_block {m q : ℕ} (A : Vector q →L[ℝ] Vector (m + 1)) :
    OrthogonalFrameAppend.operator ((spatialIsometry m).toContinuousLinearMap.comp A)
      (timeUnit m) = BlockSum.operator 1 A := by
  apply ContinuousLinearMap.ext
  intro v
  rw [OrthogonalFrameAppend.operator_apply, BlockSum.operator_apply]
  change EuclideanSpace.finAddEquivProd.symm (A (EuclideanSpace.finAddEquivProd v).1, 0) +
      EuclideanTailCoordinates.scalar.symm (EuclideanSpace.finAddEquivProd v).2 •
        EuclideanSpace.finAddEquivProd.symm (0, EuclideanTailCoordinates.scalar 1) = _
  rw [← map_smul, ← map_add]
  apply congrArg EuclideanSpace.finAddEquivProd.symm
  apply Prod.ext
  · simp
  · change 0 + EuclideanTailCoordinates.scalar.symm (EuclideanSpace.finAddEquivProd v).2 •
      EuclideanTailCoordinates.scalar 1 = (EuclideanSpace.finAddEquivProd v).2
    rw [zero_add, ← map_smul, smul_eq_mul, mul_one, LinearIsometryEquiv.apply_symm_apply]

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hmiss : ∀ x, d.rightMap x ≠ b) (k : ℕ) (hd : m = n + k) (a : Sphere m)

def endpointColumns (x : EndpointFiber d) :
    Vector ((m + 2) - (k + 1)) →L[ℝ] Vector (m + 1) := by
  let := fiberAtlas d k hd
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  exact ((SphereFiberNormalFrame.normalFrame d.leftMap d.smooth_left b d.regular_left k hd a
    ).ambient x).comp (normalModelCoordinates d hmiss k hd).toContinuousLinearMap

def endpointColumnChange : Vector ((m + 2) - (k + 1)) ≃L[ℝ] Vector (m + 1 - k) := by
  let := fiberAtlas d k hd
  exact (normalModelCoordinates d hmiss k hd).toContinuousLinearEquiv.trans
    (RegularSphereFiber.normalCoordinates k hd).symm

theorem endpointColumns_eq_originalFrame (x : EndpointFiber d) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    endpointColumns d hmiss k hd a x =
      ((RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left k hd a).ambient x).comp
        (endpointColumnChange d hmiss k hd).toContinuousLinearMap := by
  let := fiberAtlas d k hd
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  apply ContinuousLinearMap.ext
  intro v
  change (SphereFiberNormalFrame.normalFrame d.leftMap d.smooth_left b d.regular_left k hd a
      ).ambient x (normalModelCoordinates d hmiss k hd v) =
    (SphereFiberNormalFrame.normalFrame d.leftMap d.smooth_left b d.regular_left k hd a
      ).ambient x (RegularSphereFiber.normalCoordinates k hd
        ((RegularSphereFiber.normalCoordinates k hd).symm
          (normalModelCoordinates d hmiss k hd v)))
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem endpointColumns_injective (x : EndpointFiber d) :
    Function.Injective (endpointColumns d hmiss k hd a x) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  rw [endpointColumns_eq_originalFrame]
  exact ((RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left k hd a
    ).ambient_injective x).comp (endpointColumnChange d hmiss k hd).injective

theorem endpointColumns_range (x : EndpointFiber d) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    (endpointColumns d hmiss k hd a x).range =
      ((RegularSphereFiber.embedding d.leftMap d.smooth_left b d.regular_left k hd
        ).normalProjection x).range := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  rw [endpointColumns_eq_originalFrame]
  exact (LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (endpointColumnChange d hmiss k hd).surjective)).trans
      ((RegularSphereFiber.frame d.leftMap d.smooth_left b d.regular_left k hd a).ambient_range x)

theorem frame_seamCollar (s : ℝ) (hs : s ∈ seamCollarTimes d) (x : EndpointFiber d) :
    letI := fiberAtlas d k hd;
    (euclideanNormalFraming d hmiss k hd a).ambient (seamCollarPoint d s hs x) =
      (spatialIsometry m).toContinuousLinearMap.comp (endpointColumns d hmiss k hd a x) := by
  let := fiberAtlas d k hd
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  rw [euclideanNormalFraming_seamCollar]
  apply ContinuousLinearMap.ext
  intro v
  exact (spatialIsometry_apply m _).symm

theorem orthonormal_seamCollar (s : ℝ) (hs : s ∈ seamCollarTimes d) (x : EndpointFiber d) :
    letI := fiberAtlas d k hd;
    ((euclideanNormalFraming d hmiss k hd a).orthonormal (seamCollarPoint d s hs x)).val =
      (spatialIsometry m).toContinuousLinearMap.comp
        (Orthonormalization.operator (endpointColumns d hmiss k hd a) x) := by
  let := fiberAtlas d k hd
  have h := Orthonormalization.operator_congr_value
    (euclideanNormalFraming d hmiss k hd a).ambient
    (fun y ↦ (spatialIsometry m).toContinuousLinearMap.comp (endpointColumns d hmiss k hd a y))
    (seamCollarPoint d s hs x) x (frame_seamCollar d hmiss k hd a s hs x)
  exact h.trans (Orthonormalization.operator_comp_linearIsometry (spatialIsometry m)
    (endpointColumns d hmiss k hd a) x)

theorem zeroColumns_seam (x : EndpointFiber d) :
    letI := fiberAtlas d k hd; letI := fiber_isManifold d k hd;
    ∀ r : (embedding d hmiss k hd).TubularRetraction,
      EmbeddedTime.zeroColumns (n := k) (embedding d hmiss k hd) r (timeZeroMap d)
        (euclideanNormalFraming d hmiss k hd a) (endpointToTimeZero d x) =
      (BlockSum.operator 1 (Orthonormalization.operator (endpointColumns d hmiss k hd a) x)).comp
        (OrthogonalFrameAppend.lastReflection ((m + 2) - (k + 1))).toContinuousLinearMap := by
  let := fiberAtlas d k hd
  let := fiber_isManifold d k hd
  intro r
  change OrthogonalFrameAppend.operator
    ((euclideanNormalFraming d hmiss k hd a).orthonormal
      (seamCollarPoint d 0 (zero_mem_seamCollarTimes d) x)).val
    (EmbeddedTime.outwardNormal (n := k) (embedding d hmiss k hd) r (timeZeroMap d)
      (endpointToTimeZero d x)) = _
  rw [orthonormal_seamCollar d hmiss k hd a 0 (zero_mem_seamCollarTimes d) x,
    outwardNormal_seam d hmiss k hd a x r]
  change OrthogonalFrameAppend.operator
      ((spatialIsometry m).toContinuousLinearMap.comp
        (Orthonormalization.operator (endpointColumns d hmiss k hd a) x)) (-timeUnit m) =
    (BlockSum.operator 1 (Orthonormalization.operator (endpointColumns d hmiss k hd a) x)).comp
      (OrthogonalFrameAppend.lastReflection ((m + 2) - (k + 1))).toContinuousLinearMap
  rw [OrthogonalFrameAppend.operator_neg, append_timeUnit_eq_block]

end NoExoticSixSphere.ReflectedSeam
