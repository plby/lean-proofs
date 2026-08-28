import Wikipedia.NoExoticSixSphere.ReflectedSeamStateFrame
import Wikipedia.NoExoticSixSphere.CollaredFillingConnectivity

/-!
# The original endpoint frame reaches the actual two-connected filling boundary

The initial reflected-seam formula is composed with the complete framed
connectivity construction. The filling is parametrized by the ORIGINAL
endpoint regular-fiber atlas. Its full boundary-frame formula retains the
ordered endpoint coordinate change, orthonormalization, outward reflection,
and every subsequent ordinary stabilization. No comparison is supplied as
an extra hypothesis to the existence theorem.

This still starts from a genuine regular cylinder with omitted right fiber;
it neither proves collapse nullity nor supplies a general two-ended slab.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.ReflectedSeam

open GLOrthonormalization Stiefel Wikipedia.HopfProblem
open DegreeCollapse ReflectedCylinder SingularMayerVietoris

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hmiss : ∀ x, d.rightMap x ≠ b) (hd : m = n + 6) (a : Sphere m)
  (x₀ : EndpointFiber d) {U : CollaredSevenState (EndpointFiber d)}

def endpointFilling
    (F : CollaredFillingBoundary.Comparison (referenceLowCollaredState d hmiss hd a) U x₀) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    FramedSevenFilling (𝓡 6) (EndpointFiber d) := by
  let S := referenceLowCollaredState d hmiss hd a
  let := S.zeroAtlas
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  exact (CollaredFillingBoundary.fillingOfComparison F).reparametrizeBoundary
    (referenceLowStateZeroDiffeomorph d hmiss hd a)

theorem endpointFilling_boundary_point
    (F : CollaredFillingBoundary.Comparison (referenceLowCollaredState d hmiss hd a) U x₀)
    (x : EndpointFiber d) :
    letI := (referenceLowCollaredState d hmiss hd a).zeroAtlas;
    letI := U.halfBoundaryAtlas;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    ((endpointFilling d hmiss hd a x₀ F).boundaryDiffeomorph x).val =
      (F.diffeomorph (referenceLowStateZeroDiffeomorph d hmiss hd a x)).val := by
  let := (referenceLowCollaredState d hmiss hd a).zeroAtlas
  let := U.halfBoundaryAtlas
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  rfl

theorem endpoint_boundary_frame
    (F : CollaredFillingBoundary.Comparison (referenceLowCollaredState d hmiss hd a) U x₀)
    (x : EndpointFiber d) :
    letI := (referenceLowCollaredState d hmiss hd a).zeroAtlas;
    letI := U.halfBoundaryAtlas;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    ∀ v : Vector (((m + 2) - 6) + F.extra),
      (CollaredFillingBoundary.normalFrame U (U.collar.zeroPoint x₀).val).ambient
          (F.diffeomorph (referenceLowStateZeroDiffeomorph d hmiss hd a x)) (F.normal v) =
        F.ambient (BlockSum.operator F.extra
          (BlockSum.operator 1 (Orthonormalization.operator (endpointColumns d hmiss 6 hd a) x))
          (OrthogonalFrameAppend.extendColumnChange
            (sixColumnChange d hmiss hd
              (CollaredZero.referencePoint (referenceLowCollaredState d hmiss hd a) x₀))
            F.extra v)) := by
  let S := referenceLowCollaredState d hmiss hd a
  let := S.zeroAtlas
  let := U.halfBoundaryAtlas
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let E := referenceLowStateZeroDiffeomorph d hmiss hd a
  let y := CollaredZero.referencePoint S x₀
  intro v
  have hs : ((CollaredZero.normalFrame S y).ambient (E x)) =
      (BlockSum.operator 1 (Orthonormalization.operator (endpointColumns d hmiss 6 hd a) x)).comp
        (sixColumnChange d hmiss hd y).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    exact referenceState_sixFrame d hmiss hd a y x
  have h := F.frame_eq_of_source_columns (E x)
    (BlockSum.operator 1 (Orthonormalization.operator (endpointColumns d hmiss 6 hd a) x))
    (sixColumnChange d hmiss hd y) hs v
  dsimp only [E, y, S] at h
  exact h

theorem exists_twoConnected_endpoint_filling [SimplyConnectedSpace (EndpointFiber d)]
    [Subsingleton (SingularHomology (EndpointFiber d) 2)] :
    ∃ U : CollaredSevenState (EndpointFiber d),
      ∃ F : CollaredFillingBoundary.Comparison (referenceLowCollaredState d hmiss hd a) U x₀,
        letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
        let W := endpointFilling d hmiss hd a x₀ F;
        letI := W.topology;
        SimplyConnectedSpace W.W ∧ ∀ w : W.W, Subsingleton (π_ 2 W.W w) := by
  obtain ⟨U, F, hW, hpi⟩ := CollaredFillingConnectivity.exists_twoConnected_framed_filling
    (referenceLowCollaredState d hmiss hd a) x₀
  exact ⟨U, F, hW, hpi⟩

end NoExoticSixSphere.ReflectedSeam
