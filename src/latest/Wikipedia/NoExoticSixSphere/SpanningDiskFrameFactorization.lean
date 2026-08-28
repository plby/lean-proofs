import Wikipedia.NoExoticSixSphere.SpanningDiskFrameCoordinates

/-!
# Exact factorization of the disk boundary operator through the original sphere frame

After a fixed coordinate shuffle, the combined normal-and-disk-derivative
operator is the original normal-and-sphere-derivative operator with six
identity columns. The only sphere-dependent change is the explicit source
twist. It is the same for all sphere maps with the same normal codimension.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.StabilizedSpanningDisk.DiskData

open GLOrthonormalization Stiefel SphereThreeTangentFrame SpanningDiskFrameCoordinates

variable {N k : ℕ} {b : Sphere 3} {f : Sphere 3 → Vector N}
  (D : DiskData b f) (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f)

include hf

theorem combinedOperator_comp_sourceSphere (s : Sphere 3) (a : Vector k →L[ℝ] Vector N) :
    (OperatorSum.operator (boundaryFrameOperator a) (fderiv ℝ D.toFun s.val)).comp
      (sourceSphere k s).toContinuousLinearMap =
        (targetCoordinates N).toContinuousLinearMap.comp
          ((BlockSum.operator 6 (OperatorSum.operator a (framedDerivative f s))).comp
            (sourceShuffle k).toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro v
  change OperatorSum.operator (boundaryFrameOperator a) (fderiv ℝ D.toFun s.val)
      (sourceSphere k s v) = targetCoordinates N
        (BlockSum.operator 6 (OperatorSum.operator a (framedDerivative f s)) (sourceShuffle k v))
  simp only [sourceSphere_apply, sourceShuffle_apply, OperatorSum.operator_apply,
    BlockSum.operator_apply, targetCoordinates_apply, targetExtra_apply,
    boundaryFrameOperator_apply, D.fderiv_radialCoordinates hf,
    ContinuousLinearEquiv.apply_symm_apply]
  rw [← map_add]
  congr 1
  simp only [Prod.mk_add_mk, add_zero, zero_add]

theorem combinedOperator_factorization (s : Sphere 3) (a : Vector k →L[ℝ] Vector N) :
    OperatorSum.operator (boundaryFrameOperator a) (fderiv ℝ D.toFun s.val) =
      (targetCoordinates N).toContinuousLinearMap.comp
        ((BlockSum.operator 6 (OperatorSum.operator a (framedDerivative f s))).comp
          (sourceTwist k s).toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro v
  change OperatorSum.operator (boundaryFrameOperator a) (fderiv ℝ D.toFun s.val) v =
    targetCoordinates N (BlockSum.operator 6 (OperatorSum.operator a (framedDerivative f s))
      (sourceTwist k s v))
  rw [sourceTwist_apply]
  have he := congrArg (fun A : Vector ((k + 5) + 4) →L[ℝ] Vector (N + 6) ↦
      A ((sourceSphere k s).symm v)) (D.combinedOperator_comp_sourceSphere hf s a)
  change OperatorSum.operator (boundaryFrameOperator a) (fderiv ℝ D.toFun s.val)
      (sourceSphere k s ((sourceSphere k s).symm v)) = targetCoordinates N
        (BlockSum.operator 6 (OperatorSum.operator a (framedDerivative f s))
          (sourceShuffle k ((sourceSphere k s).symm v))) at he
  rw [ContinuousLinearEquiv.apply_symm_apply] at he
  exact he

end NoExoticSixSphere.StabilizedSpanningDisk.DiskData
