import Wikipedia.NoExoticSixSphere.RadialCompressionDerivative

/-! # The exact fiber derivative after a linear coordinate change -/

open scoped ContDiff

namespace NoExoticSixSphere

variable {K F : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasFDerivAt_framedCompression_linearCoordinates
    (x : F) (B : K →L[ℝ] F) (L : K →L[ℝ] K) (r : ℝ) (hr : 0 < r) :
    HasFDerivAt (fun v : K ↦ x + B (OpenPartialHomeomorph.univBall (0 : K) r (L v)))
      (r • B.comp L) 0 := by
  have hC : HasFDerivAt (OpenPartialHomeomorph.univBall (0 : K) r)
      (r • ContinuousLinearMap.id ℝ K) (L 0) := by
    simpa only [map_zero] using hasFDerivAt_univBall_zero r hr
  have hd := (B.hasFDerivAt.comp 0 (hC.comp 0 L.hasFDerivAt)).const_add x
  simpa using hd

end NoExoticSixSphere
