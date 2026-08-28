import Wikipedia.HopfProblem.DegreeCollapseSphereFiniteRepresentative

/-!
# The original zero slice is a smooth immersion away from the pole

The finite coordinate expression is the literal continuous linear inclusion
p ↦ (p, 0). All derivatives below use the original sphere atlases.
-/

noncomputable section

open scoped Topology Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereSliceImmersion

open NoExoticSixSphere FiniteSphereProductCharts SphereFiniteRepresentative

theorem slice_point (n : ℕ) (p : V n) :
    ProductSphereFiber.slice n (point n p) = (lineChart n).symm (p, (0 : ℝ)) := by
  rw [slice_finite n (point_ne_pole n p), projection_point]

theorem contMDiffAt_slice_point (n : ℕ) (p : V n) :
    ContMDiffAt (𝓡 n) (𝓡 (n + 1)) ∞ (ProductSphereFiber.slice n) (point n p) := by
  apply SphereChartRegularity.contMDiffAt_of_inverse_square
    (ContinuousLinearEquiv.refl ℝ (V n)) (lineCoordinates n)
    (ProductSphereFiber.slice n) (ContinuousLinearMap.inl ℝ (V n) ℝ) p
  · exact (ContinuousLinearMap.inl ℝ (V n) ℝ).contDiff.contMDiff.contMDiffAt
  · exact Filter.Eventually.of_forall (slice_point n)

theorem slice_point_mfderiv_injective (n : ℕ) (p : V n) :
    Function.Injective (mfderiv (𝓡 n) (𝓡 (n + 1)) (ProductSphereFiber.slice n)
      (point n p)) := by
  apply SphereChartRegularity.mfderiv_injective_of_inverse_square
    (ContinuousLinearEquiv.refl ℝ (V n)) (lineCoordinates n)
    (ProductSphereFiber.slice n) (ContinuousLinearMap.inl ℝ (V n) ℝ) p
  · exact (ContinuousLinearMap.inl ℝ (V n) ℝ).contDiff.contMDiff.contMDiffAt
  · apply (SphereChartRegularity.mfderiv_injective_iff_fderiv
      (ContinuousLinearMap.inl ℝ (V n) ℝ) p).mpr
    rw [(ContinuousLinearMap.inl ℝ (V n) ℝ).fderiv]
    intro a b h
    exact congrArg Prod.fst h
  · exact Filter.Eventually.of_forall (slice_point n)

theorem contMDiffAt_slice (n : ℕ) {x : Sphere n} (hx : x ≠ spherePole n) :
    ContMDiffAt (𝓡 n) (𝓡 (n + 1)) ∞ (ProductSphereFiber.slice n) x :=
  point_projection n hx ▸ contMDiffAt_slice_point n (sphereProjection n x)

theorem slice_mfderiv_injective (n : ℕ) {x : Sphere n} (hx : x ≠ spherePole n) :
    Function.Injective (mfderiv (𝓡 n) (𝓡 (n + 1)) (ProductSphereFiber.slice n) x) :=
  point_projection n hx ▸ slice_point_mfderiv_injective n (sphereProjection n x)

end Wikipedia.HopfProblem.DegreeCollapse.SphereSliceImmersion

