import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsGeometryAction

/-!
# Derivatives of the three actual triangle generators

The elliptic generators have derivatives `1 / (z + 1)^2` and
`1 / (z + width)^2`, and the cusp translation has derivative one.
These are computed from the actual determinant-one matrix actions,
using their strict complex derivatives through `UpperHalfPlane.ofComplex`.
The upper-half-plane neighborhood required for that coordinate inverse
is already part of the strict-derivative theorem; no global inverse
identity outside the upper half-plane is used.
-/

noncomputable section

open UpperHalfPlane

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

open SpecialPeriods

/-- The exact complex derivative of the actual order-three generator. -/
theorem actionGenerator₁_hasDerivAt (z : ℍ) :
    HasDerivAt
      (fun w : ℂ => (triangleGeometricRepresentation triangleGenerator₁ (ofComplex w) : ℂ))
      (1 / ((z : ℂ) + 1) ^ 2) (z : ℂ) := by
  simp only [triangleGeometricRepresentation_generator₁_apply]
  simpa [Triangle.slMultiplier, Triangle.slDenom, Triangle.generatorOneSL] using
    (Triangle.sl_hasStrictDerivAt_smul Triangle.generatorOneSL z).hasDerivAt

/-- The exact complex derivative of the actual order-four generator. -/
theorem actionGenerator₂_hasDerivAt (z : ℍ) :
    HasDerivAt
      (fun w : ℂ => (triangleGeometricRepresentation triangleGenerator₂ (ofComplex w) : ℂ))
      (1 / ((z : ℂ) + (Triangle.width : ℂ)) ^ 2) (z : ℂ) := by
  simp only [triangleGeometricRepresentation_generator₂_apply]
  have hm : Triangle.slMultiplier Triangle.generatorTwoSL z =
      1 / ((z : ℂ) + (Triangle.width : ℂ)) ^ 2 := by
    simp [Triangle.slMultiplier, Triangle.slDenom, Triangle.generatorTwoSL]
    ring
  rw [← hm]
  exact (Triangle.sl_hasStrictDerivAt_smul Triangle.generatorTwoSL z).hasDerivAt

/-- The actual source-normalized cusp translation has derivative one. -/
theorem actionCusp_hasDerivAt (z : ℍ) :
    HasDerivAt
      (fun w : ℂ => (triangleGeometricRepresentation triangleCuspGenerator (ofComplex w) : ℂ))
      1 (z : ℂ) := by
  simp only [triangleGeometricRepresentation_cusp, Triangle.realSLPermutation_apply]
  simpa [Triangle.slMultiplier, Triangle.slDenom] using
    (Triangle.sl_hasStrictDerivAt_smul Triangle.cuspSL z).hasDerivAt

@[simp] theorem actionDerivative_generator₁ (z : ℍ) :
    actionDerivative triangleGenerator₁ z = 1 / ((z : ℂ) + 1) ^ 2 :=
  (actionGenerator₁_hasDerivAt z).deriv

@[simp] theorem actionDerivative_generator₂ (z : ℍ) :
    actionDerivative triangleGenerator₂ z = 1 / ((z : ℂ) + (Triangle.width : ℂ)) ^ 2 :=
  (actionGenerator₂_hasDerivAt z).deriv

@[simp] theorem actionDerivative_cusp (z : ℍ) :
    actionDerivative triangleCuspGenerator z = 1 :=
  (actionCusp_hasDerivAt z).deriv

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
