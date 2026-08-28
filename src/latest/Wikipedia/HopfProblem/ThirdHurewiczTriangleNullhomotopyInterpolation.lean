import Wikipedia.HopfProblem.ThirdHurewiczTriangleNullhomotopyBoundary
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTetrahedronBasic

/-!
# Interpolating from the triangle to its square round trip

Affine interpolation preserves every face because both endpoints share
each zero barycentric coordinate. Composing with an actual based triangle
therefore gives a homotopy relative to its whole boundary.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

/-- The actual triangle-to-square-to-triangle composite. -/
def triangleReturnComposition : C(Simplex 2, Simplex 2) :=
  triangleCubeQuotient.comp triangleCubicalReturn

@[simp] theorem triangleReturnComposition_apply (s : Simplex 2) :
    triangleReturnComposition s = triangleCubeQuotient (triangleCubicalReturn s) := rfl

/-- A continuous affine homotopy from the identity to the round trip. -/
def triangleReturnInterpolation : C(I × Simplex 2, Simplex 2) :=
  tetrahedronSimplexBlendMap (ContinuousMap.id (Simplex 2)) triangleReturnComposition

@[simp] theorem triangleReturnInterpolation_zero (s : Simplex 2) :
    triangleReturnInterpolation (0, s) = s :=
  tetrahedronSimplexBlend_zero s (triangleReturnComposition s)

@[simp] theorem triangleReturnInterpolation_one (s : Simplex 2) :
    triangleReturnInterpolation (1, s) = triangleReturnComposition s :=
  tetrahedronSimplexBlend_one s (triangleReturnComposition s)

theorem triangleReturnInterpolation_coordinate_zero (t : I) (s : Simplex 2)
    (i : Fin 3) (hi : s i = 0) : triangleReturnInterpolation (t, s) i = 0 :=
  tetrahedronSimplexBlend_zero_coordinate t s (triangleReturnComposition s) i hi
    (triangleCubicalReturn_quotient_zero s i hi)

/-- The entire interpolation stays in each face containing its starting point. -/
theorem triangleReturnInterpolation_boundary (t : I) (s : Simplex 2)
    (hs : s ∈ triangleBoundary) : triangleReturnInterpolation (t, s) ∈ triangleBoundary := by
  obtain ⟨i, hi⟩ := hs
  exact ⟨i, triangleReturnInterpolation_coordinate_zero t s i hi⟩

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The actual based triangle is homotopic, relative to its whole boundary,
to its native generalized loop precomposed with the explicit return map. -/
def triangleReturnHomotopy (τ : BasedTriangle x) :
    τ.val.HomotopyRel ((basedTriangleLoop τ).val.comp triangleCubicalReturn)
      triangleBoundary where
  toFun z := τ.val (triangleReturnInterpolation z)
  continuous_toFun := τ.val.continuous.comp triangleReturnInterpolation.continuous
  map_zero_left s := congrArg τ.val (triangleReturnInterpolation_zero s)
  map_one_left s := congrArg τ.val (triangleReturnInterpolation_one s)
  prop' t s hs :=
    (τ.property _ (triangleReturnInterpolation_boundary t s hs)).trans (τ.property s hs).symm

end Wikipedia.HopfProblem.ThirdHurewicz
