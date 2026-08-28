import Wikipedia.SmoothSixDPoincare.NativeNormalBundleMaps
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# The normal-displacement differential along the zero section

In local normal-bundle coordinates, the derivative along the zero section is
the tangent-normal direct sum. This is the linear input to the normal-neighborhood
argument; it does not by itself supply a tubular neighborhood.
-/

open scoped Manifold ContDiff Bundle
open Bundle Function NoExoticSixSphere

namespace Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] (e : NativeEuclideanEmbedding E M)

/-- Normal displacement expressed in the local normal coordinates centered at `x₀`. -/
noncomputable def localNormalDisplacement (x₀ : M) (p : M × e.NormalModel) :
    EuclideanSpace ℝ (Fin e.ambientDimension) :=
  e.toFun p.1 + ProjectionBundle.ambientFromCoordinates
    e.normalProjection e.normalModelEquiv x₀ p.1 p.2

/-- The coordinate expression of normal displacement is smooth. -/
theorem contMDiff_localNormalDisplacement (x₀ : M) :
    ContMDiff ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
      (e.localNormalDisplacement x₀) :=
  (e.smooth.comp contMDiff_fst).add
    (((ProjectionBundle.contMDiff_ambientFromCoordinates e.normalProjection
      e.normalModelEquiv e.contMDiff_normalProjection x₀).comp contMDiff_fst).clm_apply
        contMDiff_snd)

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] in
/-- The base-direction restriction at zero is the embedding. -/
theorem localNormalDisplacement_zero (x₀ x : M) :
    e.localNormalDisplacement x₀ (x, 0) = e.toFun x := by
  simp [localNormalDisplacement]

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] in
/-- At a chart center, normal coordinates are the chosen normal-space identification. -/
theorem ambientNormalCoordinates_self (x : M) (v : e.NormalModel) :
    ProjectionBundle.ambientFromCoordinates e.normalProjection e.normalModelEquiv x x v =
      ((e.normalModelEquiv x).symm v : EuclideanSpace ℝ (Fin e.ambientDimension)) := by
  change e.normalProjection x (projectionIntertwiner
    (e.normalProjection x) (e.normalProjection x) ((e.normalModelEquiv x).symm v)) = _
  rw [projectionIntertwiner_self _ (e.normalProjection_idempotent x)]
  exact projection_apply_range (e.normalProjection x) (e.normalProjection_idempotent x) _

/-- Tangent and model-normal coordinates together identify the ambient vector space. -/
noncomputable def normalLinearSplitting (x : M) :
    (TangentSpace (𝓘(ℝ, E)) x × e.NormalModel) ≃L[ℝ]
      EuclideanSpace ℝ (Fin e.ambientDimension) :=
  ((ContinuousLinearEquiv.refl ℝ (TangentSpace (𝓘(ℝ, E)) x)).prodCongr
    ((e.normalModelEquiv x).symm.trans (e.normalSpaceEquiv x))).trans
      (e.tangentNormalEquiv x)

omit [IsManifold (𝓘(ℝ, E)) ∞ M] in
/-- The splitting adds the embedded tangent vector to the actual normal vector. -/
theorem normalLinearSplitting_apply (x : M) (v : TangentSpace (𝓘(ℝ, E)) x × e.NormalModel) :
    e.normalLinearSplitting x v = mvfderiv (𝓘(ℝ, E)) e.toFun x v.1 +
      ((e.normalModelEquiv x).symm v.2 : EuclideanSpace ℝ (Fin e.ambientDimension)) := rfl

/-- In local normal coordinates, the derivative along zero is the tangent-normal splitting. -/
theorem mvfderiv_localNormalDisplacement_zero (x : M) :
    mvfderiv ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (e.localNormalDisplacement x) (x, 0) =
      (e.normalLinearSplitting x).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  have hd := (e.contMDiff_localNormalDisplacement x).mdifferentiable (by simp) (x, 0)
  have hprod := mfderiv_prod_eq_add_apply
    (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, e.NormalModel)) (I'' := 𝓡 e.ambientDimension)
    (v := v) hd
  have hleft : (fun y : M ↦ e.localNormalDisplacement x (y, 0)) = e.toFun :=
    funext (e.localNormalDisplacement_zero x)
  let C : e.NormalModel →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension) :=
    (e.normalProjection x).range.subtypeL.comp (e.normalModelEquiv x).symm.toContinuousLinearMap
  have hright : (fun y : e.NormalModel ↦ e.localNormalDisplacement x (x, y)) =
      (fun y ↦ e.toFun x + C y) := by
    funext y
    exact congrArg (e.toFun x + ·) (e.ambientNormalCoordinates_self x y)
  have hC : mfderiv 𝓘(ℝ, e.NormalModel) (𝓡 e.ambientDimension)
      (fun y ↦ e.toFun x + C y) (0 : e.NormalModel) = C :=
    (C.hasFDerivAt.const_add (e.toFun x)).hasMFDerivAt.mfderiv
  change mfderiv ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension)
    (e.localNormalDisplacement x) (x, 0) v = _
  rw [hprod, hleft, hright, hC]
  rfl

/-- The normal-displacement differential is invertible at the center of every zero chart. -/
theorem localNormalDisplacement_derivative_isInvertible (x : M) :
    (mvfderiv ((𝓘(ℝ, E)).prod 𝓘(ℝ, e.NormalModel))
      (e.localNormalDisplacement x) (x, 0)).IsInvertible :=
  ⟨e.normalLinearSplitting x, (e.mvfderiv_localNormalDisplacement_zero x).symm⟩

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] in
/-- The local expression is the actual displacement of the inverse fiber coordinates. -/
theorem localNormalDisplacement_eq (x₀ : M) (p : M × e.NormalModel) :
    e.localNormalDisplacement x₀ p =
      e.normalDisplacement ⟨p.1, ProjectionBundle.fromCoordinates
        e.normalProjection e.normalModelEquiv x₀ p.1 p.2⟩ := rfl

end Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding
