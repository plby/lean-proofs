import Wikipedia.NoExoticSixSphere.ClutchingExtension
import Wikipedia.NoExoticSixSphere.EquatorDimension
import Wikipedia.NoExoticSixSphere.FrameSmoothing
import Wikipedia.NoExoticSixSphere.NormalBundle

/-!
# The normal-bundle clutching obstruction of a smooth topological sphere

Move the embedding's actual normal projection to the standard topological
sphere, construct its hemisphere clutching map, then pull any resulting global
continuous frame back to the original manifold. Smoothing uses the independently
given smooth atlas; the homeomorphism is not assumed to be smooth.

The extension premise is explicit. No stable-nullhomotopy theorem or smooth
classification result is asserted here.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  (e : EuclideanEmbedding n M) (h : M ≃ₜ Sphere n)

/-- The actual normal projection expressed on the homeomorphic standard topological sphere. -/
noncomputable def sphereNormalProjection (x : Sphere n) :
    EuclideanSpace ℝ (Fin e.ambientDimension) →L[ℝ]
      EuclideanSpace ℝ (Fin e.ambientDimension) := e.normalProjection (h.symm x)

/-- Transporting the base topologically preserves continuity of the normal projection. -/
theorem continuous_sphereNormalProjection : Continuous (e.sphereNormalProjection h) :=
  e.contMDiff_normalProjection.continuous.comp h.symm.continuous

omit [IsManifold (𝓡 n) ∞ M] in
/-- Transporting the base does not change the idempotence of the normal projection. -/
theorem sphereNormalProjection_idempotent (x : Sphere n) :
    IsIdempotentElem (e.sphereNormalProjection h x) := e.normalProjection_idempotent (h.symm x)

/-- The normal bundle's actual clutching map on the sphere equator. -/
noncomputable def normalClutchingMap (v : Sphere n) :
    C(Equator v, InvertibleOperators e.NormalModel) :=
  sphereClutchingMap (e.sphereNormalProjection h) (e.sphereNormalProjection_idempotent h)
    (e.continuous_sphereNormalProjection h) v
    (e.normalModelEquiv (h.symm v)).symm (e.normalModelEquiv (h.symm (antipode v))).symm

/-- An extension of the normal clutching map gives a continuous frame on the original manifold. -/
noncomputable def continuousNormalFrameOfExtension (v : Sphere n)
    (g : C(ClosedHemisphere (antipode v), InvertibleOperators e.NormalModel))
    (hg : ∀ x : Equator v, g (equatorSouth v x) = e.normalClutchingMap h v x) :
    ContinuousRangeFrame e.normalProjection e.NormalModel := by
  let a := sphereFrameOfClutchingExtension (e.sphereNormalProjection h)
    (e.sphereNormalProjection_idempotent h) (e.continuous_sphereNormalProjection h) v
    (e.normalModelEquiv (h.symm v)).symm (e.normalModelEquiv (h.symm (antipode v))).symm g hg
  simpa only [sphereNormalProjection, h.symm_apply_apply] using a.comap h h.continuous

/-- A normal clutching extension yields a smooth frame in the candidate's original atlas. -/
theorem nonempty_smoothNormalFrame_of_extension (v : Sphere n)
    (g : C(ClosedHemisphere (antipode v), InvertibleOperators e.NormalModel))
    (hg : ∀ x : Equator v, g (equatorSouth v x) = e.normalClutchingMap h v x) :
    Nonempty (SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel) := by
  let : CompactSpace M := compactSpace_of_homeomorph h
  let : T2Space M := t2Space_of_homeomorph h
  exact nonempty_smoothRangeFrame_of_continuous e.normalProjection
    e.normalProjection_idempotent e.contMDiff_normalProjection
    (e.continuousNormalFrameOfExtension h v g hg)

/-- In dimension six the normal clutching obstruction is a concrete map from the five-sphere. -/
noncomputable def normalSixClutchingMap {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
    (e : EuclideanEmbedding 6 M) (h : M ≃ₜ Sphere 6) (v : Sphere 6) :
    C(Sphere 5, InvertibleOperators e.NormalModel) :=
  (e.normalClutchingMap h v).comp
    ⟨(equatorSixHomeomorph v).symm, (equatorSixHomeomorph v).symm.continuous⟩

end NoExoticSixSphere.EuclideanEmbedding
