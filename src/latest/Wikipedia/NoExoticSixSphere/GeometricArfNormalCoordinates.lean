import Wikipedia.NoExoticSixSphere.NormalFrameCoordinateParity
import Wikipedia.NoExoticSixSphere.GeometricArfFrameHomotopy

/-!
# Fixed normal coordinates and normalization preserve the actual quadratic form and Arf invariant

Every original middle class has an actual embedded sphere representative.
The checked geometric sphere-parity identities therefore apply to the
original quadratic form on all classes, with independent tubular choices
and basepoints. Fixed coordinate equivalences need not preserve orientation.
Normalization after such a change is handled in its actual order.
This is frame-change invariance, not arbitrary framed-bordism invariance.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology
open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere

open GLOrthonormalization

namespace EuclideanEmbedding

attribute [local instance] modHomologyModule

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M)
  (a b : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r r' : TubularRetraction e) (m m' : M)
  [Subsingleton (π_ 2 M m)] [Subsingleton (π_ 2 M m')]

theorem modTwoHomologyQuadraticForm_eq_of_sphereParity_eq
    (h : ∀ (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
      (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)),
      e.sphereParity a f hf hi hd = e.sphereParity b f hf hi hd) :
    e.modTwoHomologyQuadraticForm a r m = e.modTwoHomologyQuadraticForm b r' m' := by
  ext c
  obtain ⟨f, hf, hi, hd, rfl⟩ := e.exists_embedded_modTwoMiddle_representative r m c
  rw [e.modTwoHomologyQuadraticForm_sphereClass a r m,
    e.modTwoHomologyQuadraticForm_sphereClass b r' m',
    e.geometricSphereParity_eq_of_embedding a r f hf hi.injective hd,
    e.geometricSphereParity_eq_of_embedding b r' f hf hi.injective hd]
  exact h f hf hi.injective hd

theorem modTwoHomologyQuadraticForm_eq_of_normal_coordinates
    (Q : Vector (e.ambientDimension - 6) ≃L[ℝ] Vector (e.ambientDimension - 6))
    (he : ∀ x, b.ambient x = (a.ambient x).comp Q.toContinuousLinearMap) :
    e.modTwoHomologyQuadraticForm a r m = e.modTwoHomologyQuadraticForm b r' m' :=
  e.modTwoHomologyQuadraticForm_eq_of_sphereParity_eq a b r r' m m'
    (e.sphereParity_eq_of_normal_coordinates a b Q he)

theorem modTwoHomologyQuadraticForm_normalized :
    e.modTwoHomologyQuadraticForm a.normalized r' m' = e.modTwoHomologyQuadraticForm a r m :=
  e.modTwoHomologyQuadraticForm_eq_of_sphereParity_eq a.normalized a r' r m' m
    (e.sphereParity_normalized a)

theorem modTwoHomologyQuadraticForm_normalized_recoordinateModel
    (Q : Vector (e.ambientDimension - 6) ≃L[ℝ] Vector (e.ambientDimension - 6)) :
    e.modTwoHomologyQuadraticForm (a.recoordinateModel Q).normalized r' m' =
      e.modTwoHomologyQuadraticForm a r m :=
  e.modTwoHomologyQuadraticForm_eq_of_sphereParity_eq (a.recoordinateModel Q).normalized a
    r' r m' m (e.sphereParity_normalized_recoordinateModel a Q)

end EuclideanEmbedding

namespace GeometricArf

open EuclideanEmbedding

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M)
  (a b : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r r' : TubularRetraction e) (m m' : M)
  [Subsingleton (π_ 2 M m)] [Subsingleton (π_ 2 M m')]

theorem invariant_eq_of_normal_coordinates
    (Q : Vector (e.ambientDimension - 6) ≃L[ℝ] Vector (e.ambientDimension - 6))
    (he : ∀ x, b.ambient x = (a.ambient x).comp Q.toContinuousLinearMap) :
    invariant e a r m = invariant e b r' m' :=
  invariant_eq_of_quadraticForm_eq e a b r r' m m'
    (e.modTwoHomologyQuadraticForm_eq_of_normal_coordinates a b r r' m m' Q he)

theorem invariant_recoordinateModel
    (Q : Vector (e.ambientDimension - 6) ≃L[ℝ] Vector (e.ambientDimension - 6)) :
    invariant e (a.recoordinateModel Q) r' m' = invariant e a r m :=
  (invariant_eq_of_normal_coordinates e a (a.recoordinateModel Q) r r' m m'
    Q (a.recoordinateModel_ambient Q)).symm

theorem invariant_normalized :
    invariant e a.normalized r' m' = invariant e a r m :=
  invariant_eq_of_quadraticForm_eq e a.normalized a r' r m' m
    (e.modTwoHomologyQuadraticForm_normalized a r r' m m')

theorem invariant_normalized_recoordinateModel
    (Q : Vector (e.ambientDimension - 6) ≃L[ℝ] Vector (e.ambientDimension - 6)) :
    invariant e (a.recoordinateModel Q).normalized r' m' = invariant e a r m :=
  invariant_eq_of_quadraticForm_eq e (a.recoordinateModel Q).normalized a r' r m' m
    (e.modTwoHomologyQuadraticForm_normalized_recoordinateModel a r r' m m' Q)

end GeometricArf
end NoExoticSixSphere

