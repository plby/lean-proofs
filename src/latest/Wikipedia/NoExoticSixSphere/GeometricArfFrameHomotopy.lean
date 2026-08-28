import Wikipedia.NoExoticSixSphere.ManifoldNormalFrameHomotopy
import Wikipedia.NoExoticSixSphere.GeometricArfInvariant

/-!
# Normal-frame homotopy invariance of the original geometric quadratic form

Every actual middle class has an embedded sphere representative. The
normal-frame homotopy preserves that representative's source-twisted
geometric parity, so it preserves the original quadratic form on all
classes. Tubular retractions and basepoints may differ at the endpoints.
Consequently the geometric Arf invariant is unchanged.

This concerns a homotopy of normal frames on the same actual embedding.
It does not assert arbitrary framed-bordism invariance or Arf detection.
-/

noncomputable section

open Function unitInterval
open scoped Manifold ContDiff Topology
open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

attribute [local instance] modHomologyModule

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M)
  (a b : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r r' : TubularRetraction e) (m m' : M)
  [Subsingleton (π_ 2 M m)] [Subsingleton (π_ 2 M m')]
  (A : C(I × M, e.NormalModel →L[ℝ] Vector e.ambientDimension))
  (hiA : ∀ p, Injective (A p))
  (hrA : ∀ p, (A p).range ≤ (e.normalProjection p.2).range)
  (hzero : ∀ x, A (0, x) = a.ambient x)
  (hone : ∀ x, A (1, x) = b.ambient x)

include hiA hrA hzero hone

theorem modTwoHomologyQuadraticForm_eq_of_normal_family :
    e.modTwoHomologyQuadraticForm a r m = e.modTwoHomologyQuadraticForm b r' m' := by
  ext c
  obtain ⟨f, hf, hi, hd, rfl⟩ := e.exists_embedded_modTwoMiddle_representative r m c
  rw [e.modTwoHomologyQuadraticForm_sphereClass a r m,
    e.modTwoHomologyQuadraticForm_sphereClass b r' m',
    e.geometricSphereParity_eq_of_embedding a r f hf hi.injective hd,
    e.geometricSphereParity_eq_of_embedding b r' f hf hi.injective hd]
  exact e.sphereParity_eq_of_normal_family a b A hiA hrA hzero hone f hf hi.injective hd

end NoExoticSixSphere.EuclideanEmbedding

namespace NoExoticSixSphere.GeometricArf

open GLOrthonormalization EuclideanEmbedding

attribute [local instance] modHomologyModule

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M)
  (a b : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r r' : TubularRetraction e) (m m' : M)
  [Subsingleton (π_ 2 M m)] [Subsingleton (π_ 2 M m')]

theorem invariant_eq_of_quadraticForm_eq
    (h : e.modTwoHomologyQuadraticForm a r m = e.modTwoHomologyQuadraticForm b r' m') :
    invariant e a r m = invariant e b r' m' := by
  let : Finite (ModHomology 2 M 3) :=
    compactManifold_modTwoMiddleHomology_finiteType (Vector 6) M m
  let : Fintype (ModHomology 2 M 3) := Fintype.ofFinite _
  exact congrArg (fun Q : QuadraticForm (ZMod 2) (ModHomology 2 M 3) ↦
    Arf.signParity (Arf.gaussSum Q)) h

theorem invariant_eq_of_normal_family
    (A : C(I × M, e.NormalModel →L[ℝ] Vector e.ambientDimension))
    (hiA : ∀ p, Injective (A p))
    (hrA : ∀ p, (A p).range ≤ (e.normalProjection p.2).range)
    (hzero : ∀ x, A (0, x) = a.ambient x)
    (hone : ∀ x, A (1, x) = b.ambient x) :
    invariant e a r m = invariant e b r' m' :=
  invariant_eq_of_quadraticForm_eq e a b r r' m m'
    (e.modTwoHomologyQuadraticForm_eq_of_normal_family a b r r' m m' A hiA hrA hzero hone)

end NoExoticSixSphere.GeometricArf
