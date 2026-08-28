import Wikipedia.NoExoticSixSphere.ImmersedFrameDerivativeComparison
import Wikipedia.NoExoticSixSphere.GeometricDerivativeInvariant

/-!
# Choice-independent geometric sphere parity for arbitrary continuous maps

The value is the actual source-twisted frame obstruction plus the actual
unordered double-point count of a constructed self-transverse immersion.
Ordinary homotopy invariance proves independence of the representative and
tubular retraction. For every embedded smooth immersive representative it
agrees with the existing geometric spanning-disk parity.

The quadratic identity, descent to middle homology, and bordism detection
are not asserted by this construction.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)

def geometricSphereParity (f : C(Sphere 3, M)) : ZMod 2 :=
  let R := e.exists_selfTransverse_immersed_homotopic r f
  e.immersedSphereCorrectedParity a R.choose R.choose_spec.1 R.choose_spec.2.2.1

theorem geometricSphereParity_eq_representative (f g : C(Sphere 3, M))
    (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) g s))
    (ht : ∀ x y, x ≠ y → g x = g y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) g x).coprod (mfderiv (𝓡 3) (𝓡 6) g y)))
    (H : f.Homotopic g) :
    e.geometricSphereParity a r f = e.immersedSphereCorrectedParity a g hg hd := by
  let R := e.exists_selfTransverse_immersed_homotopic r f
  exact e.immersedSphereCorrectedParity_homotopic a R.choose g R.choose_spec.1 hg
    R.choose_spec.2.2.1 hd R.choose_spec.2.2.2 ht (R.choose_spec.2.1.symm.trans H)

theorem geometricSphereParity_homotopic (f g : C(Sphere 3, M)) (H : f.Homotopic g) :
    e.geometricSphereParity a r f = e.geometricSphereParity a r g := by
  let R := e.exists_selfTransverse_immersed_homotopic r g
  exact e.geometricSphereParity_eq_representative a r f R.choose
    R.choose_spec.1 R.choose_spec.2.2.1 R.choose_spec.2.2.2 (H.trans R.choose_spec.2.1)

theorem geometricSphereParity_retraction_independent (r' : TubularRetraction e)
    (f : C(Sphere 3, M)) :
    e.geometricSphereParity a r f = e.geometricSphereParity a r' f := by
  let R := e.exists_selfTransverse_immersed_homotopic r' f
  exact e.geometricSphereParity_eq_representative a r f R.choose
    R.choose_spec.1 R.choose_spec.2.2.1 R.choose_spec.2.2.2 R.choose_spec.2.1

theorem geometricSphereParity_eq_of_embedding (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    e.geometricSphereParity a r f = e.sphereParity a f hf hi hd := by
  have ht : ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y)) :=
    fun x y hne heq ↦ (hne (hi heq)).elim
  exact (e.geometricSphereParity_eq_representative a r f f hf hd ht
    (ContinuousMap.Homotopic.refl f)).trans
    (e.immersedSphereCorrectedParity_eq_sphereParity a f hf hd hi)

end NoExoticSixSphere.EuclideanEmbedding
