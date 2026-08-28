import Wikipedia.NoExoticSixSphere.ImmersedDerivativeHomotopyParity
import Wikipedia.NoExoticSixSphere.SelfTransverseSphereRepresentative

/-!
# A genuine homotopy invariant from corrected immersed derivative parity

Evaluate the actual derivative-frame obstruction plus the actual unordered
double-point count on a constructed self-transverse immersed representative.
The proved ordinary homotopy theorem removes dependence on that choice.
This is not yet a normalized quadratic refinement: its value on constants,
source-twist comparison, quadratic identity, and homological descent remain
separate obligations.
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

def sphereDerivativeInvariant (f : C(Sphere 3, M)) : ZMod 2 :=
  let R := e.exists_selfTransverse_immersed_homotopic r f
  e.immersedDerivativeCorrectedParity a R.choose R.choose_spec.1 R.choose_spec.2.2.1

theorem sphereDerivativeInvariant_eq_representative (f g : C(Sphere 3, M))
    (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) g s))
    (ht : ∀ x y, x ≠ y → g x = g y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) g x).coprod (mfderiv (𝓡 3) (𝓡 6) g y)))
    (H : f.Homotopic g) :
    e.sphereDerivativeInvariant a r f = e.immersedDerivativeCorrectedParity a g hg hd := by
  let R := e.exists_selfTransverse_immersed_homotopic r f
  exact e.derivativeCorrectedParity_homotopic a R.choose g R.choose_spec.1 hg
    R.choose_spec.2.2.1 hd R.choose_spec.2.2.2 ht (R.choose_spec.2.1.symm.trans H)

theorem sphereDerivativeInvariant_homotopic (f g : C(Sphere 3, M)) (H : f.Homotopic g) :
    e.sphereDerivativeInvariant a r f = e.sphereDerivativeInvariant a r g := by
  let R := e.exists_selfTransverse_immersed_homotopic r g
  exact e.sphereDerivativeInvariant_eq_representative a r f R.choose
    R.choose_spec.1 R.choose_spec.2.2.1 R.choose_spec.2.2.2 (H.trans R.choose_spec.2.1)

theorem sphereDerivativeInvariant_retraction_independent (r' : TubularRetraction e)
    (f : C(Sphere 3, M)) :
    e.sphereDerivativeInvariant a r f = e.sphereDerivativeInvariant a r' f := by
  let R := e.exists_selfTransverse_immersed_homotopic r' f
  exact e.sphereDerivativeInvariant_eq_representative a r f R.choose
    R.choose_spec.1 R.choose_spec.2.2.1 R.choose_spec.2.2.2 R.choose_spec.2.1

end NoExoticSixSphere.EuclideanEmbedding
