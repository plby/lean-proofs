import Wikipedia.NoExoticSixSphere.TwistedBlockHomotopyReflection
import Wikipedia.NoExoticSixSphere.ImmersedSphereCorrectedParity
import Wikipedia.NoExoticSixSphere.ImmersedDerivativeHomotopyParity

/-!
# Source twisting preserves differences of immersed frame obstructions

Completeness of both actual frame parities and reflection of the common
twist identify equality of the two pairs of values. Since the values lie
in `ZMod 2`, this identifies their sums. Hence the source-twisted correction
that agrees with geometric disk parity is also ordinarily homotopy invariant.
No numerical value is assigned to the source twist itself.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere

theorem zmodTwo_cross_sum (a b c d : ZMod 2) : a + b = c + d ↔ a + c = b + d := by
  have h (a b c d : ZMod 2) (hs : a + b = c + d) : a + c = b + d := by
    rw [eq_sub_of_add_eq hs, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
    calc
      c + d + b + c = (b + d) + (c + c) := by abel
      _ = b + d := by rw [ZModModule.add_self, add_zero]
  exact ⟨h a b c d, h a c b d⟩

namespace EuclideanEmbedding

open GLOrthonormalization Stiefel SpanningDiskFrameCoordinates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem immersedSphereFrameParity_sum_eq_derivativeParity
    (f g : Sphere 3 → M)
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (hgd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) g s)) :
    e.immersedSphereFrameParity a f hf hd + e.immersedSphereFrameParity a g hg hgd =
      e.sphereDerivativeParity a f hf hd + e.sphereDerivativeParity a g hg hgd := by
  apply zmodTwo_eq_of_zero_iff
  simp only [add_eq_zero_iff_eq_neg, ZMod.neg_eq_self_mod_two]
  unfold immersedSphereFrameParity sphereDerivativeParity
  rw [Monomorphism.sphereParityOfDimension_eq_iff, Monomorphism.sphereParityOfDimension_eq_iff]
  exact twistedBlockMap_homotopic_iff
    (Nat.sub_add_cancel (e.dimension_le_ambient (f (pole 3)))).symm _ _

variable [IsManifold (𝓡 6) ∞ M] [CompactSpace M]

theorem immersedSphereCorrectedParity_homotopic (f g : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (hgd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) g s))
    (ht₀ : ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y)))
    (ht₁ : ∀ x y, x ≠ y → g x = g y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) g x).coprod (mfderiv (𝓡 3) (𝓡 6) g y)))
    (H : f.Homotopic g) :
    e.immersedSphereCorrectedParity a f hf hd = e.immersedSphereCorrectedParity a g hg hgd := by
  have h := e.derivativeCorrectedParity_homotopic a f g hf hg hd hgd ht₀ ht₁ H
  change e.sphereDerivativeParity a f hf hd + SphereSelfIntersections.unorderedParity f =
    e.sphereDerivativeParity a g hg hgd + SphereSelfIntersections.unorderedParity g at h
  have hsum := (zmodTwo_cross_sum _ _ _ _).mpr h
  have hframe := e.immersedSphereFrameParity_sum_eq_derivativeParity a f g hf hg hd hgd
  exact (zmodTwo_cross_sum _ _ _ _).mp (hframe.trans hsum)

end EuclideanEmbedding
end NoExoticSixSphere
