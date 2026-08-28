import Wikipedia.NoExoticSixSphere.EmbeddedTimeIntegralRelationAnnulus
import Wikipedia.NoExoticSixSphere.EmbeddedTimeSmoothAnnulusParity

/-!
# Actual boundary parity equality from separated integral relations

Two separated embedded boundary three-spheres with the same integral
image in the actual two-connected half have equal parity for the original
outward boundary frame. The smooth positive-time annulus, its boundary
immersions and time signs, and its proper generic perturbation are all
constructed. No cylinder presentation or connectedness of the full boundary
is assumed. This theorem does not replace the full mod-two kernel by the
reduction of the integral kernel.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse TimeCollar
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  [ChartedSpace (Vector (6 + 1)) M] [IsManifold (𝓡 (6 + 1)) ∞ M]
  (e : EuclideanEmbedding (6 + 1) M) (r : e.TubularRetraction) (t : C(M, ℝ))
  (ht : ContMDiff (𝓡 (6 + 1)) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 (6 + 1)) 𝓘(ℝ, ℝ) t x))
  (a : SmoothRangeFrame (𝓡 (6 + 1)) e.normalProjection e.NormalModel) (m : M)
  (C : TimeCollar t B) [SimplyConnectedSpace (NonnegativeHalf t)] (w : NonnegativeHalf t)
  [hW₂ : Subsingleton (π_ 2 (NonnegativeHalf t) w)]

include C w hW₂ in
theorem sphereParity_eq_of_separated_integral_relation
    (f₀ f₁ : C(Sphere 3, {x : M // t x = 0}))
    (hdis : ∀ s u, f₀ s ≠ f₁ u)
    (hclass : singularHomologyMap (TimeCollarDisk.zeroToHalf t) 3
      (SmoothCube.integralSphereClass f₀) =
      singularHomologyMap (TimeCollarDisk.zeroToHalf t) 3 (SmoothCube.integralSphereClass f₁)) :
    letI := zeroAtlas t ht hreg;
    ∀ (hf₀ : ContMDiff (𝓡 3) (𝓡 6) ∞ f₀) (hi₀ : Injective f₀)
      (hd₀ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f₀ s))
      (hf₁ : ContMDiff (𝓡 3) (𝓡 6) ∞ f₁) (hi₁ : Injective f₁)
      (hd₁ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f₁ s)),
      (zeroEmbedding e t ht hreg).sphereParity (zeroNormalFrame e r t ht hreg a m)
        f₀ hf₀ hi₀ hd₀ =
      (zeroEmbedding e t ht hreg).sphereParity (zeroNormalFrame e r t ht hreg a m)
        f₁ hf₁ hi₁ hd₁ := by
  let := zeroAtlas t ht hreg
  intro hf₀ hi₀ hd₀ hf₁ hi₁ hd₁
  obtain ⟨g, hgs, hb₀, hb₁, hgp, hgi, hheight₀, hheight₁⟩ :=
    exists_smooth_annulus_of_integral_relation e r t ht hreg C w f₀ f₁ hclass
      hf₀ hi₀ hd₀ hf₁ hi₁ hd₁
  exact sphereParity_eq_of_smooth_annulus e r t ht hreg a m f₀ f₁ g hgs hb₀ hb₁ hdis
    hgi hgp hheight₀ hheight₁ hf₀ hi₀ hd₀ hf₁ hi₁ hd₁

end NoExoticSixSphere.EmbeddedTime
