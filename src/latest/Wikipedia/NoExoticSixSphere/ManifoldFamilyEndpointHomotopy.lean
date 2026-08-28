import Wikipedia.NoExoticSixSphere.ManifoldSphereFrameOperator
import Wikipedia.NoExoticSixSphere.ManifoldFamilyLinkParity
import Wikipedia.NoExoticSixSphere.PartialFrameParityComplete

/-!
# The actual endpoint sphere operators are homotopic

Completeness of parity converts the checked boundary-obstruction equality
into a genuine homotopy. The dimension transport and normalization are
then removed, retaining the original endpoint sphere operators. The common
source-twist comparison gives equality of their geometric sphere parity.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (g : ℝ → Sphere 3 → M)
  (hg : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))
  (P : SphereFamily.ParityBallSystem g)

theorem puncturedFamilyFrameMap_zero
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ (g 0))
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) (g 0) s)) :
    (e.puncturedFamilyFrameMap a g hg P).comp (P.sphereInclusion (.inl false)) =
      (Monomorphism.normalize e.ambientDimension ((e.ambientDimension - 6) + 3)).comp
        (e.sphereFrameOperatorMap a (g 0) hf hd) := by
  apply ContinuousMap.ext
  intro s
  rfl

theorem puncturedFamilyFrameMap_one
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ (g 1))
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) (g 1) s)) :
    (e.puncturedFamilyFrameMap a g hg P).comp (P.sphereInclusion (.inl true)) =
      (Monomorphism.normalize e.ambientDimension ((e.ambientDimension - 6) + 3)).comp
        (e.sphereFrameOperatorMap a (g 1) hf hd) := by
  apply ContinuousMap.ext
  intro s
  rfl

theorem puncturedGlobalFrameMap_homotopic_iff (f h : C(Sphere 3, P.puncturedCylinder)) :
    ((e.puncturedGlobalFrameMap a g hg P).comp f).Homotopic
      ((e.puncturedGlobalFrameMap a g hg P).comp h) ↔
        ((e.puncturedFamilyFrameMap a g hg P).comp f).Homotopic
          ((e.puncturedFamilyFrameMap a g hg P).comp h) := by
  unfold puncturedGlobalFrameMap
  exact homotopic_dimensionHomeomorph_iff _ _
    ((e.puncturedFamilyFrameMap a g hg P).comp f) ((e.puncturedFamilyFrameMap a g hg P).comp h)

variable (hf₀ : ContMDiff (𝓡 3) (𝓡 6) ∞ (g 0))
  (hd₀ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) (g 0) s))
  (hf₁ : ContMDiff (𝓡 3) (𝓡 6) ∞ (g 1))
  (hd₁ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) (g 1) s))

include hg P in
theorem endpoint_frameOperator_homotopic
    (heven : Even (Nat.card (SphereFamily.singularParameters (n := 6) g))) :
    (e.sphereFrameOperatorMap a (g 0) hf₀ hd₀).Homotopic
      (e.sphereFrameOperatorMap a (g 1) hf₁ hd₁) := by
  have he := e.endpoint_familyBoundaryObstruction_eq a g hg P heven
  have H := (sphereThirdObstruction_eq_iff_homotopic ((e.ambientDimension - 6) + 1)
    ((e.puncturedGlobalFrameMap a g hg P).comp (P.sphereInclusion (.inl false)))
    ((e.puncturedGlobalFrameMap a g hg P).comp (P.sphereInclusion (.inl true)))).mp he
  have H' := (e.puncturedGlobalFrameMap_homotopic_iff a g hg P
    (P.sphereInclusion (.inl false)) (P.sphereInclusion (.inl true))).mp H
  rw [e.puncturedFamilyFrameMap_zero a g hg P hf₀ hd₀,
    e.puncturedFamilyFrameMap_one a g hg P hf₁ hd₁] at H'
  exact (Monomorphism.normalize_homotopic_iff _ _).mp H'

include hg P in
theorem endpoint_sphereParity_eq
    (heven : Even (Nat.card (SphereFamily.singularParameters (n := 6) g)))
    (hi₀ : Injective (g 0)) (hi₁ : Injective (g 1)) :
    e.sphereParity a (g 0) hf₀ hi₀ hd₀ = e.sphereParity a (g 1) hf₁ hi₁ hd₁ :=
  e.sphereParity_eq_of_frameOperator_homotopic a (g 0) hf₀ hd₀ hi₀ (g 1) hf₁ hd₁ hi₁
    (e.endpoint_frameOperator_homotopic a g hg P hf₀ hd₀ hf₁ hd₁ heven)

end NoExoticSixSphere.EuclideanEmbedding
