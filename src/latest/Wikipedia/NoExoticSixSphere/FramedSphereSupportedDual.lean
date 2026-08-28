import Wikipedia.NoExoticSixSphere.InternalSphereOpenTube
import Wikipedia.NoExoticSixSphere.OpenSphereTubeSupportedClass

/-!
# An actual supported cap-dual class for a framed embedded sphere

The internal tube is constructed from the supplied smooth embedded sphere
and its genuine normal frame in the original manifold. The original
normal class then extends to a relative class supported exactly on that
sphere's range. Its absolute cap is the original sphere fundamental-class
image. No existence of a tube or dual cohomology class is assumed.
-/

noncomputable section

open Function Set Topology
open scoped Manifold ContDiff
open Wikipedia.HopfProblem.SphereHomologyCoefficients

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

local instance sphereDualAmbientDimension : Fact (Module.finrank ℝ (Vector 6) = (3 + 2) + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (f : Sphere 3 → M)
  (C : Sphere 3 → Vector 3 →L[ℝ] Vector e.ambientDimension) (r : TubularRetraction e)
  (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
  (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 3 →L[ℝ] Vector e.ambientDimension) ∞ C)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
  (hiC : ∀ s, Injective (C s)) (hCr : ∀ s, (C s).range = e.sphereNormalSpace f s)

include r hi hC hd hiC hCr in
/-- The constructed relative dual is supported on the original embedded sphere itself. -/
theorem exists_supportedSphereDual :
    ∃ a : SupportedModTwoCohomology.Cohomology (range f) 3,
      ManifoldCapMap.dualityMap (E := Vector 6) 3 M 3 3 rfl
          (RelativeModTwoCochains.toAbsoluteCohomology (range f)ᶜ 3 a) =
        modHomologyMap 2 (⟨f, hf.continuous⟩ : C(Sphere 3, M)) 3
          (unitSphereModTopClass 2 2) := by
  obtain ⟨τ, hτ, hzero⟩ := e.exists_internalSphereOpenTube f C r hf hi hC hd hiC hCr
  have hcore : OpenSphereTubeCap.core τ = (⟨f, hf.continuous⟩ : C(Sphere 3, M)) :=
    ContinuousMap.ext hzero
  have hex : ∃ a : SupportedModTwoCohomology.Cohomology
      (range (OpenSphereTubeCap.core τ)) 3,
      ManifoldCapMap.dualityMap (E := Vector 6) 3 M 3 3 rfl
          (RelativeModTwoCochains.toAbsoluteCohomology (range (OpenSphereTubeCap.core τ))ᶜ 3 a) =
        modHomologyMap 2 (OpenSphereTubeCap.core τ) 3 (unitSphereModTopClass 2 2) := by
    refine ⟨OpenSphereTubeCap.supportedClass τ hτ, ?_⟩
    exact (congrArg (ManifoldCapMap.dualityMap (E := Vector 6) 3 M 3 3 rfl)
      (OpenSphereTubeCap.absoluteClass_eq_toAbsolute τ hτ)).symm.trans
        (OpenSphereTubeCap.cap_absoluteClass τ hτ)
  have hr : range (OpenSphereTubeCap.core τ) = range f :=
    congrArg (fun g : Sphere 3 → M => range g) (funext hzero)
  rw [hr] at hex
  simpa only [hcore] using hex

end NoExoticSixSphere.EuclideanEmbedding
