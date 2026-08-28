import Wikipedia.NoExoticSixSphere.StableSixSphereRegularRepresentative
import Wikipedia.NoExoticSixSphere.RegularSphereFiberEmbedding

/-!
# Nonzero actual stable classes have nonempty normally framed regular fibers

Smooth approximation and Sard provide the original map and regular value.
The genuine fiber is a compact smooth six-manifold in its constructed atlas;
its original ambient inclusion has the explicitly induced normal frame.
No connectivity of this fiber, and no equality with its own framed collapse
class, is inferred from these facts.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StableSixSphereMaps

theorem exists_nonempty_framed_regular_representative (c : Class) (hc : c ≠ nullClass) :
    ∃ (k : ℕ) (g : StageMap k),
      ∃ hg : ContMDiff (𝓡 (k + 8)) (𝓡 (k + 2)) ∞ g,
        ∃ (b : Sphere (k + 2))
          (hreg : ∀ x, g x = b → Surjective (mfderiv (𝓡 (k + 8)) (𝓡 (k + 2)) g x)),
          ofMap g = c ∧ Nonempty {x : Sphere (k + 8) // g x = b} ∧
          letI := regularFiberAtlas g hg b hreg 6 (by
            simp only [finrank_euclideanSpace_fin]);
          IsManifold (𝓡 6) ∞ {x : Sphere (k + 8) // g x = b} ∧
          CompactSpace {x : Sphere (k + 8) // g x = b} ∧
          Nonempty (SmoothRangeFrame (𝓡 6)
            (RegularSphereFiber.embedding g hg b hreg 6 (by omega)).normalProjection
            (RegularSphereFiber.embedding g hg b hreg 6 (by omega)).NormalModel) := by
  obtain ⟨k, g, hg, b, hreg, he, hne⟩ := exists_nonempty_smooth_regular_representative c hc
  refine ⟨k, g, hg, b, hreg, he, hne, ?_⟩
  let := regularFiberAtlas g hg b hreg 6 (by
    simp only [finrank_euclideanSpace_fin])
  refine ⟨regularFiber_isManifold g hg b hreg 6 (by
    simp only [finrank_euclideanSpace_fin]), RegularSphereFiber.fiber_compact g b, ?_⟩
  exact ⟨RegularSphereFiber.frame g hg b hreg 6 (by omega) (spherePole (k + 8))⟩

end NoExoticSixSphere.StableSixSphereMaps
