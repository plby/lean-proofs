import Wikipedia.NoExoticSixSphere.FramedSlabData
import Wikipedia.NoExoticSixSphere.RelativeRegularCylinder

/-!
# A continuous sphere-map homotopy gives a compact framed slab

Smooth approximation, Sard, endpoint-preserving regularization, the actual
slab atlas, and its normal-frame construction are combined here. No regular
homotopy, slab atlas, frame, or boundary identification is an input.

This is the geometric homotopy-to-framed-slab direction for the induced
sphere-fiber frames. It does not assert that a collapse map is nullhomotopic,
or identify these frames with a specified stabilized frame after compactification.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere

theorem exists_framedCollaredCylinder {m n : ℕ} {f₀ f₁ : C(Sphere m, Sphere n)}
    (h₀ : ContMDiff (𝓡 m) (𝓡 n) ∞ f₀) (h₁ : ContMDiff (𝓡 m) (𝓡 n) ∞ f₁)
    (H : f₀.Homotopy f₁) (b : Sphere n)
    (hreg₀ : ∀ x, f₀ x = b → Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f₀ x))
    (hreg₁ : ∀ x, f₁ x = b → Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f₁ x))
    (k : ℕ) (hd : m = n + k) (a : Sphere m) :
    ∃ d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1,
      d.leftMap = f₀ ∧ d.rightMap = f₁ ∧
      H.toContinuousMap.HomotopicRel (d.map.comp CylinderTime.inclusion) CylinderTime.boundary ∧
      Nonempty (d.FramedSlabData k hd a) ∧
      CompactSpace (CylinderFiberSlab.slab d.map b 0 1) ∧
      Topology.IsClosedEmbedding d.slabEuclideanInclusion := by
  obtain ⟨d, hd₀, hd₁, hhom⟩ := exists_regularCollaredCylinder h₀ h₁ H b hreg₀ hreg₁
  exact ⟨d, hd₀, hd₁, hhom, d.nonempty_framedSlabData k hd a,
    CylinderFiberSlab.compactSpace d.map b 0 1, d.isClosedEmbedding_slabEuclideanInclusion⟩

end NoExoticSixSphere
