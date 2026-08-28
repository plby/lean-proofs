import Wikipedia.NoExoticSixSphere.CompactSphereSmoothOpenTube
import Wikipedia.NoExoticSixSphere.SevenDimensionalFramedProduct

/-!
# A native smooth four-normal tube for an embedded three-sphere

The original seven-dimensional normal framing constructs a genuine
four-dimensional normal complement. The compact-image tube and smooth
compression keep the original sphere fixed and put the whole open tube
inside any prescribed open neighborhood of its image.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

theorem exists_fourNormalSmoothOpenTube {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 7) M]
    [IsManifold (𝓡 7) ∞ M] (e : EuclideanEmbedding 7 M)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
    (hi : Injective f) (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
    (U : Set M) (hU : IsOpen U) (hfU : ∀ s, f s ∈ U) :
    ∃ Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞,
      Φ.source = univ ∧ Φ.target ⊆ U ∧ ∀ s, Φ (s, 0) = f s := by
  obtain ⟨D, ρ, -, -, T, A, -, -, hCs, hCn, hCr, -⟩ :=
    e.exists_framedProduct_of_dimension_seven a (spherePole 3) f hf hi hd
  let C := boundaryComplementOperator A.transverse
  have hiC (s : Sphere 3) : Injective (C s) := Stiefel.injective ⟨C s, hCn s⟩
  let : Nonempty M := ⟨f (spherePole 3)⟩
  obtain ⟨R⟩ := e.nonempty_retractionNear (isCompact_range hf.continuous)
  exact e.exists_compactSphereSmoothOpenTube_in_open f C R hf hi hCs hd hiC hCr U hU hfU

end NoExoticSixSphere.EuclideanEmbedding
