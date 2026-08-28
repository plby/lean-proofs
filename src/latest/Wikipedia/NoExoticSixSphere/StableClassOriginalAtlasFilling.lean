import Wikipedia.NoExoticSixSphere.StableSixSphereCollapse
import Wikipedia.NoExoticSixSphere.OriginalAtlasFramedFilling

/-!
# An actual vanishing stable collapse class fills the original six-manifold

The directed-limit equality supplies a finite nullhomotopy. The existing
smooth regular-fiber construction then gives a compact normally framed
seven-dimensional filling, whose entire native boundary is diffeomorphic
to the original manifold with its supplied atlas.

The stable-class equality is an explicit hypothesis, not a supplied
classification axiom. Its proof from the candidate's zero Arf invariant
is still missing. The induced boundary frame is not identified with a
separately prescribed original frame in this statement.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

open SphereMapSuspension

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a)

theorem exists_originalAtlas_filling_of_stable_class_zero (m : M)
    (hd : 8 ≤ e.ambientDimension)
    (hz : d.sixthStableClass hd = StableSixSphereMaps.nullClass) :
    ∃ r : ℕ,
      ∃ G : C(Sphere (e.ambientDimension + (r + 1)),
          Sphere ((e.ambientDimension - 6) + (r + 1))),
        ∃ hG : ContMDiff (𝓡 (e.ambientDimension + (r + 1)))
          (𝓡 ((e.ambientDimension - 6) + (r + 1))) ∞ G,
        ∃ hGreg : ∀ y, G y = equators (e.ambientDimension - 6) (r + 1)
          (sphereZero (e.ambientDimension - 6)) → Function.Surjective
            (mfderiv (𝓡 (e.ambientDimension + (r + 1)))
              (𝓡 ((e.ambientDimension - 6) + (r + 1))) G y),
        ∃ A : SphereFiberFramedFilling G hG
          (equators (e.ambientDimension - 6) (r + 1) (sphereZero (e.ambientDimension - 6)))
          hGreg 6 (by omega)
          (equators e.ambientDimension (r + 1) (e.compactifiedEmbedding m)),
          letI := A.topology;
          letI := A.atlas;
          letI := A.boundaryAtlas;
          ∃ D : M ≃ₘ⟮𝓡 6, 𝓡 6⟯ {w : A.W // ((𝓡∂ 1).prod (𝓡 6)).IsBoundaryPoint w},
            ∀ x, A.inclusion (D x).val = WithLp.toLp 2
              (0, (equators e.ambientDimension (r + 1) (e.compactifiedEmbedding x)).val) := by
  obtain ⟨r, hr⟩ := (d.sixthStableClass_eq_null_iff hd).mp hz
  exact ⟨r, d.exists_originalAtlas_filling_of_iterate_nullhomotopic m r hr⟩

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
