import Wikipedia.NoExoticSixSphere.SphereCollapseGermComparison
import Wikipedia.NoExoticSixSphere.SphereCollapseRegularValue
import Wikipedia.NoExoticSixSphere.CompactifiedEmbeddingDifferential
import Wikipedia.NoExoticSixSphere.RegularFiberIdentification
import Wikipedia.NoExoticSixSphere.StabilizedFiberFramedFilling

/-!
# A finite collapse nullhomotopy fills the original smooth manifold

The input is a nullhomotopy of an actual finite suspension of the constructed
framed collapse. Fiber-germ comparison transfers it to a smooth regular
representative. One further suspension ensures a positive-dimensional target.
The constructed compact normally framed filling has its entire native boundary
diffeomorphic to the original manifold, with its independently given atlas.
The ambient boundary inclusion is exactly the iterated equatorial embedding.

The nullhomotopy remains an explicit hypothesis. The filling's frame is the
constructed induced frame; equality with a prescribed original boundary frame
is not asserted. Neither detection nor final sphere rigidity is proved here.
-/

noncomputable section

open Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

open SphereMapSuspension

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  (d : e.FramedCollapseData a)

/-- A filling of the original atlas, conditional on the actual collapse nullhomotopy. -/
theorem exists_originalAtlas_filling_of_iterate_nullhomotopic
    (m : M) (r : ℕ) (hnull : (iterate d.sphereMap r).Nullhomotopic) :
    ∃ G : C(Sphere (e.ambientDimension + (r + 1)),
        Sphere ((e.ambientDimension - n) + (r + 1))),
      ∃ hG : ContMDiff (𝓡 (e.ambientDimension + (r + 1)))
        (𝓡 ((e.ambientDimension - n) + (r + 1))) ∞ G,
      ∃ hGreg : ∀ y, G y = equators (e.ambientDimension - n) (r + 1)
        (sphereZero (e.ambientDimension - n)) → Function.Surjective
          (mfderiv (𝓡 (e.ambientDimension + (r + 1)))
            (𝓡 ((e.ambientDimension - n) + (r + 1))) G y),
      ∃ A : SphereFiberFramedFilling G hG
        (equators (e.ambientDimension - n) (r + 1) (sphereZero (e.ambientDimension - n)))
        hGreg n (by have hn := e.dimension_le_ambient m; omega)
        (equators e.ambientDimension (r + 1) (e.compactifiedEmbedding m)),
        letI := A.topology;
        letI := A.atlas;
        letI := A.boundaryAtlas;
        ∃ D : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ {w : A.W // ((𝓡∂ 1).prod (𝓡 n)).IsBoundaryPoint w},
          ∀ x, A.inclusion (D x).val = WithLp.toLp 2
            (0, (equators e.ambientDimension (r + 1) (e.compactifiedEmbedding x)).val) := by
  obtain ⟨g, hg, -, hfiber, hreg, hgerm⟩ := d.exists_smoothSphereMap_regular
  have hn := e.dimension_le_ambient m
  have hd : e.ambientDimension = (e.ambientDimension - n) + n := by omega
  have hng : (iterate g r).Nullhomotopic :=
    (d.iterate_nullhomotopic_iff_of_fiber_germs g hfiber hgerm r).mp hnull
  have hnnext : (iterate g (r + 1)).Nullhomotopic := map_nullhomotopic hng
  let b := sphereZero (e.ambientDimension - n)
  let p := e.compactifiedEmbedding m
  obtain ⟨G, hG, hGreg, A, D, hD⟩ :=
    exists_framedFilling_of_nullhomotopic_iterate g hg b hreg n hd p (r + 1)
      (by omega) hnnext
  refine ⟨G, hG, hGreg, A, ?_⟩
  let := regularFiberAtlas g hg b hreg n (by simpa using hd)
  let := A.topology
  let := A.atlas
  let := A.boundaryAtlas
  let D₀ := diffeomorphToRegularFiber g hg b hreg n (by simpa using hd)
    e.compactifiedEmbedding e.contMDiff_compactifiedEmbedding
    e.compactifiedEmbedding_isEmbedding.injective e.injective_mfderiv_compactifiedEmbedding hfiber
  refine ⟨D₀.trans D, ?_⟩
  intro x
  change A.inclusion (D (D₀ x)).val = _
  have hv : (D₀ x).val = e.compactifiedEmbedding x := rfl
  rw [hD, hv]

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
