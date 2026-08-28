import Wikipedia.HopfProblem.DegreeCollapseNativeNullCylinder
import Wikipedia.NoExoticSixSphere.OriginalAtlasFramedFilling

/-!

# The actual stabilized collapse cylinder retains the original native manifold

Unlike the abstract framed-filling package, this theorem retains the actual
regular collared cylinder needed by the reflection construction. Its left
map is homotopic to the specified stabilized collapse. The original atlas
is carried to its specified native regular-fiber atlas, with the underlying
map exactly the iterated equatorial compactified embedding.

The finite suspension nullhomotopy is still an explicit hypothesis. No
connectivity or homology of the resulting filling is inferred from it.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse

open NoExoticSixSphere SphereMapSuspension

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}

theorem exists_original_atlas_cylinder_of_iterate_nullhomotopic
    (d : e.FramedCollapseData a) (m : M) (r : ℕ)
    (hnull : (iterate d.sphereMap r).Nullhomotopic) :
    ∃ C : RegularCollaredCylinder (M := Sphere (e.ambientDimension + (r + 1)))
        (𝓡 (e.ambientDimension + (r + 1)))
        (𝓡 ((e.ambientDimension - n) + (r + 1)))
        (equators (e.ambientDimension - n) (r + 1)
          (sphereZero (e.ambientDimension - n))) 0 1,
      (iterate d.sphereMap (r + 1)).Homotopic C.leftMap ∧
      (∀ x, C.rightMap x ≠ equators (e.ambientDimension - n) (r + 1)
        (sphereZero (e.ambientDimension - n))) ∧
      letI := regularFiberAtlas C.leftMap C.smooth_left
        (equators (e.ambientDimension - n) (r + 1) (sphereZero (e.ambientDimension - n)))
        C.regular_left n (by
          simp only [finrank_euclideanSpace_fin]
          have hn := e.dimension_le_ambient m
          omega)
      ∃ D : M ≃ₘ⟮𝓡 n, 𝓡 n⟯
          {y : Sphere (e.ambientDimension + (r + 1)) //
            C.leftMap y = equators (e.ambientDimension - n) (r + 1)
              (sphereZero (e.ambientDimension - n))},
        ∀ x, (D x).val = equators e.ambientDimension (r + 1)
          (e.compactifiedEmbedding x) := by
  obtain ⟨g, hg, H, hfiber, hreg, _⟩ := d.exists_smoothSphereMap_regular
  have hn := e.dimension_le_ambient m
  have hd : e.ambientDimension = (e.ambientDimension - n) + n := by omega
  have hgn : (iterate g r).Nullhomotopic := by
    obtain ⟨c, hc⟩ := hnull
    exact ⟨c, (iterate_homotopic H r).symm.trans hc⟩
  let _ := regularFiberAtlas g hg (sphereZero (e.ambientDimension - n)) hreg n
    (by simpa using hd)
  let D₀ := diffeomorphToRegularFiber g hg (sphereZero (e.ambientDimension - n)) hreg n
    (by simpa using hd) e.compactifiedEmbedding e.contMDiff_compactifiedEmbedding
    e.compactifiedEmbedding_isEmbedding.injective e.injective_mfderiv_compactifiedEmbedding hfiber
  obtain ⟨C, HC, hmiss, D, hD⟩ :=
    exists_native_filling_cylinder_of_nullhomotopic_iterate g hg
      (sphereZero (e.ambientDimension - n)) hreg hd (r + 1) (by omega) D₀
      (map_nullhomotopic hgn)
  refine ⟨C, (iterate_homotopic H (r + 1)).trans HC, hmiss, ?_⟩
  let _ := regularFiberAtlas C.leftMap C.smooth_left
    (equators (e.ambientDimension - n) (r + 1) (sphereZero (e.ambientDimension - n)))
    C.regular_left n (by simp only [finrank_euclideanSpace_fin]; omega)
  exact ⟨D, hD⟩

end Wikipedia.HopfProblem.DegreeCollapse
