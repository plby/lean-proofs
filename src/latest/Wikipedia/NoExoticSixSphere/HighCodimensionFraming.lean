import Wikipedia.NoExoticSixSphere.NormalFraming
import Wikipedia.NoExoticSixSphere.SphereCollapseRegularValue

/-!
# Framed collapse maps in arbitrarily high codimension

The normal-framing argument works for every embedding of a candidate
six-sphere whose codimension is at least seven. We therefore retain any
requested codimension lower bound when constructing a framed embedding and
its smooth regular collapse.

This supplies room for the later stable homotopy computation. It does not
prove a suspension theorem or nullhomotopy of the collapse map.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]

theorem nonempty_smoothNormalFrame_of_codimension_ge_seven
    (h : M ≃ₜ Sphere 6) (e : EuclideanEmbedding 6 M) (he : 7 ≤ e.ambientDimension - 6) :
    Nonempty (SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) := by
  let v : Sphere 6 := sphereZero 6
  have hO := sphereOrthogonalVanishing_of_rank
    (by decide : 5 < 7) fiveSphereOrthogonalSevenVanishing (e.ambientDimension - 6) he
  obtain ⟨c, ⟨H⟩⟩ := GLOrthonormalization.nullhomotopic_of_orthogonal_nullhomotopic
    (e.ambientDimension - 6) hO (e.normalSixClutchingMap h v)
  exact e.nonempty_smoothNormalFrame_of_clutchingNullhomotopy h v c H

theorem exists_highCodimensionFramedEmbedding (h : M ≃ₜ Sphere 6) (r : ℕ) :
    ∃ e : EuclideanEmbedding 6 M, r ≤ e.ambientDimension - 6 ∧
      Nonempty (SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) := by
  obtain ⟨e, he⟩ := exists_highCodimensionEmbedding h (max r 7)
  exact ⟨e, (le_max_left r 7).trans he,
    nonempty_smoothNormalFrame_of_codimension_ge_seven h e ((le_max_right r 7).trans he)⟩

theorem exists_highCodimensionSixSphereRegularCollapse (h : M ≃ₜ Sphere 6) (r : ℕ) :
    ∃ e : EuclideanEmbedding 6 M, r ≤ e.ambientDimension - 6 ∧
      ∃ g : C(Sphere e.ambientDimension, Sphere (e.ambientDimension - 6)),
        ContMDiff (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - 6)) ∞ g ∧
        (∀ y, g y = sphereZero (e.ambientDimension - 6) ↔
          ∃ x, e.compactifiedEmbedding x = y) ∧
        ∀ y, g y = sphereZero (e.ambientDimension - 6) →
          Function.Surjective
            (mfderiv (𝓡 e.ambientDimension) (𝓡 (e.ambientDimension - 6)) g y) := by
  let : CompactSpace M := compactSpace_of_homeomorph h
  let : Nonempty M := ⟨h.symm (sphereZero 6)⟩
  obtain ⟨e, he, ⟨a⟩⟩ := exists_highCodimensionFramedEmbedding h r
  let d := e.framedCollapseData a
  obtain ⟨g, hg, _, hfiber, hregular, _⟩ := d.exists_smoothSphereMap_regular
  exact ⟨e, he, g, hg, hfiber, hregular⟩

end NoExoticSixSphere
