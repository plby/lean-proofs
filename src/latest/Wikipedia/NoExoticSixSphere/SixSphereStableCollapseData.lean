import Wikipedia.NoExoticSixSphere.StableClassOriginalAtlasFilling
import Wikipedia.NoExoticSixSphere.NormalFraming

/-!
# Candidate six-spheres supply actual stable collapse data

The original normal-framing argument works at any prescribed sufficiently
large codimension. Retaining the dimension bound places the resulting
actual collapse in the constructed sixth-stem system. The existence of
these data is unconditional; vanishing of their stable class is not claimed.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]

theorem EuclideanEmbedding.nonempty_normalFrame_of_homeomorph_sixSphere
    (e : EuclideanEmbedding 6 M) (h : M ≃ₜ Sphere 6) (he : 7 ≤ e.ambientDimension - 6) :
    Nonempty (SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) := by
  have hO := sphereOrthogonalVanishing_of_rank (by decide : 5 < 7)
    fiveSphereOrthogonalSevenVanishing (e.ambientDimension - 6) he
  obtain ⟨c, ⟨H⟩⟩ := GLOrthonormalization.nullhomotopic_of_orthogonal_nullhomotopic
    (e.ambientDimension - 6) hO (e.normalSixClutchingMap h (spherePole 6))
  exact e.nonempty_smoothNormalFrame_of_clutchingNullhomotopy h (spherePole 6) c H

theorem exists_highCodimensionFramedEmbedding (h : M ≃ₜ Sphere 6) (c : ℕ) :
    ∃ e : EuclideanEmbedding 6 M, c ≤ e.ambientDimension - 6 ∧
      Nonempty (SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) := by
  obtain ⟨e, he⟩ := exists_highCodimensionEmbedding h (max 7 c)
  exact ⟨e, (Nat.le_max_right 7 c).trans he,
    e.nonempty_normalFrame_of_homeomorph_sixSphere h ((Nat.le_max_left 7 c).trans he)⟩

theorem exists_sixSphereStableCollapseData (h : M ≃ₜ Sphere 6) :
    ∃ e : EuclideanEmbedding 6 M, ∃ hd : 8 ≤ e.ambientDimension,
      ∃ a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel,
        ∃ d : e.FramedCollapseData a,
          (d.sixthStableClass hd = StableSixSphereMaps.nullClass ↔
            ∃ r : ℕ, (SphereMapSuspension.iterate d.sphereMap r).Nullhomotopic) := by
  let : CompactSpace M := compactSpace_of_homeomorph h
  let : Nonempty M := h.toEquiv.nonempty
  obtain ⟨e, he, ⟨a⟩⟩ := exists_highCodimensionFramedEmbedding h 7
  have hd : 8 ≤ e.ambientDimension := by omega
  let d := e.framedCollapseData a
  exact ⟨e, hd, a, d, d.sixthStableClass_eq_null_iff hd⟩

end NoExoticSixSphere
