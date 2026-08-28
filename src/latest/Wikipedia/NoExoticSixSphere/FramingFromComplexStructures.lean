import Wikipedia.NoExoticSixSphere.OrthogonalPathSpaceVanishing
import Wikipedia.NoExoticSixSphere.SphereSuspensionHomotopy
import Wikipedia.NoExoticSixSphere.OrthogonalStableRange
import Wikipedia.NoExoticSixSphere.FramedEmbeddingReduction

/-!
# The rank-six complex-structure input suffices for actual normal framing

Meridian families and their sphere quotient connect the checked minimum-path
deformation directly to maps from the actual five-sphere. No identification
of cube-based homotopy groups with sphere homotopy classes is used here.

This module keeps rank-six complex-structure nullhomotopy as an explicit input.
`RankSixVanishing.lean` proves it, and `NormalFraming.lean` applies that proof.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere

open GLOrthonormalization

theorem fiveSphereOrthogonalSixteenVanishing_of_complexStructureSix
    (h6 : ∀ J : C(Sphere 4, OrthogonalComplexStructures.Space 6),
      ∃ K, J.Homotopic (ContinuousMap.const _ K)) :
    ∀ f : C(Sphere 5, OrthogonalOperators 16),
      ∃ a, f.Homotopic (ContinuousMap.const _ a) := by
  intro f
  obtain ⟨v⟩ : Nonempty (Sphere 5) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  let e : Equator v ≃ₜ Sphere 4 :=
    equatorEuclideanHomeomorph v (n := 5) finrank_euclideanSpace_fin
  let : Nonempty (Sphere 4) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  let : Nonempty (Equator v) := e.toEquiv.nonempty
  let P : C(Sphere 4, Path (f v) (f (antipode v))) :=
    (SphereSuspension.meridians v f).comp (toContinuousMap e.symm)
  obtain ⟨γ, ⟨H⟩⟩ := OrthogonalPolygon.fourthSphere_pathFamily_sixteen_of_rankSix h6 _ _ P
  have hleft : P.comp (toContinuousMap e) = SphereSuspension.meridians v f := by
    apply ContinuousMap.ext
    intro x
    change SphereSuspension.meridians v f (e.symm (e x)) = SphereSuspension.meridians v f x
    rw [e.symm_apply_apply]
  have hright : (ContinuousMap.const (Sphere 4) γ).comp (toContinuousMap e) =
      ContinuousMap.const (Equator v) γ := rfl
  let G := (H.compContinuousMap (toContinuousMap e)).cast hleft hright
  exact ⟨f v, SphereSuspension.nullhomotopic_of_meridians v f γ G⟩

theorem fiveSphereOrthogonalSevenVanishing_of_complexStructureSix
    (h6 : ∀ J : C(Sphere 4, OrthogonalComplexStructures.Space 6),
      ∃ K, J.Homotopic (ContinuousMap.const _ K)) :
    ∀ f : C(Sphere 5, OrthogonalOperators 7),
      ∃ a, f.Homotopic (ContinuousMap.const _ a) :=
  sphereOrthogonalVanishing_descends (by decide : 5 + 1 < 7) 16 (by decide)
    (fiveSphereOrthogonalSixteenVanishing_of_complexStructureSix h6)

theorem exists_framedEmbedding_of_complexStructureSixVanishing
    (h6 : ∀ J : C(Sphere 4, OrthogonalComplexStructures.Space 6),
      ∃ K, J.Homotopic (ContinuousMap.const _ K))
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
    (h : M ≃ₜ Sphere 6) :
    ∃ e : EuclideanEmbedding 6 M,
      Nonempty (SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) :=
  exists_framedEmbedding_of_rankSevenVanishing
    (fiveSphereOrthogonalSevenVanishing_of_complexStructureSix h6) h

end NoExoticSixSphere
