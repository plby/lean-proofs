import Wikipedia.NoExoticSixSphere.ManifoldParityBallOperatorExtension
import Wikipedia.NoExoticSixSphere.ManifoldFamilyFrameBoundary
import Wikipedia.NoExoticSixSphere.PartialFrameDimensionCoordinates

/-!
# Every local linking value of the constructed global frame is one

The actual normalization agrees on the original linking spheres. Together
with identity-block stability and the disk-extending chart coordinates,
this discharges the local hypotheses in the global boundary relation.
The geometric normal-disk endpoint comparison is a separate remaining step.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel DiskBoundary

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (g : ℝ → Sphere 3 → M)
  (hg : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))
  (P : SphereFamily.ParityBallSystem g)

theorem puncturedFamilyFrameMap_link (q : SphereFamily.singularParameters (n := 6) g) :
    (e.puncturedFamilyFrameMap a g hg P).comp (P.sphereInclusion (.inr q)) =
      (Monomorphism.normalize e.ambientDimension ((e.ambientDimension - 6) + 3)).comp
        ((P.ball q).globalOperatorLink hg e a) := by
  apply ContinuousMap.ext
  intro s
  rfl

theorem puncturedGlobalFrameMap_extends_iff (f : C(Sphere 3, P.puncturedCylinder)) :
    Extends ((e.puncturedGlobalFrameMap a g hg P).comp f) ↔
      Extends ((e.puncturedFamilyFrameMap a g hg P).comp f) := by
  unfold puncturedGlobalFrameMap
  exact extends_dimensionHomeomorph_iff _ _ ((e.puncturedFamilyFrameMap a g hg P).comp f)

theorem familyBoundaryObstruction_link (q : SphereFamily.singularParameters (n := 6) g) :
    e.familyBoundaryObstruction a g hg P (.inr q) = 1 := by
  have hne : e.familyBoundaryObstruction a g hg P (.inr q) ≠ 0 := by
    intro hz
    have he := (sphereThirdObstruction_zero_iff_extension _ _).mp hz
    have hf := (e.puncturedGlobalFrameMap_extends_iff a g hg P
      (P.sphereInclusion (.inr q))).mp he
    rw [e.puncturedFamilyFrameMap_link a g hg P q] at hf
    exact (P.ball q).normalized_globalOperatorLink_not_extends hg e a hf
  exact zmodTwo_eq_of_zero_iff _ _ (by simp [hne])

theorem endpoint_familyBoundaryObstruction_eq
    (heven : Even (Nat.card (SphereFamily.singularParameters (n := 6) g))) :
    e.familyBoundaryObstruction a g hg P (.inl false) =
      e.familyBoundaryObstruction a g hg P (.inl true) :=
  e.endpoint_familyBoundaryObstruction_eq_of_even_links a g hg P heven
    (e.familyBoundaryObstruction_link a g hg P)

end NoExoticSixSphere.EuclideanEmbedding
