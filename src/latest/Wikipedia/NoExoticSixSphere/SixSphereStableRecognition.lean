import Wikipedia.NoExoticSixSphere.FramedCollapseRecognition
import Wikipedia.NoExoticSixSphere.StableSixFiniteDetection

/-!
# The remaining collapse-vanishing input implies actual six-sphere rigidity

The constructed candidate collapse is the actual map from S13 to S7.
Its stable identity criterion supplies a finite ordinary nullhomotopy,
and the original-atlas framed filling recognition supplies a diffeomorphism.
Equivalently, nullity of the first ordinary suspension suffices.

These are reductions, not proofs of the remaining vanishing statement.
No injectivity of stabilization at the S7 stage and no nullity of the
unsuspended collapse is assumed.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.SixSphereThirteen

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M] [IsManifold (𝓡 6) ∞ M]
  (h : M ≃ₜ Sphere 6)

theorem nonempty_diffeomorph_of_stableClass_eq_one (hz : stableClass h = 1) :
    Nonempty (M ≃ₘ⟮𝓡 6, 𝓡 6⟯ Sphere 6) := by
  obtain ⟨r, hr⟩ := (stableClass_eq_one_iff h).mp hz
  exact (collapseData h).nonempty_sphere_diffeomorph_of_iterate_nullhomotopic h r hr

theorem nonempty_diffeomorph_of_suspension_nullhomotopic
    (hnull : (SphereMapSuspension.map (sphereMap h)).Nullhomotopic) :
    Nonempty (M ≃ₘ⟮𝓡 6, 𝓡 6⟯ Sphere 6) :=
  nonempty_diffeomorph_of_stableClass_eq_one h
    ((stableClass_eq_one_iff_suspension_nullhomotopic h).mpr hnull)

end NoExoticSixSphere.SixSphereThirteen

namespace NoExoticSixSphere

universe u

theorem sixSphereRigidity_of_collapse_suspension_nullhomotopic
    (hnull : ∀ (M : Type u) (_ : TopologicalSpace M)
      (_ : ChartedSpace (EuclideanSpace ℝ (Fin 6)) M) (_ : IsManifold (𝓡 6) ∞ M)
      (h : M ≃ₜ Sphere 6),
        (SphereMapSuspension.map (SixSphereThirteen.sphereMap h)).Nullhomotopic) :
    SixSphereRigidity.{u} := by
  intro M t c s ⟨h⟩
  exact SixSphereThirteen.nonempty_diffeomorph_of_suspension_nullhomotopic h (hnull M t c s h)

end NoExoticSixSphere
