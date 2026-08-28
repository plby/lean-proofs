import Wikipedia.NoExoticSixSphere.Classification
import Wikipedia.SmoothSixDPoincare.BoundarylessModelChange

/-!
# Six-sphere rigidity for arbitrary real six-dimensional coordinate models

Changing the coordinate model preserves the original smooth structure through
an identity-on-points diffeomorphism. The sphere retains its standard atlas.
-/

open scoped ContDiff Manifold

namespace NoExoticSixSphere

/-- A homeomorphism to the six-sphere upgrades to a diffeomorphism for the
original atlas, regardless of the chosen six-dimensional real coordinate model. -/
theorem diffeomorphic_of_homeomorphic
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type*) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (hdim : Module.finrank ℝ E = 6) (h : M ≃ₜ Sphere 6) :
    Nonempty (M ≃ₘ⟮𝓘(ℝ, E), 𝓡 6⟯ Sphere 6) := by
  obtain ⟨e⟩ : Nonempty (E ≃L[ℝ] EuclideanSpace ℝ (Fin 6)) :=
    FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by simpa using hdim)
  let Φ : PartialDiffeomorph 𝓘(ℝ, E) (𝓡 6) E (EuclideanSpace ℝ (Fin 6)) ∞ :=
    { e.toHomeomorph.toOpenPartialHomeomorph with
      contMDiffOn_toFun := e.toDiffeomorph.contMDiff.contMDiffOn
      contMDiffOn_invFun := e.symm.toDiffeomorph.contMDiff.contMDiffOn }
  let := Wikipedia.SmoothSixDPoincare.BoundarylessModelChange.chartedSpace
    (I := 𝓘(ℝ, E)) (M := M) Φ rfl
  let := Wikipedia.SmoothSixDPoincare.BoundarylessModelChange.isManifold
    (I := 𝓘(ℝ, E)) (M := M) Φ rfl
  let D := Wikipedia.SmoothSixDPoincare.BoundarylessModelChange.diffeomorph
    (I := 𝓘(ℝ, E)) (M := M) Φ rfl
  obtain ⟨d⟩ := noExoticSixSpheres M inferInstance inferInstance inferInstance ⟨h⟩
  exact ⟨D.symm.trans d⟩

end NoExoticSixSphere
