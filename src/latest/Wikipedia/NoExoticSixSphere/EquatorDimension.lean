import Wikipedia.NoExoticSixSphere.Equator
import Wikipedia.NoExoticSixSphere.Definitions

/-!
# Dimension of the equatorial sphere

The orthogonal hyperplane has codimension one. An orthonormal basis identifies
its unit sphere with the standard Euclidean sphere, so the clutching domain for
a six-sphere is genuinely the standard five-sphere.
-/

open Module

namespace NoExoticSixSphere

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A linear isometry equivalence restricts to a homeomorphism of actual unit spheres. -/
noncomputable def unitSphereCongr (e : E ≃ₗᵢ[ℝ] F) : UnitSphere E ≃ₜ UnitSphere F :=
  e.toHomeomorph.subtype (by
    intro x
    simp only [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.coe_toHomeomorph,
      e.norm_map])

/-- The kernel definition of the equatorial hyperplane equals the orthogonal complement. -/
theorem equatorialSpace_eq_orthogonal (v : UnitSphere E) :
    equatorialSpace v = (ℝ ∙ (v : E))ᗮ := by
  ext x
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.symm

/-- The hyperplane perpendicular to a unit vector has codimension one. -/
theorem finrank_equatorialSpace [FiniteDimensional ℝ E] (v : UnitSphere E) {n : ℕ}
    (hn : finrank ℝ E = n + 1) : finrank ℝ (equatorialSpace v) = n := by
  let : Fact (finrank ℝ E = n + 1) := ⟨hn⟩
  rw [equatorialSpace_eq_orthogonal]
  apply Submodule.finrank_orthogonal_span_singleton
  exact norm_ne_zero_iff.mp (by rw [ClosedHemisphere.unit_norm]; exact one_ne_zero)

/-- An orthonormal coordinate system for the actual equatorial hyperplane. -/
noncomputable def equatorialCoordinates [FiniteDimensional ℝ E] (v : UnitSphere E) {n : ℕ}
    (hn : finrank ℝ E = n + 1) : equatorialSpace v ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  ((stdOrthonormalBasis ℝ (equatorialSpace v)).reindex
    (finCongr (finrank_equatorialSpace v hn))).repr

/-- The actual equator is homeomorphic to the standard sphere of the correct dimension. -/
noncomputable def equatorEuclideanHomeomorph [FiniteDimensional ℝ E]
    (v : UnitSphere E) {n : ℕ} (hn : finrank ℝ E = n + 1) :
    Equator v ≃ₜ UnitSphere (EuclideanSpace ℝ (Fin n)) :=
  (equatorHomeomorph v).trans (unitSphereCongr (equatorialCoordinates v hn))

/-- The equator of the standard six-sphere is the standard five-sphere up to homeomorphism. -/
noncomputable def equatorSixHomeomorph (v : Sphere 6) : Equator v ≃ₜ Sphere 5 :=
  equatorEuclideanHomeomorph v (n := 6) finrank_euclideanSpace_fin

/-- The equator of a six-sphere is nonempty. -/
theorem nonempty_equatorSix (v : Sphere 6) : Nonempty (Equator v) := by
  let : Nonempty (Sphere 5) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  exact (equatorSixHomeomorph v).toEquiv.nonempty

end NoExoticSixSphere
