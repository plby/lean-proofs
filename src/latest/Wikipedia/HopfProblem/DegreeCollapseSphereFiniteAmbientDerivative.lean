import Wikipedia.HopfProblem.DegreeCollapseSphereFiniteAmbientPoint

/-!
# The actual inverse sphere chart has exactly the ambient tangent image

Differentiate the original inverse chart through the native sphere inclusion.
Its derivative is injective. Differentiating its constant squared norm shows
that its range is the orthogonal complement of its actual unit-sphere value.
-/

noncomputable section

open Function
open scoped Manifold ContDiff RealInnerProductSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereFiniteAmbientDerivative

open NoExoticSixSphere SphereCenteredAmbientChart SphereFiniteAmbientPoint

local instance (n : ℕ) : Fact (Module.finrank ℝ (V (n + 1)) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem derivative_native (n : ℕ) (u : V n) :
    fderiv ℝ (ambientPoint n) u =
      (mfderiv (𝓡 n) 𝓘(ℝ, V (n + 1)) (Subtype.val : Sphere n → V (n + 1))
        (SphereFiniteRepresentative.point n u)).comp
          (mfderiv (𝓡 n) (𝓡 n) (SphereFiniteRepresentative.point n) u) := by
  have hc := mfderiv_comp u
    ((contMDiff_coe_sphere (n := n) (m := ∞)).mdifferentiable (by simp)
      (SphereFiniteRepresentative.point n u))
    ((SphereFiniteRepresentative.point_contMDiff n).mdifferentiable (by simp) u)
  rw [mfderiv_eq_fderiv] at hc
  exact hc

theorem derivative_injective (n : ℕ) (u : V n) :
    Injective (fderiv ℝ (ambientPoint n) u) := by
  rw [derivative_native]
  have hi : Injective (mfderiv (𝓡 n) 𝓘(ℝ, V (n + 1))
      (Subtype.val : Sphere n → V (n + 1)) (SphereFiniteRepresentative.point n u)) := by
    intro v w h
    exact injective_mvfderiv_subtypeVal_sphere (n := n)
      (SphereFiniteRepresentative.point n u) h
  exact hi.comp (SphereFiniteRepresentative.point_mfderiv_bijective n u).injective

theorem derivative_tangent (n : ℕ) (u v : V n) :
    inner ℝ (ambientPoint n u) (fderiv ℝ (ambientPoint n) u v) = 0 := by
  have hd := ((contDiff_ambientPoint n).differentiable (by simp) u).hasFDerivAt.norm_sq
  have he : (fun z : V n ↦ ‖ambientPoint n z‖ ^ 2) = fun _ ↦ (1 : ℝ) := by
    funext z
    rw [ambientPoint_norm, one_pow]
  rw [he] at hd
  have h := congrArg (fun L : V n →L[ℝ] ℝ ↦ L v)
    (hd.unique (hasFDerivAt_const (1 : ℝ) u))
  change (2 : ℕ) • inner ℝ (ambientPoint n u) (fderiv ℝ (ambientPoint n) u v) = 0 at h
  rw [two_smul] at h
  linarith

theorem derivative_range (n : ℕ) (u : V n) :
    (fderiv ℝ (ambientPoint n) u).range = (ℝ ∙ ambientPoint n u)ᗮ := by
  have hle : (fderiv ℝ (ambientPoint n) u).range ≤ (ℝ ∙ ambientPoint n u)ᗮ := by
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (derivative_tangent n u v)
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.finrank_range_of_inj (derivative_injective n u), finrank_euclideanSpace_fin]
  exact (Submodule.finrank_orthogonal_span_singleton
    (ne_zero_of_mem_unit_sphere (SphereFiniteRepresentative.point n u))).symm

end Wikipedia.HopfProblem.DegreeCollapse.SphereFiniteAmbientDerivative
