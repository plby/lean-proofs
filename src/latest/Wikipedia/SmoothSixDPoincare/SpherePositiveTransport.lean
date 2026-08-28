import Wikipedia.HopfProblem.SphereHomologyBasic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Actual determinant-one orthogonal transport between sphere points

A hyperplane reflection moves one unit vector to another. A second
reflection in a hyperplane containing the target fixes that target and
corrects the determinant. The actual orthogonal complement supplies its
nonzero normal in every ambient dimension at least two.
-/

noncomputable section

open Set Metric

namespace Wikipedia.SmoothSixDPoincare.SpherePoint

open Wikipedia.HopfProblem.SphereHomology

section Reflection

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem hyperplaneReflection_det (u : V) (hu : u ≠ 0) :
    ((ℝ ∙ u)ᗮ.reflection).toLinearMap.det = -1 := by
  rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal,
    finrank_span_singleton hu, pow_one]

theorem positive_transport_of_normal (v w : sphere (0 : V) 1)
    (u : V) (hu : u ≠ 0) (huw : inner ℝ u w.val = 0) (hvw : v ≠ w) :
    ∃ R : V ≃ₗᵢ[ℝ] V, R v.val = w.val ∧ R.toLinearMap.det = 1 := by
  have hvw' : (v : V) - (w : V) ≠ 0 := by
    intro h
    exact hvw (Subtype.ext (sub_eq_zero.mp h))
  let R₁ := (ℝ ∙ ((v : V) - (w : V)))ᗮ.reflection
  let R₂ := (ℝ ∙ u)ᗮ.reflection
  have h₁ : R₁ v.val = w.val :=
    Submodule.reflection_sub ((mem_sphere_zero_iff_norm.mp v.property).trans
      (mem_sphere_zero_iff_norm.mp w.property).symm)
  have h₂ : R₂ w.val = w.val :=
    Submodule.reflection_mem_subspace_eq_self
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr huw)
  refine ⟨R₁.trans R₂, ?_, ?_⟩
  · change R₂ (R₁ v.val) = w.val
    rw [h₁, h₂]
  · change (R₂.toLinearMap.comp R₁.toLinearMap).det = 1
    rw [LinearMap.det_comp, hyperplaneReflection_det u hu,
      hyperplaneReflection_det ((v : V) - (w : V)) hvw']
    norm_num

end Reflection

/-- Any two original Euclidean sphere points are related by a determinant-one linear isometry. -/
theorem exists_positive_transport (n : ℕ) (v w : UnitSphere (n + 1)) :
    ∃ R : EuclideanSpace ℝ (Fin (n + 2)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)),
      R v.val = w.val ∧ R.toLinearMap.det = 1 := by
  by_cases hvw : v = w
  · refine ⟨LinearIsometryEquiv.refl ℝ _, ?_, ?_⟩
    · exact congrArg Subtype.val hvw
    · exact LinearMap.det_id
  · let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 2))) = (n + 1) + 1) :=
      ⟨by simp⟩
    let b := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (n + 1)
      (ne_zero_of_mem_unit_sphere w)
    let u : EuclideanSpace ℝ (Fin (n + 2)) :=
      (b (0 : Fin (n + 1)) : EuclideanSpace ℝ (Fin (n + 2)))
    have hun : ‖u‖ = 1 := b.norm_eq_one 0
    have hu : u ≠ 0 := by
      intro h
      rw [h, norm_zero] at hun
      exact zero_ne_one hun
    have huw : inner ℝ u w.val = 0 := by
      have h := (b (0 : Fin (n + 1))).property
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp h
    exact positive_transport_of_normal v w u hu huw hvw

def positiveTransport (n : ℕ) (v w : UnitSphere (n + 1)) :
    EuclideanSpace ℝ (Fin (n + 2)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)) :=
  Classical.choose (exists_positive_transport n v w)

theorem positiveTransport_apply (n : ℕ) (v w : UnitSphere (n + 1)) :
    positiveTransport n v w v.val = w.val :=
  (Classical.choose_spec (exists_positive_transport n v w)).1

theorem positiveTransport_det (n : ℕ) (v w : UnitSphere (n + 1)) :
    (positiveTransport n v w).toLinearMap.det = 1 :=
  (Classical.choose_spec (exists_positive_transport n v w)).2

end Wikipedia.SmoothSixDPoincare.SpherePoint
