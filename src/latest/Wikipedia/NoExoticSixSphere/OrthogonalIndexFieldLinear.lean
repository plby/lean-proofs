import Wikipedia.NoExoticSixSphere.OrthogonalIndexTestField

/-!
# The test-field construction is a linear embedding

The rotating sine field depends linearly on its initial skew operator.
At the interval midpoint it preserves the Hilbert--Schmidt norm, so no
linear independence is lost when operators are realized as variation fields.
-/

namespace NoExoticSixSphere.OrthogonalIndexTestField

open GLOrthonormalization CayleyTransform OrthogonalIndexTransport
  OrthogonalExponential SkewConjugation HilbertSchmidt

variable {n : ℕ}

noncomputable def conjugateLinear (a : OrthogonalOperators n) :
    SkewOperators n →ₗ[ℝ] SkewOperators n where
  toFun := conjugate a
  map_add' A B := by
    apply Subtype.ext
    change a.1.1.comp (((A : Vector n →L[ℝ] Vector n) + B).comp
      (OrthogonalPaths.inverse a).1.1) = _
    simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
    rfl
  map_smul' r A := by
    apply Subtype.ext
    change a.1.1.comp ((r • (A : Vector n →L[ℝ] Vector n)).comp
      (OrthogonalPaths.inverse a).1.1) = _
    simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    rfl

noncomputable def fieldLinear (K : SkewOperators n) :
    SkewOperators n →ₗ[ℝ] (ℝ → SkewOperators n) :=
  LinearMap.pi (fun t ↦ Real.sin (Real.pi * t) •
    conjugateLinear (exp (t • ((-1 / 2 : ℝ) • K))))

theorem fieldLinear_apply (K A : SkewOperators n) : fieldLinear K A = field K A := rfl

theorem squareNorm_field_midpoint (K A : SkewOperators n) :
    squareNorm (field K A (1 / 2) : Vector n →L[ℝ] Vector n) =
      squareNorm (A : Vector n →L[ℝ] Vector n) := by
  rw [field, Submodule.coe_smul, squareNorm_smul, squareNorm_transport]
  rw [show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  ring

theorem fieldLinear_injective (K : SkewOperators n) : Function.Injective (fieldLinear K) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro A h
  have hm : field K A (1 / 2) = 0 := congrFun h (1 / 2)
  have hz : squareNorm (A : Vector n →L[ℝ] Vector n) = 0 := by
    rw [← squareNorm_field_midpoint K A, hm]
    exact (squareNorm_eq_zero_iff _).mpr rfl
  exact Subtype.ext ((squareNorm_eq_zero_iff _).mp hz)

end NoExoticSixSphere.OrthogonalIndexTestField
