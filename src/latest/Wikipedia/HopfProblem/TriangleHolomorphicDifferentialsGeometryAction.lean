import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsGeometry
import Wikipedia.HopfProblem.SpecialPeriodsTriangleActions

/-!
# Derivatives of the actual triangle action

The derivative is taken from the constructed holomorphic action on the
upper half-plane.  The chain rule proves its multiplicative cocycle law;
differentiating the inverse action proves nonvanishing and the inverse
formula.  No automorphy factor is supplied as independent data.
-/

noncomputable section

open UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

open SpecialPeriods

/-- The scalar derivative of the actual triangle-group action. -/
def actionDerivative (g : TriangleGroup) (z : ℍ) : ℂ :=
  scalarDeriv (fun w : ℍ => (triangleGeometricRepresentation g w : ℂ)) z

theorem actionHasDerivAt (g : TriangleGroup) (z : ℍ) :
    HasDerivAt (fun w : ℂ =>
      (triangleGeometricRepresentation g (UpperHalfPlane.ofComplex w) : ℂ))
      (actionDerivative g z) (z : ℂ) :=
  scalarHasDerivAt
    (UpperHalfPlane.contMDiff_coe.comp (triangleGeometricRepresentation_holomorphic g)) z

/-- The actual action derivative is holomorphic everywhere on the upper half-plane. -/
theorem actionDerivative_holomorphic (g : TriangleGroup) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (actionDerivative g) :=
  scalarDeriv_holomorphic
    (UpperHalfPlane.contMDiff_coe.comp (triangleGeometricRepresentation_holomorphic g))

/-- Pullback of a scalar function uses the derivative of the actual action. -/
theorem scalarDeriv_comp_action {f : ℍ → ℂ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (g : TriangleGroup) (z : ℍ) :
    scalarDeriv (f ∘ triangleGeometricRepresentation g) z =
      scalarDeriv f (triangleGeometricRepresentation g z) * actionDerivative g z :=
  scalarDeriv_comp hf (triangleGeometricRepresentation_holomorphic g) z

@[simp] theorem actionDerivative_one (z : ℍ) : actionDerivative 1 z = 1 := by
  simpa only [actionDerivative, map_one, Equiv.Perm.one_apply] using scalarDeriv_coe z

/-- The cocycle law is the scalar chain rule for the actual group action. -/
theorem actionDerivative_mul (g h : TriangleGroup) (z : ℍ) :
    actionDerivative (g * h) z =
      actionDerivative g (triangleGeometricRepresentation h z) * actionDerivative h z := by
  simpa only [actionDerivative, map_mul, Equiv.Perm.mul_apply, Function.comp_def] using
    scalarDeriv_comp
      (UpperHalfPlane.contMDiff_coe.comp (triangleGeometricRepresentation_holomorphic g))
      (triangleGeometricRepresentation_holomorphic h) z

/-- The derivative cannot vanish because the inverse action differentiates to one. -/
theorem actionDerivative_ne_zero (g : TriangleGroup) (z : ℍ) :
    actionDerivative g z ≠ 0 := by
  have hi := actionDerivative_mul g⁻¹ g z
  rw [inv_mul_cancel, actionDerivative_one] at hi
  intro hz
  rw [hz, mul_zero] at hi
  exact one_ne_zero hi

@[simp] theorem actionDerivative_inv_apply (g : TriangleGroup) (z : ℍ) :
    actionDerivative g⁻¹ (triangleGeometricRepresentation g z) =
      (actionDerivative g z)⁻¹ := by
  have hi : actionDerivative g⁻¹ (triangleGeometricRepresentation g z) *
      actionDerivative g z = 1 := by
    simpa only [inv_mul_cancel, actionDerivative_one] using
      (actionDerivative_mul g⁻¹ g z).symm
  calc
    actionDerivative g⁻¹ (triangleGeometricRepresentation g z) =
        (actionDerivative g⁻¹ (triangleGeometricRepresentation g z) *
          actionDerivative g z) * (actionDerivative g z)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ (actionDerivative_ne_zero g z), mul_one]
    _ = (actionDerivative g z)⁻¹ := by rw [hi, one_mul]

/-- The inverse derivative at an arbitrary point uses its actual inverse image. -/
theorem actionDerivative_inv (g : TriangleGroup) (z : ℍ) :
    actionDerivative g⁻¹ z =
      (actionDerivative g (triangleGeometricRepresentation g⁻¹ z))⁻¹ := by
  have he : triangleGeometricRepresentation g (triangleGeometricRepresentation g⁻¹ z) = z := by
    rw [map_inv]
    exact (triangleGeometricRepresentation g).apply_symm_apply z
  simpa only [he] using
    actionDerivative_inv_apply g (triangleGeometricRepresentation g⁻¹ z)

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
