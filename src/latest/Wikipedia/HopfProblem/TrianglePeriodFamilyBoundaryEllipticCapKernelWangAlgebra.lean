import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Recovering a linear map from genuine finite-cover columns

The first covering column is primitive and the second retains its actual
integral shear.  Multiplying by the covering index determines the map on
every class, without choosing or replacing a splitting.
-/

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

variable {A B : Type*} [AddCommGroup A] [Module ℤ A]
  [AddCommGroup B] [Module ℤ B]

/-- The literal two-column covering identity in any integral module. -/
theorem cover_columns_smul (e : A ≃ₗ[ℤ] (Fin 2 → ℤ))
    (u v a : A) (c d : ℤ) (hu : e u = ![1, 0]) (hv : e v = ![c, d]) :
    d • a = (d * e a 0 - c * e a 1) • u + e a 1 • v := by
  apply e.injective
  rw [map_add, map_zsmul, map_zsmul, map_zsmul, hu, hv]
  ext i
  fin_cases i
  · change d * e a 0 = (d * e a 0 - c * e a 1) * 1 + e a 1 * c
    ring
  · change d * e a 1 = (d * e a 0 - c * e a 1) * 0 + e a 1 * d
    ring

/-- Applying any actual linear map keeps the genuine covering shear. -/
theorem map_cover_columns (e : A ≃ₗ[ℤ] (Fin 2 → ℤ)) (L : A →ₗ[ℤ] B)
    (u v a : A) (c d : ℤ) (hu : e u = ![1, 0]) (hv : e v = ![c, d]) :
    d • L a = (d * e a 0 - c * e a 1) • L u + e a 1 • L v := by
  simpa only [map_add, map_zsmul] using congrArg L (cover_columns_smul e u v a c d hu hv)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
