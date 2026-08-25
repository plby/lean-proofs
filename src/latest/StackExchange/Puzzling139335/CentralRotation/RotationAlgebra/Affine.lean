import StackExchange.Puzzling139335.PlaneIsometries.Chasles

/-! # Affine identities for the central rotation argument -/

namespace Puzzling139335.CentralRotation.RotationAlgebra

open PlaneIsometries

/-- Point reflection has its usual complex-coordinate formula. -/
theorem complex_pointReflection (c x : Plane) :
    complexEquiv (AffineIsometryEquiv.pointReflection ℝ c x) =
      2 * complexEquiv c - complexEquiv x := by
  rw [AffineIsometryEquiv.pointReflection_apply, vsub_eq_sub, vadd_eq_add,
    map_add, map_sub]
  ring

/-- Affine isometries transport point reflections and their centers. -/
theorem affine_map_pointReflection (e : Plane ≃ᵃⁱ[ℝ] Plane) (c x : Plane) :
    e (AffineIsometryEquiv.pointReflection ℝ c x) =
      AffineIsometryEquiv.pointReflection ℝ (e c) (e x) := by
  rw [AffineIsometryEquiv.pointReflection_apply, e.map_vadd, e.map_vsub,
    AffineIsometryEquiv.pointReflection_apply]

/-- Conjugating a half-turn pulls its center back by the conjugating map. -/
theorem conjugate_pointReflection (e : Plane ≃ᵃⁱ[ℝ] Plane) (c x : Plane) :
    e.symm (AffineIsometryEquiv.pointReflection ℝ c (e x)) =
      AffineIsometryEquiv.pointReflection ℝ (e.symm c) x := by
  rw [affine_map_pointReflection, e.symm_apply_apply]

/-- If `F = h ∘ g⁻¹`, then `g⁻¹ = h ∘ F`, since `h` is a half-turn. -/
theorem inverse_eq_reflection_comp (F g : Plane ≃ᵃⁱ[ℝ] Plane) (O : Plane)
    (hF : ∀ x, F x = AffineIsometryEquiv.pointReflection ℝ O (g.symm x))
    (x : Plane) :
    g.symm x = AffineIsometryEquiv.pointReflection ℝ O (F x) := by
  rw [hF]
  exact (AffineIsometryEquiv.pointReflection_involutive (𝕜 := ℝ) O (g.symm x)).symm

/-- The preimage of the original center under `F = h ∘ g⁻¹` is `g O`. -/
theorem inverse_center (F g : Plane ≃ᵃⁱ[ℝ] Plane) (O : Plane)
    (hF : ∀ x, F x = AffineIsometryEquiv.pointReflection ℝ O (g.symm x)) :
    F.symm O = g O := by
  apply F.injective
  rw [F.apply_symm_apply, hF, g.symm_apply_apply,
    AffineIsometryEquiv.pointReflection_self]

/-- A period of `m+1` identifies the `m`th iterate with the inverse map. -/
theorem iterate_eq_symm_of_succ_eq_id (F : Plane ≃ᵃⁱ[ℝ] Plane) {m : ℕ}
    (hperiod : (F : Plane → Plane)^[m + 1] = id) :
    (F : Plane → Plane)^[m] = F.symm := by
  funext x
  apply F.injective
  calc
    F (((F : Plane → Plane)^[m]) x) = ((F : Plane → Plane)^[m + 1]) x :=
      (Function.iterate_succ_apply' (F : Plane → Plane) m x).symm
    _ = x := congrFun hperiod x
    _ = F (F.symm x) := (F.apply_symm_apply x).symm

/-- Under the finite-period identity, the isometry of the first overlap is
the conjugated half-turn `F⁻¹ ∘ h ∘ F`. -/
theorem iterate_comp_inverse_eq_conjugate (F g : Plane ≃ᵃⁱ[ℝ] Plane)
    (O : Plane) {m : ℕ}
    (hF : ∀ x, F x = AffineIsometryEquiv.pointReflection ℝ O (g.symm x))
    (hperiod : (F : Plane → Plane)^[m + 1] = id) (x : Plane) :
    ((F : Plane → Plane)^[m]) (g.symm x) =
      F.symm (AffineIsometryEquiv.pointReflection ℝ O (F x)) := by
  rw [iterate_eq_symm_of_succ_eq_id F hperiod, inverse_eq_reflection_comp F g O hF]

/-- The same conjugated half-turn is centered at `g O`. -/
theorem iterate_comp_inverse_eq_pointReflection (F g : Plane ≃ᵃⁱ[ℝ] Plane)
    (O : Plane) {m : ℕ}
    (hF : ∀ x, F x = AffineIsometryEquiv.pointReflection ℝ O (g.symm x))
    (hperiod : (F : Plane → Plane)^[m + 1] = id) (x : Plane) :
    ((F : Plane → Plane)^[m]) (g.symm x) =
      AffineIsometryEquiv.pointReflection ℝ (g O) x := by
  rw [iterate_comp_inverse_eq_conjugate F g O hF hperiod,
    conjugate_pointReflection, inverse_center F g O hF]

end Puzzling139335.CentralRotation.RotationAlgebra
