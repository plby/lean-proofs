import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.Dynamics.Center

/-! # Powers and invariant sets of actual rotations -/

open Set

namespace Puzzling139335.N4MiddleInvolutions.Reflection.Dynamics

noncomputable section

open PlaneIsometries

/-- A complex rotation formula iterates to the corresponding coefficient power. -/
theorem rotation_pow_complex_action (g : Plane ≃ᵃⁱ[ℝ] Plane) (C : Plane) (a : ℂ)
    (hrot : ∀ p, complexEquiv (g p) =
      complexEquiv C + a * (complexEquiv p - complexEquiv C)) (n : ℕ) (p : Plane) :
    complexEquiv ((g ^ n) p) =
      complexEquiv C + a ^ n * (complexEquiv p - complexEquiv C) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', AffineIsometryEquiv.coe_mul, Function.comp_apply, hrot, ih, pow_succ]
      ring

/-- Coefficient one gives the identity actual affine isometry. -/
theorem pow_eq_one_of_complex_pow_eq_one
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (C : Plane) (a : ℂ)
    (hrot : ∀ p, complexEquiv (g p) =
      complexEquiv C + a * (complexEquiv p - complexEquiv C))
    {n : ℕ} (hn : a ^ n = 1) : g ^ n = 1 := by
  apply AffineIsometryEquiv.ext
  intro p
  apply complexEquiv.injective
  rw [rotation_pow_complex_action g C a hrot, hn]
  simp

/-- Coefficient minus one gives reflection through the actual rotation center. -/
theorem pow_eq_pointReflection_of_complex_pow_eq_neg_one
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (C : Plane) (a : ℂ)
    (hrot : ∀ p, complexEquiv (g p) =
      complexEquiv C + a * (complexEquiv p - complexEquiv C))
    {n : ℕ} (hn : a ^ n = -1) :
    g ^ n = AffineIsometryEquiv.pointReflection ℝ C := by
  apply AffineIsometryEquiv.ext
  intro p
  apply complexEquiv.injective
  rw [rotation_pow_complex_action g C a hrot, hn, AffineIsometryEquiv.pointReflection_apply]
  change complexEquiv C + -1 * (complexEquiv p - complexEquiv C) =
    complexEquiv (C - p + C)
  rw [map_add, map_sub]
  ring

/-- Invariance under an actual affine isometry is preserved by every natural power. -/
theorem pow_image_eq_of_image_eq (g : Plane ≃ᵃⁱ[ℝ] Plane) {K : Set Plane}
    (hK : g '' K = K) (n : ℕ) : (g ^ n) '' K = K := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (g ^ (n + 1)) '' K = g '' ((g ^ n) '' K) := by
          rw [pow_succ']
          exact (image_image (g : Plane → Plane)
            (g ^ n : Plane ≃ᵃⁱ[ℝ] Plane) K).symm
        _ = K := by rw [ih, hK]

/-- Invariance under both reflections gives invariance under every power of their composition. -/
theorem composition_pow_image_eq (e : Plane ≃ᵃⁱ[ℝ] Plane) {K : Set Plane}
    (heK : e '' K = K) (hHK : ReflectionSeparation.horizontal '' K = K) (n : ℕ) :
    ((e * ReflectionSeparation.horizontal) ^ n) '' K = K := by
  apply pow_image_eq_of_image_eq
  calc
    (e * ReflectionSeparation.horizontal) '' K =
        e '' (ReflectionSeparation.horizontal '' K) :=
      (image_image (e : Plane → Plane) (ReflectionSeparation.horizontal : Plane → Plane) K).symm
    _ = K := by rw [hHK, heK]

end

end Puzzling139335.N4MiddleInvolutions.Reflection.Dynamics
