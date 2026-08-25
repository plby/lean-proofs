import StackExchange.Puzzling139335.CentralRotation.RotationAlgebra.Affine
import StackExchange.Puzzling139335.CentralRotation.RotationAlgebra.Complex

/-! # Direct plane isometries in complex coordinates -/

namespace Puzzling139335.CentralRotation.RotationAlgebra

open PlaneIsometries

/-- The explicit direct affine formula determines the inverse formula. -/
theorem direct_form_symm (e : Plane ≃ᵃⁱ[ℝ] Plane) (a : Circle) (b : ℂ)
    (he : ∀ x, complexEquiv (e x) = (a : ℂ) * complexEquiv x + b) (x : Plane) :
    complexEquiv (e.symm x) =
      (a : ℂ)⁻¹ * complexEquiv x - (a : ℂ)⁻¹ * b := by
  have hx := he (e.symm x)
  rw [e.apply_symm_apply] at hx
  calc
    complexEquiv (e.symm x) =
        (a : ℂ)⁻¹ * ((a : ℂ) * complexEquiv (e.symm x)) := by
      rw [← mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero a), one_mul]
    _ = (a : ℂ)⁻¹ * (complexEquiv x - b) := by
      rw [← eq_sub_iff_add_eq.mpr hx.symm]
    _ = (a : ℂ)⁻¹ * complexEquiv x - (a : ℂ)⁻¹ * b := mul_sub _ _ _

/-- The map `F = h ∘ g⁻¹` is direct, with multiplier `-a⁻¹`. -/
theorem direct_form_reflection_comp_inverse (F g : Plane ≃ᵃⁱ[ℝ] Plane)
    (O : Plane) (a : Circle) (b : ℂ)
    (hg : ∀ x, complexEquiv (g x) = (a : ℂ) * complexEquiv x + b)
    (hF : ∀ x, F x = AffineIsometryEquiv.pointReflection ℝ O (g.symm x))
    (x : Plane) :
    complexEquiv (F x) = ((-a⁻¹ : Circle) : ℂ) * complexEquiv x +
      (2 * complexEquiv O + (a : ℂ)⁻¹ * b) := by
  rw [hF, complex_pointReflection, direct_form_symm g a b hg]
  simp only [Circle.coe_neg, Circle.coe_inv]
  ring

/-- A direct isometry with two distinct fixed points is the identity. -/
theorem direct_eq_refl_of_two_fixed (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (a : Circle) (b : ℂ)
    (he : ∀ x, complexEquiv (e x) = (a : ℂ) * complexEquiv x + b)
    {p q : Plane} (hpq : p ≠ q) (hp : e p = p) (hq : e q = q) :
    e = AffineIsometryEquiv.refl ℝ Plane := by
  have ha := coefficient_eq_one_of_two_fixed he complexEquiv.injective hpq hp hq
  have hcoord := he p
  rw [hp, ha, one_mul] at hcoord
  have hb : b = 0 := by linear_combination -hcoord
  apply AffineIsometryEquiv.ext
  intro x
  apply complexEquiv.injective
  change complexEquiv (e x) = complexEquiv x
  simpa only [ha, one_mul, hb, add_zero] using he x

/-- A direct isometry fixing `z` and swapping two distinct points is the
half-turn about `z`.  The endpoint permutation supplies nonidentity. -/
theorem direct_eq_pointReflection_of_fixed_of_swap (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (a : Circle) (b : ℂ)
    (he : ∀ x, complexEquiv (e x) = (a : ℂ) * complexEquiv x + b)
    {z p q : Plane} (hz : e z = z) (hpq : p ≠ q)
    (hp : e p = q) (hq : e q = p) :
    e = AffineIsometryEquiv.pointReflection ℝ z := by
  have ha := coefficient_eq_neg_one_of_swap he complexEquiv.injective hpq hp hq
  have hcoord := he z
  rw [hz, ha] at hcoord
  apply AffineIsometryEquiv.ext
  intro x
  apply complexEquiv.injective
  rw [he, ha, complex_pointReflection]
  linear_combination -hcoord

/-- A direct nontranslation has the fixed point computed by the complex
rotation-center formula. -/
theorem direct_exists_fixed_of_coefficient_ne_one (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (a : Circle) (ha : a ≠ 1) (b : ℂ)
    (he : ∀ x, complexEquiv (e x) = (a : ℂ) * complexEquiv x + b) :
    ∃ c, e c = c := by
  refine ⟨complexEquiv.symm (complexRotationCenter a b), ?_⟩
  apply complexEquiv.injective
  rw [he, complexEquiv.apply_symm_apply]
  exact (complex_direct_fixed_iff a ha b _).mpr rfl

/-- A root-of-unity multiplier gives an actual period for a direct isometry
with a fixed point, including its translation term. -/
theorem direct_iterate_eq_id_of_fixed (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (a : Circle) (b : ℂ)
    (he : ∀ x, complexEquiv (e x) = (a : ℂ) * complexEquiv x + b)
    {c : Plane} (hc : e c = c) {n : ℕ} (hpower : (a : ℂ) ^ n = 1) :
    (e : Plane → Plane)^[n] = id :=
  iterate_eq_id_of_fixed_of_pow_eq_one he complexEquiv.injective hc hpower

/-- The nonidentity coefficient supplies the fixed point, so no independent
fixed-point hypothesis is needed in the finite-period conclusion. -/
theorem direct_iterate_eq_id_of_coefficient_ne_one (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (a : Circle) (ha : a ≠ 1) (b : ℂ)
    (he : ∀ x, complexEquiv (e x) = (a : ℂ) * complexEquiv x + b)
    {n : ℕ} (hpower : (a : ℂ) ^ n = 1) : (e : Plane → Plane)^[n] = id := by
  obtain ⟨c, hc⟩ := direct_exists_fixed_of_coefficient_ne_one e a ha b he
  exact direct_iterate_eq_id_of_fixed e a b he hc hpower

/-- Multiplier minus one determines a half-turn, including its center. -/
theorem direct_eq_pointReflection_of_coefficient_neg_one (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (a : Circle) (b : ℂ)
    (he : ∀ x, complexEquiv (e x) = (a : ℂ) * complexEquiv x + b)
    (ha : (a : ℂ) = -1) :
    e = AffineIsometryEquiv.pointReflection ℝ (complexEquiv.symm (b / 2)) := by
  apply AffineIsometryEquiv.ext
  intro x
  apply complexEquiv.injective
  rw [he, ha, complex_pointReflection, complexEquiv.apply_symm_apply]
  ring

/-- A direct isometry which is not a half-turn has coefficient different
from minus one. -/
theorem direct_coefficient_ne_neg_one_of_no_pointReflection
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (a : Circle) (b : ℂ)
    (he : ∀ x, complexEquiv (e x) = (a : ℂ) * complexEquiv x + b)
    (hnot : ∀ c, e ≠ AffineIsometryEquiv.pointReflection ℝ c) : a ≠ -1 := by
  intro ha
  apply hnot (complexEquiv.symm (b / 2))
  apply direct_eq_pointReflection_of_coefficient_neg_one e a b he
  simp only [ha, Circle.coe_neg, Circle.coe_one]

/-- The multiplier of `h ∘ g⁻¹` is nonidentity unless that of `g` is minus one. -/
theorem neg_inv_coefficient_ne_one (a : Circle) (ha : a ≠ -1) : -a⁻¹ ≠ 1 := by
  intro h
  apply ha
  have hinv : a⁻¹ = -1 := neg_eq_iff_eq_neg.mp h
  simpa only [inv_inv, inv_neg, inv_one] using congrArg Inv.inv hinv

end Puzzling139335.CentralRotation.RotationAlgebra
